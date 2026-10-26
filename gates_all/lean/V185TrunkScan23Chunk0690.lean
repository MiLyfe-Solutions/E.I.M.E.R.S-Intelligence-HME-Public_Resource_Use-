import V185TrunkScan23Chunk0689

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4080663 : List Nat := [1, 1, 3, 5, 1, 3, 2, 1, 2, 1, 3]
def baseStart_4080663 : Nat := 118140960795 + 4080663 * 2 ^ 59
def prefixEnd_4080663 : Nat := 4983230072969 + 3 ^ 40 * 4080663 * 2
def baseEnd_4080663 : Nat := 2095341508018073120945879

theorem tailTrace_4080663 : CollatzResearch.WordTrace tailWord_4080663 prefixEnd_4080663 2095341508018073120945879 := by
  unfold tailWord_4080663
  simp only [CollatzResearch.WordTrace]
  refine ⟨148834006815462347600734643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99222671210308231733823095 148834006815462347600734643)
  ·
    refine ⟨223251010223193521401101965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148834006815462347600734643 223251010223193521401101965)
    ·
      refine ⟨83719128833697570525413237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223251010223193521401101965 83719128833697570525413237)
      ·
        refine ⟨7848668328159147236757491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 83719128833697570525413237 7848668328159147236757491)
        ·
          refine ⟨11773002492238720855136237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7848668328159147236757491 11773002492238720855136237)
          ·
            refine ⟨4414875934589520320676089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11773002492238720855136237 4414875934589520320676089)
            ·
              refine ⟨3311156950942140240507067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4414875934589520320676089 3311156950942140240507067)
              ·
                refine ⟨4966735426413210360760601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3311156950942140240507067 4966735426413210360760601)
                ·
                  refine ⟨3725051569809907770570451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4966735426413210360760601 3725051569809907770570451)
                  ·
                    refine ⟨5587577354714861655855677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3725051569809907770570451 5587577354714861655855677)
                    ·
                      refine ⟨2095341508018073120945879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5587577354714861655855677 2095341508018073120945879)
                      ·
                        rfl

theorem cell23_4080663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 2, 1, 2, 1, 3].length) (baseStart_4080663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4080663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4080663 prefixEnd_4080663 := by exact prefixLift 4080663
  have htrace : WordTrace (prefixWord ++ tailWord_4080663) baseStart_4080663 baseEnd_4080663 := by
    simpa [prefixWord, tailWord_4080663, baseEnd_4080663] using wordTrace_append hprefix tailTrace_4080663
  have hstable : (prefixWord ++ tailWord_4080663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4080663).length < 2 ^ (prefixWord ++ tailWord_4080663).sum := by decide
  have hdescent : baseEnd_4080663 < baseStart_4080663 := by decide
  rcases family_descends (prefixWord ++ tailWord_4080663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4080665 : List Nat := [1, 2, 1, 2, 1, 1, 4, 3, 2, 2, 4]
def baseStart_4080665 : Nat := 118140960795 + 4080665 * 2 ^ 59
def prefixEnd_4080665 : Nat := 4983230072969 + 3 ^ 40 * 4080665 * 2
def baseEnd_4080665 : Nat := 2095342534979382113120869

theorem tailTrace_4080665 : CollatzResearch.WordTrace tailWord_4080665 prefixEnd_4080665 2095342534979382113120869 := by
  unfold tailWord_4080665
  simp only [CollatzResearch.WordTrace]
  refine ⟨148834079761455101942307449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99222719840970067961538299 148834079761455101942307449)
  ·
    refine ⟨111625559821091326456730587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148834079761455101942307449 111625559821091326456730587)
    ·
      refine ⟨167438339731636989685095881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111625559821091326456730587 167438339731636989685095881)
      ·
        refine ⟨125578754798727742263821911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167438339731636989685095881 125578754798727742263821911)
        ·
          refine ⟨188368132198091613395732867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125578754798727742263821911 188368132198091613395732867)
          ·
            refine ⟨282552198297137420093599301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188368132198091613395732867 282552198297137420093599301)
            ·
              refine ⟨52978537180713266267549869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 282552198297137420093599301 52978537180713266267549869)
              ·
                refine ⟨19866951442767474850331201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52978537180713266267549869 19866951442767474850331201)
                ·
                  refine ⟨14900213582075606137748401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19866951442767474850331201 14900213582075606137748401)
                  ·
                    refine ⟨11175160186556704603311301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14900213582075606137748401 11175160186556704603311301)
                    ·
                      refine ⟨2095342534979382113120869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11175160186556704603311301 2095342534979382113120869)
                      ·
                        rfl

theorem cell23_4080665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 3, 2, 2, 4].length) (baseStart_4080665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4080665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4080665 prefixEnd_4080665 := by exact prefixLift 4080665
  have htrace : WordTrace (prefixWord ++ tailWord_4080665) baseStart_4080665 baseEnd_4080665 := by
    simpa [prefixWord, tailWord_4080665, baseEnd_4080665] using wordTrace_append hprefix tailTrace_4080665
  have hstable : (prefixWord ++ tailWord_4080665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4080665).length < 2 ^ (prefixWord ++ tailWord_4080665).sum := by decide
  have hdescent : baseEnd_4080665 < baseStart_4080665 := by decide
  rcases family_descends (prefixWord ++ tailWord_4080665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4080709 : List Nat := [1, 3, 1, 1, 1, 3, 6, 2, 5]
def baseStart_4080709 : Nat := 118140960795 + 4080709 * 2 ^ 59
def prefixEnd_4080709 : Nat := 4983230072969 + 3 ^ 40 * 4080709 * 2
def baseEnd_4080709 : Nat := 232818347569797771218963

theorem tailTrace_4080709 : CollatzResearch.WordTrace tailWord_4080709 prefixEnd_4080709 232818347569797771218963 := by
  unfold tailWord_4080709
  simp only [CollatzResearch.WordTrace]
  refine ⟨148835684573295697456909181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99223789715530464971272787 148835684573295697456909181)
  ·
    refine ⟨55813381714985886546340943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148835684573295697456909181 55813381714985886546340943)
    ·
      refine ⟨83720072572478829819511415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55813381714985886546340943 83720072572478829819511415)
      ·
        refine ⟨125580108858718244729267123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83720072572478829819511415 125580108858718244729267123)
        ·
          refine ⟨188370163288077367093900685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125580108858718244729267123 188370163288077367093900685)
          ·
            refine ⟨70638811233029012660212757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 188370163288077367093900685 70638811233029012660212757)
            ·
              refine ⟨3311194276548234968447473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 70638811233029012660212757 3311194276548234968447473)
              ·
                refine ⟨2483395707411176226335605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3311194276548234968447473 2483395707411176226335605)
                ·
                  refine ⟨232818347569797771218963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2483395707411176226335605 232818347569797771218963)
                  ·
                    rfl

theorem cell23_4080709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 6, 2, 5].length) (baseStart_4080709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4080709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4080709 prefixEnd_4080709 := by exact prefixLift 4080709
  have htrace : WordTrace (prefixWord ++ tailWord_4080709) baseStart_4080709 baseEnd_4080709 := by
    simpa [prefixWord, tailWord_4080709, baseEnd_4080709] using wordTrace_append hprefix tailTrace_4080709
  have hstable : (prefixWord ++ tailWord_4080709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4080709).length < 2 ^ (prefixWord ++ tailWord_4080709).sum := by decide
  have hdescent : baseEnd_4080709 < baseStart_4080709 := by decide
  rcases family_descends (prefixWord ++ tailWord_4080709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4080712 : List Nat := [2, 1, 3, 1, 1, 1, 3, 1, 1, 7, 2]
def baseStart_4080712 : Nat := 118140960795 + 4080712 * 2 ^ 59
def prefixEnd_4080712 : Nat := 4983230072969 + 3 ^ 40 * 4080712 * 2
def baseEnd_4080712 : Nat := 2095366668570143429233153

theorem tailTrace_4080712 : CollatzResearch.WordTrace tailWord_4080712 prefixEnd_4080712 2095366668570143429233153 := by
  unfold tailWord_4080712
  simp only [CollatzResearch.WordTrace]
  refine ⟨74417896996142414484634195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99223862661523219312845593 74417896996142414484634195)
  ·
    refine ⟨111626845494213621726951293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74417896996142414484634195 111626845494213621726951293)
    ·
      refine ⟨41860067060330108147606735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111626845494213621726951293 41860067060330108147606735)
      ·
        refine ⟨62790100590495162221410103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41860067060330108147606735 62790100590495162221410103)
        ·
          refine ⟨94185150885742743332115155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62790100590495162221410103 94185150885742743332115155)
          ·
            refine ⟨141277726328614114998172733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94185150885742743332115155 141277726328614114998172733)
            ·
              refine ⟨52979147373230293124314775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141277726328614114998172733 52979147373230293124314775)
              ·
                refine ⟨79468721059845439686472163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52979147373230293124314775 79468721059845439686472163)
                ·
                  refine ⟨119203081589768159529708245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79468721059845439686472163 119203081589768159529708245)
                  ·
                    refine ⟨2793822224760191238977537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 119203081589768159529708245 2793822224760191238977537)
                    ·
                      refine ⟨2095366668570143429233153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2793822224760191238977537 2095366668570143429233153)
                      ·
                        rfl

theorem cell23_4080712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 1, 1, 7, 2].length) (baseStart_4080712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4080712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4080712 prefixEnd_4080712 := by exact prefixLift 4080712
  have htrace : WordTrace (prefixWord ++ tailWord_4080712) baseStart_4080712 baseEnd_4080712 := by
    simpa [prefixWord, tailWord_4080712, baseEnd_4080712] using wordTrace_append hprefix tailTrace_4080712
  have hstable : (prefixWord ++ tailWord_4080712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4080712).length < 2 ^ (prefixWord ++ tailWord_4080712).sum := by decide
  have hdescent : baseEnd_4080712 < baseStart_4080712 := by decide
  rcases family_descends (prefixWord ++ tailWord_4080712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4080726 : List Nat := [5, 2, 2, 1, 2, 1, 1, 2, 7]
def baseStart_4080726 : Nat := 118140960795 + 4080726 * 2 ^ 59
def prefixEnd_4080726 : Nat := 4983230072969 + 3 ^ 40 * 4080726 * 2
def baseEnd_4080726 : Nat := 232819317477700708273121

theorem tailTrace_4080726 : CollatzResearch.WordTrace tailWord_4080726 prefixEnd_4080726 232819317477700708273121 := by
  unfold tailWord_4080726
  simp only [CollatzResearch.WordTrace]
  refine ⟨9302269038389631835017377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 99224203076156072906852021 9302269038389631835017377)
  ·
    refine ⟨6976701778792223876263033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9302269038389631835017377 6976701778792223876263033)
    ·
      refine ⟨5232526334094167907197275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6976701778792223876263033 5232526334094167907197275)
      ·
        refine ⟨7848789501141251860795913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5232526334094167907197275 7848789501141251860795913)
        ·
          refine ⟨5886592125855938895596935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7848789501141251860795913 5886592125855938895596935)
          ·
            refine ⟨8829888188783908343395403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5886592125855938895596935 8829888188783908343395403)
            ·
              refine ⟨13244832283175862515093105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8829888188783908343395403 13244832283175862515093105)
              ·
                refine ⟨9933624212381896886319829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13244832283175862515093105 9933624212381896886319829)
                ·
                  refine ⟨232819317477700708273121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9933624212381896886319829 232819317477700708273121)
                  ·
                    rfl

theorem cell23_4080726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 2, 7].length) (baseStart_4080726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4080726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4080726 prefixEnd_4080726 := by exact prefixLift 4080726
  have htrace : WordTrace (prefixWord ++ tailWord_4080726) baseStart_4080726 baseEnd_4080726 := by
    simpa [prefixWord, tailWord_4080726, baseEnd_4080726] using wordTrace_append hprefix tailTrace_4080726
  have hstable : (prefixWord ++ tailWord_4080726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4080726).length < 2 ^ (prefixWord ++ tailWord_4080726).sum := by decide
  have hdescent : baseEnd_4080726 < baseStart_4080726 := by decide
  rcases family_descends (prefixWord ++ tailWord_4080726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4080752 : List Nat := [2, 1, 1, 1, 5, 1, 1, 2, 5, 4]
def baseStart_4080752 : Nat := 118140960795 + 4080752 * 2 ^ 59
def prefixEnd_4080752 : Nat := 4983230072969 + 3 ^ 40 * 4080752 * 2
def baseEnd_4080752 : Nat := 698462402598774424244323

theorem tailTrace_4080752 : CollatzResearch.WordTrace tailWord_4080752 prefixEnd_4080752 698462402598774424244323 := by
  unfold tailWord_4080752
  simp only [CollatzResearch.WordTrace]
  refine ⟨74418626456069957900362255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99224835274759943867149673 74418626456069957900362255)
  ·
    refine ⟨111627939684104936850543383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74418626456069957900362255 111627939684104936850543383)
    ·
      refine ⟨167441909526157405275815075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111627939684104936850543383 167441909526157405275815075)
      ·
        refine ⟨251162864289236107913722613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167441909526157405275815075 251162864289236107913722613)
        ·
          refine ⟨23546518527115885116911495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 251162864289236107913722613 23546518527115885116911495)
          ·
            refine ⟨35319777790673827675367243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23546518527115885116911495 35319777790673827675367243)
            ·
              refine ⟨52979666686010741513050865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35319777790673827675367243 52979666686010741513050865)
              ·
                refine ⟨39734750014508056134788149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52979666686010741513050865 39734750014508056134788149)
                ·
                  refine ⟨3725132813860130262636389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39734750014508056134788149 3725132813860130262636389)
                  ·
                    refine ⟨698462402598774424244323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3725132813860130262636389 698462402598774424244323)
                    ·
                      rfl

theorem cell23_4080752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 2, 5, 4].length) (baseStart_4080752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4080752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4080752 prefixEnd_4080752 := by exact prefixLift 4080752
  have htrace : WordTrace (prefixWord ++ tailWord_4080752) baseStart_4080752 baseEnd_4080752 := by
    simpa [prefixWord, tailWord_4080752, baseEnd_4080752] using wordTrace_append hprefix tailTrace_4080752
  have hstable : (prefixWord ++ tailWord_4080752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4080752).length < 2 ^ (prefixWord ++ tailWord_4080752).sum := by decide
  have hdescent : baseEnd_4080752 < baseStart_4080752 := by decide
  rcases family_descends (prefixWord ++ tailWord_4080752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4080755 : List Nat := [1, 1, 1, 2, 2, 1, 1, 1, 3, 6, 4]
def baseStart_4080755 : Nat := 118140960795 + 4080755 * 2 ^ 59
def prefixEnd_4080755 : Nat := 4983230072969 + 3 ^ 40 * 4080755 * 2
def baseEnd_4080755 : Nat := 2095388748238286760995455

theorem tailTrace_4080755 : CollatzResearch.WordTrace tailWord_4080755 prefixEnd_4080755 2095388748238286760995455 := by
  unfold tailWord_4080755
  simp only [CollatzResearch.WordTrace]
  refine ⟨148837362331129047313083719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99224908220752698208722479 148837362331129047313083719)
  ·
    refine ⟨223256043496693570969625579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148837362331129047313083719 223256043496693570969625579)
    ·
      refine ⟨334884065245040356454438369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223256043496693570969625579 334884065245040356454438369)
      ·
        refine ⟨251163048933780267340828777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 334884065245040356454438369 251163048933780267340828777)
        ·
          refine ⟨188372286700335200505621583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 251163048933780267340828777 188372286700335200505621583)
          ·
            refine ⟨282558430050502800758432375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188372286700335200505621583 282558430050502800758432375)
            ·
              refine ⟨423837645075754201137648563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 282558430050502800758432375 423837645075754201137648563)
              ·
                refine ⟨635756467613631301706472845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 423837645075754201137648563 635756467613631301706472845)
                ·
                  refine ⟨238408675355111738139927317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 635756467613631301706472845 238408675355111738139927317)
                  ·
                    refine ⟨11175406657270862725309093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 238408675355111738139927317 11175406657270862725309093)
                    ·
                      refine ⟨2095388748238286760995455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11175406657270862725309093 2095388748238286760995455)
                      ·
                        rfl

theorem cell23_4080755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 6, 4].length) (baseStart_4080755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4080755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4080755 prefixEnd_4080755 := by exact prefixLift 4080755
  have htrace : WordTrace (prefixWord ++ tailWord_4080755) baseStart_4080755 baseEnd_4080755 := by
    simpa [prefixWord, tailWord_4080755, baseEnd_4080755] using wordTrace_append hprefix tailTrace_4080755
  have hstable : (prefixWord ++ tailWord_4080755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4080755).length < 2 ^ (prefixWord ++ tailWord_4080755).sum := by decide
  have hdescent : baseEnd_4080755 < baseStart_4080755 := by decide
  rcases family_descends (prefixWord ++ tailWord_4080755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4080769 : List Nat := [1, 2, 4, 2, 2, 1, 1, 3, 3, 4]
def baseStart_4080769 : Nat := 118140960795 + 4080769 * 2 ^ 59
def prefixEnd_4080769 : Nat := 4983230072969 + 3 ^ 40 * 4080769 * 2
def baseEnd_4080769 : Nat := 698465312322483235406797

theorem tailTrace_4080769 : CollatzResearch.WordTrace tailWord_4080769 prefixEnd_4080769 698465312322483235406797 := by
  unfold tailWord_4080769
  simp only [CollatzResearch.WordTrace]
  refine ⟨148837872953078327704093361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99225248635385551802728907 148837872953078327704093361)
  ·
    refine ⟨111628404714808745778070021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148837872953078327704093361 111628404714808745778070021)
    ·
      refine ⟨20930325884026639833388129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111628404714808745778070021 20930325884026639833388129)
      ·
        refine ⟨15697744413019979875041097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20930325884026639833388129 15697744413019979875041097)
        ·
          refine ⟨11773308309764984906280823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15697744413019979875041097 11773308309764984906280823)
          ·
            refine ⟨17659962464647477359421235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11773308309764984906280823 17659962464647477359421235)
            ·
              refine ⟨26489943696971216039131853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17659962464647477359421235 26489943696971216039131853)
              ·
                refine ⟨9933728886364206014674445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26489943696971216039131853 9933728886364206014674445)
                ·
                  refine ⟨3725148332386577255502917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9933728886364206014674445 3725148332386577255502917)
                  ·
                    refine ⟨698465312322483235406797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3725148332386577255502917 698465312322483235406797)
                    ·
                      rfl

theorem cell23_4080769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 3, 3, 4].length) (baseStart_4080769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4080769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4080769 prefixEnd_4080769 := by exact prefixLift 4080769
  have htrace : WordTrace (prefixWord ++ tailWord_4080769) baseStart_4080769 baseEnd_4080769 := by
    simpa [prefixWord, tailWord_4080769, baseEnd_4080769] using wordTrace_append hprefix tailTrace_4080769
  have hstable : (prefixWord ++ tailWord_4080769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4080769).length < 2 ^ (prefixWord ++ tailWord_4080769).sum := by decide
  have hdescent : baseEnd_4080769 < baseStart_4080769 := by decide
  rcases family_descends (prefixWord ++ tailWord_4080769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4080819 : List Nat := [1, 1, 1, 2, 3, 2, 3, 1, 4, 3, 2]
def baseStart_4080819 : Nat := 118140960795 + 4080819 * 2 ^ 59
def prefixEnd_4080819 : Nat := 4983230072969 + 3 ^ 40 * 4080819 * 2
def baseEnd_4080819 : Nat := 2095421611000174510595161

theorem tailTrace_4080819 : CollatzResearch.WordTrace tailWord_4080819 prefixEnd_4080819 2095421611000174510595161 := by
  unfold tailWord_4080819
  simp only [CollatzResearch.WordTrace]
  refine ⟨148839696602897186243413511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99226464401931457495609007 148839696602897186243413511)
  ·
    refine ⟨223259544904345779365120267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148839696602897186243413511 223259544904345779365120267)
    ·
      refine ⟨334889317356518669047680401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223259544904345779365120267 334889317356518669047680401)
      ·
        refine ⟨251166988017389001785760301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 334889317356518669047680401 251166988017389001785760301)
        ·
          refine ⟨94187620506520875669660113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 251166988017389001785760301 94187620506520875669660113)
          ·
            refine ⟨70640715379890656752245085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94187620506520875669660113 70640715379890656752245085)
            ·
              refine ⟨26490268267458996282091907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70640715379890656752245085 26490268267458996282091907)
              ·
                refine ⟨39735402401188494423137861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26490268267458996282091907 39735402401188494423137861)
                ·
                  refine ⟨7450387950222842704338349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39735402401188494423137861 7450387950222842704338349)
                  ·
                    refine ⟨2793895481333566014126881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7450387950222842704338349 2793895481333566014126881)
                    ·
                      refine ⟨2095421611000174510595161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2793895481333566014126881 2095421611000174510595161)
                      ·
                        rfl

theorem cell23_4080819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 1, 4, 3, 2].length) (baseStart_4080819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4080819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4080819 prefixEnd_4080819 := by exact prefixLift 4080819
  have htrace : WordTrace (prefixWord ++ tailWord_4080819) baseStart_4080819 baseEnd_4080819 := by
    simpa [prefixWord, tailWord_4080819, baseEnd_4080819] using wordTrace_append hprefix tailTrace_4080819
  have hstable : (prefixWord ++ tailWord_4080819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4080819).length < 2 ^ (prefixWord ++ tailWord_4080819).sum := by decide
  have hdescent : baseEnd_4080819 < baseStart_4080819 := by decide
  rcases family_descends (prefixWord ++ tailWord_4080819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4080833 : List Nat := [1, 2, 6, 1, 1, 3, 2, 1, 6]
def baseStart_4080833 : Nat := 118140960795 + 4080833 * 2 ^ 59
def prefixEnd_4080833 : Nat := 4983230072969 + 3 ^ 40 * 4080833 * 2
def baseEnd_4080833 : Nat := 232825422192148606202233

theorem tailTrace_4080833 : CollatzResearch.WordTrace tailWord_4080833 prefixEnd_4080833 232825422192148606202233 := by
  unfold tailWord_4080833
  simp only [CollatzResearch.WordTrace]
  refine ⟨148840207224846466634423153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99226804816564311089615435 148840207224846466634423153)
  ·
    refine ⟨111630155418634849975817365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148840207224846466634423153 111630155418634849975817365)
    ·
      refine ⟨5232663535248508592616439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 111630155418634849975817365 5232663535248508592616439)
      ·
        refine ⟨7848995302872762888924659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5232663535248508592616439 7848995302872762888924659)
        ·
          refine ⟨11773492954309144333386989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7848995302872762888924659 11773492954309144333386989)
          ·
            refine ⟨4415059857865929125020121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11773492954309144333386989 4415059857865929125020121)
            ·
              refine ⟨3311294893399446843765091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4415059857865929125020121 3311294893399446843765091)
              ·
                refine ⟨4966942340099170265647637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3311294893399446843765091 4966942340099170265647637)
                ·
                  refine ⟨232825422192148606202233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4966942340099170265647637 232825422192148606202233)
                  ·
                    rfl

theorem cell23_4080833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 2, 1, 6].length) (baseStart_4080833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4080833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4080833 prefixEnd_4080833 := by exact prefixLift 4080833
  have htrace : WordTrace (prefixWord ++ tailWord_4080833) baseStart_4080833 baseEnd_4080833 := by
    simpa [prefixWord, tailWord_4080833, baseEnd_4080833] using wordTrace_append hprefix tailTrace_4080833
  have hstable : (prefixWord ++ tailWord_4080833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4080833).length < 2 ^ (prefixWord ++ tailWord_4080833).sum := by decide
  have hdescent : baseEnd_4080833 < baseStart_4080833 := by decide
  rcases family_descends (prefixWord ++ tailWord_4080833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4080853 : List Nat := [1, 3, 2, 4, 1, 2, 2, 1, 2, 3, 2]
def baseStart_4080853 : Nat := 118140960795 + 4080853 * 2 ^ 59
def prefixEnd_4080853 : Nat := 4983230072969 + 3 ^ 40 * 4080853 * 2
def baseEnd_4080853 : Nat := 2095439069342427377570005

theorem tailTrace_4080853 : CollatzResearch.WordTrace tailWord_4080853 prefixEnd_4080853 2095439069342427377570005 := by
  unfold tailWord_4080853
  simp only [CollatzResearch.WordTrace]
  refine ⟨148840936684774010050151213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99227291123182673366767475 148840936684774010050151213)
  ·
    refine ⟨55815351256790253768806705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148840936684774010050151213 55815351256790253768806705)
    ·
      refine ⟨41861513442592690326605029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55815351256790253768806705 41861513442592690326605029)
      ·
        refine ⟨7849033770486129436238443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41861513442592690326605029 7849033770486129436238443)
        ·
          refine ⟨11773550655729194154357665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7849033770486129436238443 11773550655729194154357665)
          ·
            refine ⟨8830162991796895615768249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11773550655729194154357665 8830162991796895615768249)
            ·
              refine ⟨6622622243847671711826187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8830162991796895615768249 6622622243847671711826187)
              ·
                refine ⟨9933933365771507567739281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6622622243847671711826187 9933933365771507567739281)
                ·
                  refine ⟨7450450024328630675804461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9933933365771507567739281 7450450024328630675804461)
                  ·
                    refine ⟨2793918759123236503426673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7450450024328630675804461 2793918759123236503426673)
                    ·
                      refine ⟨2095439069342427377570005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2793918759123236503426673 2095439069342427377570005)
                      ·
                        rfl

theorem cell23_4080853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 2, 1, 2, 3, 2].length) (baseStart_4080853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4080853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4080853 prefixEnd_4080853 := by exact prefixLift 4080853
  have htrace : WordTrace (prefixWord ++ tailWord_4080853) baseStart_4080853 baseEnd_4080853 := by
    simpa [prefixWord, tailWord_4080853, baseEnd_4080853] using wordTrace_append hprefix tailTrace_4080853
  have hstable : (prefixWord ++ tailWord_4080853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4080853).length < 2 ^ (prefixWord ++ tailWord_4080853).sum := by decide
  have hdescent : baseEnd_4080853 < baseStart_4080853 := by decide
  rcases family_descends (prefixWord ++ tailWord_4080853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4080876 : List Nat := [2, 2, 1, 1, 2, 5, 2, 2, 2, 4]
def baseStart_4080876 : Nat := 118140960795 + 4080876 * 2 ^ 59
def prefixEnd_4080876 : Nat := 4983230072969 + 3 ^ 40 * 4080876 * 2
def baseEnd_4080876 : Nat := 698483626465826929194133

theorem tailTrace_4080876 : CollatzResearch.WordTrace tailWord_4080876 prefixEnd_4080876 698483626465826929194133 := by
  unfold tailWord_4080876
  simp only [CollatzResearch.WordTrace]
  refine ⟨74420887781845342489119241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99227850375793789985492321 74420887781845342489119241)
  ·
    refine ⟨55815665836384006866839431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74420887781845342489119241 55815665836384006866839431)
    ·
      refine ⟨83723498754576010300259147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55815665836384006866839431 83723498754576010300259147)
      ·
        refine ⟨125585248131864015450388721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83723498754576010300259147 125585248131864015450388721)
        ·
          refine ⟨94188936098898011587791541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125585248131864015450388721 94188936098898011587791541)
          ·
            refine ⟨8830212759271688586355457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 94188936098898011587791541 8830212759271688586355457)
            ·
              refine ⟨6622659569453766439766593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8830212759271688586355457 6622659569453766439766593)
              ·
                refine ⟨4966994677090324829824945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6622659569453766439766593 4966994677090324829824945)
                ·
                  refine ⟨3725246007817743622368709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4966994677090324829824945 3725246007817743622368709)
                  ·
                    refine ⟨698483626465826929194133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3725246007817743622368709 698483626465826929194133)
                    ·
                      rfl

theorem cell23_4080876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 4].length) (baseStart_4080876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4080876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4080876 prefixEnd_4080876 := by exact prefixLift 4080876
  have htrace : WordTrace (prefixWord ++ tailWord_4080876) baseStart_4080876 baseEnd_4080876 := by
    simpa [prefixWord, tailWord_4080876, baseEnd_4080876] using wordTrace_append hprefix tailTrace_4080876
  have hstable : (prefixWord ++ tailWord_4080876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4080876).length < 2 ^ (prefixWord ++ tailWord_4080876).sum := by decide
  have hdescent : baseEnd_4080876 < baseStart_4080876 := by decide
  rcases family_descends (prefixWord ++ tailWord_4080876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4080877 : List Nat := [1, 5, 1, 2, 2, 3, 2, 2, 1, 1, 3]
def baseStart_4080877 : Nat := 118140960795 + 4080877 * 2 ^ 59
def prefixEnd_4080877 : Nat := 4983230072969 + 3 ^ 40 * 4080877 * 2
def baseEnd_4080877 : Nat := 2095451392878135283669895

theorem tailTrace_4080877 : CollatzResearch.WordTrace tailWord_4080877 prefixEnd_4080877 2095451392878135283669895 := by
  unfold tailWord_4080877
  simp only [CollatzResearch.WordTrace]
  refine ⟨148841812036687062149024885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99227874691124708099349923 148841812036687062149024885)
  ·
    refine ⟨13953919878439412076471083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 148841812036687062149024885 13953919878439412076471083)
    ·
      refine ⟨20930879817659118114706625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13953919878439412076471083 20930879817659118114706625)
      ·
        refine ⟨15698159863244338586029969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20930879817659118114706625 15698159863244338586029969)
        ·
          refine ⟨11773619897433253939522477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15698159863244338586029969 11773619897433253939522477)
          ·
            refine ⟨4415107461537470227320929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11773619897433253939522477 4415107461537470227320929)
            ·
              refine ⟨3311330596153102670490697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4415107461537470227320929 3311330596153102670490697)
              ·
                refine ⟨2483497947114827002868023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3311330596153102670490697 2483497947114827002868023)
                ·
                  refine ⟨3725246920672240504302035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2483497947114827002868023 3725246920672240504302035)
                  ·
                    refine ⟨5587870381008360756453053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3725246920672240504302035 5587870381008360756453053)
                    ·
                      refine ⟨2095451392878135283669895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5587870381008360756453053 2095451392878135283669895)
                      ·
                        rfl

theorem cell23_4080877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 2, 2, 1, 1, 3].length) (baseStart_4080877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4080877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4080877 prefixEnd_4080877 := by exact prefixLift 4080877
  have htrace : WordTrace (prefixWord ++ tailWord_4080877) baseStart_4080877 baseEnd_4080877 := by
    simpa [prefixWord, tailWord_4080877, baseEnd_4080877] using wordTrace_append hprefix tailTrace_4080877
  have hstable : (prefixWord ++ tailWord_4080877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4080877).length < 2 ^ (prefixWord ++ tailWord_4080877).sum := by decide
  have hdescent : baseEnd_4080877 < baseStart_4080877 := by decide
  rcases family_descends (prefixWord ++ tailWord_4080877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4080899 : List Nat := [1, 1, 1, 3, 2, 4, 1, 3, 1, 3, 3]
def baseStart_4080899 : Nat := 118140960795 + 4080899 * 2 ^ 59
def prefixEnd_4080899 : Nat := 4983230072969 + 3 ^ 40 * 4080899 * 2
def baseEnd_4080899 : Nat := 2095462689452534197594793

theorem tailTrace_4080899 : CollatzResearch.WordTrace tailWord_4080899 prefixEnd_4080899 2095462689452534197594793 := by
  unfold tailWord_4080899
  simp only [CollatzResearch.WordTrace]
  refine ⟨148842614442607359906325751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99228409628404906604217167 148842614442607359906325751)
  ·
    refine ⟨223263921663911039859488627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148842614442607359906325751 223263921663911039859488627)
    ·
      refine ⟨334895882495866559789232941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223263921663911039859488627 334895882495866559789232941)
      ·
        refine ⟨125585955935949959920962353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 334895882495866559789232941 125585955935949959920962353)
        ·
          refine ⟨94189466951962469940721765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125585955935949959920962353 94189466951962469940721765)
          ·
            refine ⟨17660525053492963113885331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94189466951962469940721765 17660525053492963113885331)
            ·
              refine ⟨26490787580239444670827997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17660525053492963113885331 26490787580239444670827997)
              ·
                refine ⟨9934045342589791751560499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26490787580239444670827997 9934045342589791751560499)
                ·
                  refine ⟨14901068013884687627340749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9934045342589791751560499 14901068013884687627340749)
                  ·
                    refine ⟨5587900505206757860252781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14901068013884687627340749 5587900505206757860252781)
                    ·
                      refine ⟨2095462689452534197594793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5587900505206757860252781 2095462689452534197594793)
                      ·
                        rfl

theorem cell23_4080899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 3, 1, 3, 3].length) (baseStart_4080899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4080899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4080899 prefixEnd_4080899 := by exact prefixLift 4080899
  have htrace : WordTrace (prefixWord ++ tailWord_4080899) baseStart_4080899 baseEnd_4080899 := by
    simpa [prefixWord, tailWord_4080899, baseEnd_4080899] using wordTrace_append hprefix tailTrace_4080899
  have hstable : (prefixWord ++ tailWord_4080899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4080899).length < 2 ^ (prefixWord ++ tailWord_4080899).sum := by decide
  have hdescent : baseEnd_4080899 < baseStart_4080899 := by decide
  rcases family_descends (prefixWord ++ tailWord_4080899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4080933 : List Nat := [1, 3, 1, 2, 4, 1, 3, 2, 2, 1, 3]
def baseStart_4080933 : Nat := 118140960795 + 4080933 * 2 ^ 59
def prefixEnd_4080933 : Nat := 4983230072969 + 3 ^ 40 * 4080933 * 2
def baseEnd_4080933 : Nat := 2095480147794787064569637

theorem tailTrace_4080933 : CollatzResearch.WordTrace tailWord_4080933 prefixEnd_4080933 2095480147794787064569637 := by
  unfold tailWord_4080933
  simp only [CollatzResearch.WordTrace]
  refine ⟨148843854524484183713063453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99229236349656122475375635 148843854524484183713063453)
  ·
    refine ⟨55816445446681568892398795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148843854524484183713063453 55816445446681568892398795)
    ·
      refine ⟨83724668170022353338598193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55816445446681568892398795 83724668170022353338598193)
      ·
        refine ⟨62793501127516765003948645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83724668170022353338598193 62793501127516765003948645)
        ·
          refine ⟨11773781461409393438240371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62793501127516765003948645 11773781461409393438240371)
          ·
            refine ⟨17660672192114090157360557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11773781461409393438240371 17660672192114090157360557)
            ·
              refine ⟨6622752072042783809010209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17660672192114090157360557 6622752072042783809010209)
              ·
                refine ⟨4967064054032087856757657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6622752072042783809010209 4967064054032087856757657)
                ·
                  refine ⟨3725298040524065892568243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4967064054032087856757657 3725298040524065892568243)
                  ·
                    refine ⟨5587947060786098838852365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3725298040524065892568243 5587947060786098838852365)
                    ·
                      refine ⟨2095480147794787064569637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5587947060786098838852365 2095480147794787064569637)
                      ·
                        rfl

theorem cell23_4080933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 3, 2, 2, 1, 3].length) (baseStart_4080933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4080933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4080933 prefixEnd_4080933 := by exact prefixLift 4080933
  have htrace : WordTrace (prefixWord ++ tailWord_4080933) baseStart_4080933 baseEnd_4080933 := by
    simpa [prefixWord, tailWord_4080933, baseEnd_4080933] using wordTrace_append hprefix tailTrace_4080933
  have hstable : (prefixWord ++ tailWord_4080933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4080933).length < 2 ^ (prefixWord ++ tailWord_4080933).sum := by decide
  have hdescent : baseEnd_4080933 < baseStart_4080933 := by decide
  rcases family_descends (prefixWord ++ tailWord_4080933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4080949 : List Nat := [1, 3, 3, 1, 2, 2, 2, 1, 2, 6]
def baseStart_4080949 : Nat := 118140960795 + 4080949 * 2 ^ 59
def prefixEnd_4080949 : Nat := 4983230072969 + 3 ^ 40 * 4080949 * 2
def baseEnd_4080949 : Nat := 698496121161753000656521

theorem tailTrace_4080949 : CollatzResearch.WordTrace tailWord_4080949 prefixEnd_4080949 698496121161753000656521 := by
  unfold tailWord_4080949
  simp only [CollatzResearch.WordTrace]
  refine ⟨148844438092426218445645901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99229625394950812297097267 148844438092426218445645901)
  ·
    refine ⟨55816664284659831917117213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148844438092426218445645901 55816664284659831917117213)
    ·
      refine ⟨20931249106747436968918955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55816664284659831917117213 20931249106747436968918955)
      ·
        refine ⟨31396873660121155453378433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20931249106747436968918955 31396873660121155453378433)
        ·
          refine ⟨23547655245090866590033825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31396873660121155453378433 23547655245090866590033825)
          ·
            refine ⟨17660741433818149942525369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23547655245090866590033825 17660741433818149942525369)
            ·
              refine ⟨13245556075363612456894027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17660741433818149942525369 13245556075363612456894027)
              ·
                refine ⟨19868334113045418685341041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13245556075363612456894027 19868334113045418685341041)
                ·
                  refine ⟨14901250584784064014005781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19868334113045418685341041 14901250584784064014005781)
                  ·
                    refine ⟨698496121161753000656521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14901250584784064014005781 698496121161753000656521)
                    ·
                      rfl

theorem cell23_4080949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 1, 2, 6].length) (baseStart_4080949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4080949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4080949 prefixEnd_4080949 := by exact prefixLift 4080949
  have htrace : WordTrace (prefixWord ++ tailWord_4080949) baseStart_4080949 baseEnd_4080949 := by
    simpa [prefixWord, tailWord_4080949, baseEnd_4080949] using wordTrace_append hprefix tailTrace_4080949
  have hstable : (prefixWord ++ tailWord_4080949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4080949).length < 2 ^ (prefixWord ++ tailWord_4080949).sum := by decide
  have hdescent : baseEnd_4080949 < baseStart_4080949 := by decide
  rcases family_descends (prefixWord ++ tailWord_4080949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4080996 : List Nat := [2, 3, 1, 1, 3, 4, 1, 1, 7]
def baseStart_4080996 : Nat := 118140960795 + 4080996 * 2 ^ 59
def prefixEnd_4080996 : Nat := 4983230072969 + 3 ^ 40 * 4080996 * 2
def baseEnd_4080996 : Nat := 232834721897335590897983

theorem tailTrace_4080996 : CollatzResearch.WordTrace tailWord_4080996 prefixEnd_4080996 232834721897335590897983 := by
  unfold tailWord_4080996
  simp only [CollatzResearch.WordTrace]
  refine ⟨74423076161627972736303421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99230768215503963648404561 74423076161627972736303421)
  ·
    refine ⟨27908653560610489776113783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74423076161627972736303421 27908653560610489776113783)
    ·
      refine ⟨41862980340915734664170675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27908653560610489776113783 41862980340915734664170675)
      ·
        refine ⟨62794470511373601996256013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41862980340915734664170675 62794470511373601996256013)
        ·
          refine ⟨23547926441765100748596005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62794470511373601996256013 23547926441765100748596005)
          ·
            refine ⟨4415236207830956390361751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23547926441765100748596005 4415236207830956390361751)
            ·
              refine ⟨6622854311746434585542627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4415236207830956390361751 6622854311746434585542627)
              ·
                refine ⟨9934281467619651878313941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6622854311746434585542627 9934281467619651878313941)
                ·
                  refine ⟨232834721897335590897983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9934281467619651878313941 232834721897335590897983)
                  ·
                    rfl

theorem cell23_4080996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 4, 1, 1, 7].length) (baseStart_4080996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4080996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4080996 prefixEnd_4080996 := by exact prefixLift 4080996
  have htrace : WordTrace (prefixWord ++ tailWord_4080996) baseStart_4080996 baseEnd_4080996 := by
    simpa [prefixWord, tailWord_4080996, baseEnd_4080996] using wordTrace_append hprefix tailTrace_4080996
  have hstable : (prefixWord ++ tailWord_4080996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4080996).length < 2 ^ (prefixWord ++ tailWord_4080996).sum := by decide
  have hdescent : baseEnd_4080996 < baseStart_4080996 := by decide
  rcases family_descends (prefixWord ++ tailWord_4080996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4081029 : List Nat := [1, 3, 1, 1, 3, 1, 2, 3, 1, 3, 4]
def baseStart_4081029 : Nat := 118140960795 + 4081029 * 2 ^ 59
def prefixEnd_4081029 : Nat := 4983230072969 + 3 ^ 40 * 4081029 * 2
def baseEnd_4081029 : Nat := 2095529441937618688969195

theorem tailTrace_4081029 : CollatzResearch.WordTrace tailWord_4081029 prefixEnd_4081029 2095529441937618688969195 := by
  unfold tailWord_4081029
  simp only [CollatzResearch.WordTrace]
  refine ⟨148847355932136392108558141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99231570621424261405705427 148847355932136392108558141)
  ·
    refine ⟨55817758474551147040709303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148847355932136392108558141 55817758474551147040709303)
    ·
      refine ⟨83726637711826720561063955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55817758474551147040709303 83726637711826720561063955)
      ·
        refine ⟨125589956567740080841595933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83726637711826720561063955 125589956567740080841595933)
        ·
          refine ⟨47096233712902530315598475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125589956567740080841595933 47096233712902530315598475)
          ·
            refine ⟨70644350569353795473397713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47096233712902530315598475 70644350569353795473397713)
            ·
              refine ⟨52983262927015346605048285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70644350569353795473397713 52983262927015346605048285)
              ·
                refine ⟨19868723597630754976893107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52983262927015346605048285 19868723597630754976893107)
                ·
                  refine ⟨29803085396446132465339661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19868723597630754976893107 29803085396446132465339661)
                  ·
                    refine ⟨11176157023667299674502373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29803085396446132465339661 11176157023667299674502373)
                    ·
                      refine ⟨2095529441937618688969195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11176157023667299674502373 2095529441937618688969195)
                      ·
                        rfl

theorem cell23_4081029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 3, 1, 3, 4].length) (baseStart_4081029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4081029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4081029 prefixEnd_4081029 := by exact prefixLift 4081029
  have htrace : WordTrace (prefixWord ++ tailWord_4081029) baseStart_4081029 baseEnd_4081029 := by
    simpa [prefixWord, tailWord_4081029, baseEnd_4081029] using wordTrace_append hprefix tailTrace_4081029
  have hstable : (prefixWord ++ tailWord_4081029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4081029).length < 2 ^ (prefixWord ++ tailWord_4081029).sum := by decide
  have hdescent : baseEnd_4081029 < baseStart_4081029 := by decide
  rcases family_descends (prefixWord ++ tailWord_4081029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4081056 : List Nat := [2, 1, 1, 4, 1, 2, 2, 3, 3, 4]
def baseStart_4081056 : Nat := 118140960795 + 4081056 * 2 ^ 59
def prefixEnd_4081056 : Nat := 4983230072969 + 3 ^ 40 * 4081056 * 2
def baseEnd_4081056 : Nat := 698514435305096694443857

theorem tailTrace_4081056 : CollatzResearch.WordTrace tailWord_4081056 prefixEnd_4081056 698514435305096694443857 := by
  unfold tailWord_4081056
  simp only [CollatzResearch.WordTrace]
  refine ⟨74424170351519287859895511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99232227135359050479860681 74424170351519287859895511)
  ·
    refine ⟨111636255527278931789843267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74424170351519287859895511 111636255527278931789843267)
    ·
      refine ⟨167454383290918397684764901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111636255527278931789843267 167454383290918397684764901)
      ·
        refine ⟨31397696867047199565893419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 167454383290918397684764901 31397696867047199565893419)
        ·
          refine ⟨47096545300570799348840129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31397696867047199565893419 47096545300570799348840129)
          ·
            refine ⟨35322408975428099511630097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47096545300570799348840129 35322408975428099511630097)
            ·
              refine ⟨26491806731571074633722573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35322408975428099511630097 26491806731571074633722573)
              ·
                refine ⟨9934427524339152987645965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26491806731571074633722573 9934427524339152987645965)
                ·
                  refine ⟨3725410321627182370367237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9934427524339152987645965 3725410321627182370367237)
                  ·
                    refine ⟨698514435305096694443857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3725410321627182370367237 698514435305096694443857)
                    ·
                      rfl

theorem cell23_4081056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 3, 3, 4].length) (baseStart_4081056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4081056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4081056 prefixEnd_4081056 := by exact prefixLift 4081056
  have htrace : WordTrace (prefixWord ++ tailWord_4081056) baseStart_4081056 baseEnd_4081056 := by
    simpa [prefixWord, tailWord_4081056, baseEnd_4081056] using wordTrace_append hprefix tailTrace_4081056
  have hstable : (prefixWord ++ tailWord_4081056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4081056).length < 2 ^ (prefixWord ++ tailWord_4081056).sum := by decide
  have hdescent : baseEnd_4081056 < baseStart_4081056 := by decide
  rcases family_descends (prefixWord ++ tailWord_4081056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4081063 : List Nat := [1, 1, 6, 1, 1, 1, 3, 1, 2, 4, 2]
def baseStart_4081063 : Nat := 118140960795 + 4081063 * 2 ^ 59
def prefixEnd_4081063 : Nat := 4983230072969 + 3 ^ 40 * 4081063 * 2
def baseEnd_4081063 : Nat := 2095546900279871555944039

theorem tailTrace_4081063 : CollatzResearch.WordTrace tailWord_4081063 prefixEnd_4081063 2095546900279871555944039 := by
  unfold tailWord_4081063
  simp only [CollatzResearch.WordTrace]
  refine ⟨148848596014013215915295843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99232397342675477276863895 148848596014013215915295843)
  ·
    refine ⟨223272894021019823872943765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148848596014013215915295843 223272894021019823872943765)
    ·
      refine ⟨10465916907235304244044239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 223272894021019823872943765 10465916907235304244044239)
      ·
        refine ⟨15698875360852956366066359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10465916907235304244044239 15698875360852956366066359)
        ·
          refine ⟨23548313041279434549099539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15698875360852956366066359 23548313041279434549099539)
          ·
            refine ⟨35322469561919151823649309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23548313041279434549099539 35322469561919151823649309)
            ·
              refine ⟨13245926085719681933868491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35322469561919151823649309 13245926085719681933868491)
              ·
                refine ⟨19868889128579522900802737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13245926085719681933868491 19868889128579522900802737)
                ·
                  refine ⟨14901666846434642175602053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19868889128579522900802737 14901666846434642175602053)
                  ·
                    refine ⟨2794062533706495407925385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14901666846434642175602053 2794062533706495407925385)
                    ·
                      refine ⟨2095546900279871555944039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2794062533706495407925385 2095546900279871555944039)
                      ·
                        rfl

theorem cell23_4081063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 1, 2, 4, 2].length) (baseStart_4081063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4081063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4081063 prefixEnd_4081063 := by exact prefixLift 4081063
  have htrace : WordTrace (prefixWord ++ tailWord_4081063) baseStart_4081063 baseEnd_4081063 := by
    simpa [prefixWord, tailWord_4081063, baseEnd_4081063] using wordTrace_append hprefix tailTrace_4081063
  have hstable : (prefixWord ++ tailWord_4081063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4081063).length < 2 ^ (prefixWord ++ tailWord_4081063).sum := by decide
  have hdescent : baseEnd_4081063 < baseStart_4081063 := by decide
  rcases family_descends (prefixWord ++ tailWord_4081063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4081113 : List Nat := [1, 2, 1, 2, 4, 2, 1, 3, 3, 1, 3]
def baseStart_4081113 : Nat := 118140960795 + 4081113 * 2 ^ 59
def prefixEnd_4081113 : Nat := 4983230072969 + 3 ^ 40 * 4081113 * 2
def baseEnd_4081113 : Nat := 2095572574312596360318809

theorem tailTrace_4081113 : CollatzResearch.WordTrace tailWord_4081113 prefixEnd_4081113 2095572574312596360318809 := by
  unfold tailWord_4081113
  simp only [CollatzResearch.WordTrace]
  refine ⟨148850419663832074454615993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99233613109221382969743995 148850419663832074454615993)
  ·
    refine ⟨111637814747874055840961995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148850419663832074454615993 111637814747874055840961995)
    ·
      refine ⟨167456722121811083761442993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111637814747874055840961995 167456722121811083761442993)
      ·
        refine ⟨125592541591358312821082245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167456722121811083761442993 125592541591358312821082245)
        ·
          refine ⟨23548601548379683653952921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125592541591358312821082245 23548601548379683653952921)
          ·
            refine ⟨17661451161284762740464691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23548601548379683653952921 17661451161284762740464691)
            ·
              refine ⟨26492176741927144110697037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17661451161284762740464691 26492176741927144110697037)
              ·
                refine ⟨9934566278222679041511389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26492176741927144110697037 9934566278222679041511389)
                ·
                  refine ⟨3725462354333504640566771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9934566278222679041511389 3725462354333504640566771)
                  ·
                    refine ⟨5588193531500256960850157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3725462354333504640566771 5588193531500256960850157)
                    ·
                      refine ⟨2095572574312596360318809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5588193531500256960850157 2095572574312596360318809)
                      ·
                        rfl

theorem cell23_4081113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 3, 3, 1, 3].length) (baseStart_4081113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4081113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4081113 prefixEnd_4081113 := by exact prefixLift 4081113
  have htrace : WordTrace (prefixWord ++ tailWord_4081113) baseStart_4081113 baseEnd_4081113 := by
    simpa [prefixWord, tailWord_4081113, baseEnd_4081113] using wordTrace_append hprefix tailTrace_4081113
  have hstable : (prefixWord ++ tailWord_4081113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4081113).length < 2 ^ (prefixWord ++ tailWord_4081113).sum := by decide
  have hdescent : baseEnd_4081113 < baseStart_4081113 := by decide
  rcases family_descends (prefixWord ++ tailWord_4081113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4081123 : List Nat := [1, 1, 1, 6, 2, 1, 1, 2, 1, 5, 2]
def baseStart_4081123 : Nat := 118140960795 + 4081123 * 2 ^ 59
def prefixEnd_4081123 : Nat := 4983230072969 + 3 ^ 40 * 4081123 * 2
def baseEnd_4081123 : Nat := 2095577709119141321193763

theorem tailTrace_4081123 : CollatzResearch.WordTrace tailWord_4081123 prefixEnd_4081123 2095577709119141321193763 := by
  unfold tailWord_4081123
  simp only [CollatzResearch.WordTrace]
  refine ⟨148850784393795846162480023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99233856262530564108320015 148850784393795846162480023)
  ·
    refine ⟨223276176590693769243720035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148850784393795846162480023 223276176590693769243720035)
    ·
      refine ⟨334914264886040653865580053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223276176590693769243720035 334914264886040653865580053)
      ·
        refine ⟨15699106166533155649949065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 334914264886040653865580053 15699106166533155649949065)
        ·
          refine ⟨11774329624899866737461799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15699106166533155649949065 11774329624899866737461799)
          ·
            refine ⟨17661494437349800106192699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11774329624899866737461799 17661494437349800106192699)
            ·
              refine ⟨26492241656024700159289049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17661494437349800106192699 26492241656024700159289049)
              ·
                refine ⟨19869181242018525119466787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26492241656024700159289049 19869181242018525119466787)
                ·
                  refine ⟨29803771863027787679200181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19869181242018525119466787 29803771863027787679200181)
                  ·
                    refine ⟨2794103612158855094925017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29803771863027787679200181 2794103612158855094925017)
                    ·
                      refine ⟨2095577709119141321193763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2794103612158855094925017 2095577709119141321193763)
                      ·
                        rfl

theorem cell23_4081123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 2, 1, 5, 2].length) (baseStart_4081123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4081123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4081123 prefixEnd_4081123 := by exact prefixLift 4081123
  have htrace : WordTrace (prefixWord ++ tailWord_4081123) baseStart_4081123 baseEnd_4081123 := by
    simpa [prefixWord, tailWord_4081123, baseEnd_4081123] using wordTrace_append hprefix tailTrace_4081123
  have hstable : (prefixWord ++ tailWord_4081123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4081123).length < 2 ^ (prefixWord ++ tailWord_4081123).sum := by decide
  have hdescent : baseEnd_4081123 < baseStart_4081123 := by decide
  rcases family_descends (prefixWord ++ tailWord_4081123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4081146 : List Nat := [3, 1, 1, 1, 1, 2, 3, 1, 6, 4]
def baseStart_4081146 : Nat := 118140960795 + 4081146 * 2 ^ 59
def prefixEnd_4081146 : Nat := 4983230072969 + 3 ^ 40 * 4081146 * 2
def baseEnd_4081146 : Nat := 698529839724731577068719

theorem tailTrace_4081146 : CollatzResearch.WordTrace tailWord_4081146 prefixEnd_4081146 698529839724731577068719 := by
  unfold tailWord_4081146
  simp only [CollatzResearch.WordTrace]
  refine ⟨37212905818178130272641823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99234415515141680727044861 37212905818178130272641823)
  ·
    refine ⟨55819358727267195408962735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37212905818178130272641823 55819358727267195408962735)
    ·
      refine ⟨83729038090900793113444103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55819358727267195408962735 83729038090900793113444103)
      ·
        refine ⟨125593557136351189670166155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83729038090900793113444103 125593557136351189670166155)
        ·
          refine ⟨188390335704526784505249233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125593557136351189670166155 188390335704526784505249233)
          ·
            refine ⟨141292751778395088378936925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188390335704526784505249233 141292751778395088378936925)
            ·
              refine ⟨52984781916898158142101347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141292751778395088378936925 52984781916898158142101347)
              ·
                refine ⟨79477172875347237213152021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52984781916898158142101347 79477172875347237213152021)
                ·
                  refine ⟨3725492478531901744366501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 79477172875347237213152021 3725492478531901744366501)
                  ·
                    refine ⟨698529839724731577068719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3725492478531901744366501 698529839724731577068719)
                    ·
                      rfl

theorem cell23_4081146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 1, 6, 4].length) (baseStart_4081146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4081146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4081146 prefixEnd_4081146 := by exact prefixLift 4081146
  have htrace : WordTrace (prefixWord ++ tailWord_4081146) baseStart_4081146 baseEnd_4081146 := by
    simpa [prefixWord, tailWord_4081146, baseEnd_4081146] using wordTrace_append hprefix tailTrace_4081146
  have hstable : (prefixWord ++ tailWord_4081146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4081146).length < 2 ^ (prefixWord ++ tailWord_4081146).sum := by decide
  have hdescent : baseEnd_4081146 < baseStart_4081146 := by decide
  rcases family_descends (prefixWord ++ tailWord_4081146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4081158 : List Nat := [6, 2, 1, 1, 2, 1, 3, 2, 1, 4]
def baseStart_4081158 : Nat := 118140960795 + 4081158 * 2 ^ 59
def prefixEnd_4081158 : Nat := 4983230072969 + 3 ^ 40 * 4081158 * 2
def baseEnd_4081158 : Nat := 698531893647349561418701

theorem tailTrace_4081158 : CollatzResearch.WordTrace tailWord_4081158 prefixEnd_4081158 698531893647349561418701 := by
  unfold tailWord_4081158
  simp only [CollatzResearch.WordTrace]
  refine ⟨4651626904645907723125129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 99234707299112698093336085 4651626904645907723125129)
  ·
    refine ⟨3488720178484430792343847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4651626904645907723125129 3488720178484430792343847)
    ·
      refine ⟨5233080267726646188515771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3488720178484430792343847 5233080267726646188515771)
      ·
        refine ⟨7849620401589969282773657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5233080267726646188515771 7849620401589969282773657)
        ·
          refine ⟨5887215301192476962080243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7849620401589969282773657 5887215301192476962080243)
          ·
            refine ⟨8830822951788715443120365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5887215301192476962080243 8830822951788715443120365)
            ·
              refine ⟨3311558606920768291170137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8830822951788715443120365 3311558606920768291170137)
              ·
                refine ⟨2483668955190576218377603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3311558606920768291170137 2483668955190576218377603)
                ·
                  refine ⟨3725503432785864327566405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2483668955190576218377603 3725503432785864327566405)
                  ·
                    refine ⟨698531893647349561418701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3725503432785864327566405 698531893647349561418701)
                    ·
                      rfl

theorem cell23_4081158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_4081158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4081158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4081158 prefixEnd_4081158 := by exact prefixLift 4081158
  have htrace : WordTrace (prefixWord ++ tailWord_4081158) baseStart_4081158 baseEnd_4081158 := by
    simpa [prefixWord, tailWord_4081158, baseEnd_4081158] using wordTrace_append hprefix tailTrace_4081158
  have hstable : (prefixWord ++ tailWord_4081158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4081158).length < 2 ^ (prefixWord ++ tailWord_4081158).sum := by decide
  have hdescent : baseEnd_4081158 < baseStart_4081158 := by decide
  rcases family_descends (prefixWord ++ tailWord_4081158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4081164 : List Nat := [2, 2, 1, 2, 5, 1, 3, 2, 1, 1, 3]
def baseStart_4081164 : Nat := 118140960795 + 4081164 * 2 ^ 59
def prefixEnd_4081164 : Nat := 4983230072969 + 3 ^ 40 * 4081164 * 2
def baseEnd_4081164 : Nat := 2095598761825975660781075

theorem tailTrace_4081164 : CollatzResearch.WordTrace tailWord_4081164 prefixEnd_4081164 2095598761825975660781075 := by
  unfold tailWord_4081164
  simp only [CollatzResearch.WordTrace]
  refine ⟨74426139893323655082361273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99234853191098206776481697 74426139893323655082361273)
  ·
    refine ⟨55819604919992741311770955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74426139893323655082361273 55819604919992741311770955)
    ·
      refine ⟨83729407379989111967656433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55819604919992741311770955 83729407379989111967656433)
      ·
        refine ⟨62797055534991833975742325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83729407379989111967656433 62797055534991833975742325)
        ·
          refine ⟨5887223956405484435225843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 62797055534991833975742325 5887223956405484435225843)
          ·
            refine ⟨8830835934608226652838765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5887223956405484435225843 8830835934608226652838765)
            ·
              refine ⟨3311563475478084994814537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8830835934608226652838765 3311563475478084994814537)
              ·
                refine ⟨2483672606608563746110903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3311563475478084994814537 2483672606608563746110903)
                ·
                  refine ⟨3725508909912845619166355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2483672606608563746110903 3725508909912845619166355)
                  ·
                    refine ⟨5588263364869268428749533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3725508909912845619166355 5588263364869268428749533)
                    ·
                      refine ⟨2095598761825975660781075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5588263364869268428749533 2095598761825975660781075)
                      ·
                        rfl

theorem cell23_4081164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 3, 2, 1, 1, 3].length) (baseStart_4081164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4081164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4081164 prefixEnd_4081164 := by exact prefixLift 4081164
  have htrace : WordTrace (prefixWord ++ tailWord_4081164) baseStart_4081164 baseEnd_4081164 := by
    simpa [prefixWord, tailWord_4081164, baseEnd_4081164] using wordTrace_append hprefix tailTrace_4081164
  have hstable : (prefixWord ++ tailWord_4081164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4081164).length < 2 ^ (prefixWord ++ tailWord_4081164).sum := by decide
  have hdescent : baseEnd_4081164 < baseStart_4081164 := by decide
  rcases family_descends (prefixWord ++ tailWord_4081164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4081187 : List Nat := [1, 1, 1, 4, 6, 1, 1, 2, 1, 1, 4]
def baseStart_4081187 : Nat := 118140960795 + 4081187 * 2 ^ 59
def prefixEnd_4081187 : Nat := 4983230072969 + 3 ^ 40 * 4081187 * 2
def baseEnd_4081187 : Nat := 2095610571881029070793469

theorem tailTrace_4081187 : CollatzResearch.WordTrace tailWord_4081187 prefixEnd_4081187 2095610571881029070793469 := by
  unfold tailWord_4081187
  simp only [CollatzResearch.WordTrace]
  refine ⟨148853118665563985092809815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99235412443709323395206543 148853118665563985092809815)
  ·
    refine ⟨223279677998345977639214723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148853118665563985092809815 223279677998345977639214723)
    ·
      refine ⟨334919516997518966458822085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223279677998345977639214723 334919516997518966458822085)
      ·
        refine ⟨62797409437034806211029141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 334919516997518966458822085 62797409437034806211029141)
        ·
          refine ⟨2943628567361006541141991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 62797409437034806211029141 2943628567361006541141991)
          ·
            refine ⟨4415442851041509811712987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2943628567361006541141991 4415442851041509811712987)
            ·
              refine ⟨6623164276562264717569481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4415442851041509811712987 6623164276562264717569481)
              ·
                refine ⟨4967373207421698538177111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6623164276562264717569481 4967373207421698538177111)
                ·
                  refine ⟨7451059811132547807265667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4967373207421698538177111 7451059811132547807265667)
                  ·
                    refine ⟨11176589716698821710898501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7451059811132547807265667 11176589716698821710898501)
                    ·
                      refine ⟨2095610571881029070793469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11176589716698821710898501 2095610571881029070793469)
                      ·
                        rfl

theorem cell23_4081187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 1, 2, 1, 1, 4].length) (baseStart_4081187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4081187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4081187 prefixEnd_4081187 := by exact prefixLift 4081187
  have htrace : WordTrace (prefixWord ++ tailWord_4081187) baseStart_4081187 baseEnd_4081187 := by
    simpa [prefixWord, tailWord_4081187, baseEnd_4081187] using wordTrace_append hprefix tailTrace_4081187
  have hstable : (prefixWord ++ tailWord_4081187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4081187).length < 2 ^ (prefixWord ++ tailWord_4081187).sum := by decide
  have hdescent : baseEnd_4081187 < baseStart_4081187 := by decide
  rcases family_descends (prefixWord ++ tailWord_4081187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4081203 : List Nat := [1, 1, 1, 2, 4, 4, 1, 2, 1, 3, 3]
def baseStart_4081203 : Nat := 118140960795 + 4081203 * 2 ^ 59
def prefixEnd_4081203 : Nat := 4983230072969 + 3 ^ 40 * 4081203 * 2
def baseEnd_4081203 : Nat := 2095618787571501008193395

theorem tailTrace_4081203 : CollatzResearch.WordTrace tailWord_4081203 prefixEnd_4081203 2095618787571501008193395 := by
  unfold tailWord_4081203
  simp only [CollatzResearch.WordTrace]
  refine ⟨148853702233506019825392263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99235801489004013216928175 148853702233506019825392263)
  ·
    refine ⟨223280553350259029738088395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148853702233506019825392263 223280553350259029738088395)
    ·
      refine ⟨334920830025388544607132593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223280553350259029738088395 334920830025388544607132593)
      ·
        refine ⟨251190622519041408455349445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 334920830025388544607132593 251190622519041408455349445)
        ·
          refine ⟨47098241722320264085378021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 251190622519041408455349445 47098241722320264085378021)
          ·
            refine ⟨8830920322935049516008379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47098241722320264085378021 8830920322935049516008379)
            ·
              refine ⟨13246380484402574274012569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8830920322935049516008379 13246380484402574274012569)
              ·
                refine ⟨9934785363301930705509427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13246380484402574274012569 9934785363301930705509427)
                ·
                  refine ⟨14902178044952896058264141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9934785363301930705509427 14902178044952896058264141)
                  ·
                    refine ⟨5588316766857336021849053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14902178044952896058264141 5588316766857336021849053)
                    ·
                      refine ⟨2095618787571501008193395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5588316766857336021849053 2095618787571501008193395)
                      ·
                        rfl

theorem cell23_4081203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 2, 1, 3, 3].length) (baseStart_4081203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4081203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4081203 prefixEnd_4081203 := by exact prefixLift 4081203
  have htrace : WordTrace (prefixWord ++ tailWord_4081203) baseStart_4081203 baseEnd_4081203 := by
    simpa [prefixWord, tailWord_4081203, baseEnd_4081203] using wordTrace_append hprefix tailTrace_4081203
  have hstable : (prefixWord ++ tailWord_4081203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4081203).length < 2 ^ (prefixWord ++ tailWord_4081203).sum := by decide
  have hdescent : baseEnd_4081203 < baseStart_4081203 := by decide
  rcases family_descends (prefixWord ++ tailWord_4081203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4081226 : List Nat := [3, 1, 2, 1, 1, 3, 1, 1, 1, 5, 4]
def baseStart_4081226 : Nat := 118140960795 + 4081226 * 2 ^ 59
def prefixEnd_4081226 : Nat := 4983230072969 + 3 ^ 40 * 4081226 * 2
def baseEnd_4081226 : Nat := 2095630597626554418205789

theorem tailTrace_4081226 : CollatzResearch.WordTrace tailWord_4081226 prefixEnd_4081226 2095630597626554418205789 := by
  unfold tailWord_4081226
  simp only [CollatzResearch.WordTrace]
  refine ⟨37213635278105673688369883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99236360741615129835653021 37213635278105673688369883)
  ·
    refine ⟨55820452917158510532554825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37213635278105673688369883 55820452917158510532554825)
    ·
      refine ⟨41865339687868882899416119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55820452917158510532554825 41865339687868882899416119)
      ·
        refine ⟨62798009531803324349124179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41865339687868882899416119 62798009531803324349124179)
        ·
          refine ⟨94197014297704986523686269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62798009531803324349124179 94197014297704986523686269)
          ·
            refine ⟨35323880361639369946382351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94197014297704986523686269 35323880361639369946382351)
            ·
              refine ⟨52985820542459054919573527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35323880361639369946382351 52985820542459054919573527)
              ·
                refine ⟨79478730813688582379360291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52985820542459054919573527 79478730813688582379360291)
                ·
                  refine ⟨119218096220532873569040437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79478730813688582379360291 119218096220532873569040437)
                  ·
                    refine ⟨11176696520674956897097541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 119218096220532873569040437 11176696520674956897097541)
                    ·
                      refine ⟨2095630597626554418205789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11176696520674956897097541 2095630597626554418205789)
                      ·
                        rfl

theorem cell23_4081226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 1, 1, 5, 4].length) (baseStart_4081226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4081226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4081226 prefixEnd_4081226 := by exact prefixLift 4081226
  have htrace : WordTrace (prefixWord ++ tailWord_4081226) baseStart_4081226 baseEnd_4081226 := by
    simpa [prefixWord, tailWord_4081226, baseEnd_4081226] using wordTrace_append hprefix tailTrace_4081226
  have hstable : (prefixWord ++ tailWord_4081226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4081226).length < 2 ^ (prefixWord ++ tailWord_4081226).sum := by decide
  have hdescent : baseEnd_4081226 < baseStart_4081226 := by decide
  rcases family_descends (prefixWord ++ tailWord_4081226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4081260 : List Nat := [2, 2, 1, 1, 3, 1, 1, 4, 4, 2, 2]
def baseStart_4081260 : Nat := 118140960795 + 4081260 * 2 ^ 59
def prefixEnd_4081260 : Nat := 4983230072969 + 3 ^ 40 * 4081260 * 2
def baseEnd_4081260 : Nat := 2095648055968807285180633

theorem tailTrace_4081260 : CollatzResearch.WordTrace tailWord_4081260 prefixEnd_4081260 2095648055968807285180633 := by
  unfold tailWord_4081260
  simp only [CollatzResearch.WordTrace]
  refine ⟨74427890597149759280108617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99237187462866345706811489 74427890597149759280108617)
  ·
    refine ⟨55820917947862319460081463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74427890597149759280108617 55820917947862319460081463)
    ·
      refine ⟨83731376921793479190122195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55820917947862319460081463 83731376921793479190122195)
      ·
        refine ⟨125597065382690218785183293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83731376921793479190122195 125597065382690218785183293)
        ·
          refine ⟨47098899518508832044443735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125597065382690218785183293 47098899518508832044443735)
          ·
            refine ⟨70648349277763248066665603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47098899518508832044443735 70648349277763248066665603)
            ·
              refine ⟨105972523916644872099998405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70648349277763248066665603 105972523916644872099998405)
              ·
                refine ⟨19869848234370913518749701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 105972523916644872099998405 19869848234370913518749701)
                ·
                  refine ⟨3725596543944546284765569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19869848234370913518749701 3725596543944546284765569)
                  ·
                    refine ⟨2794197407958409713574177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3725596543944546284765569 2794197407958409713574177)
                    ·
                      refine ⟨2095648055968807285180633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2794197407958409713574177 2095648055968807285180633)
                      ·
                        rfl

theorem cell23_4081260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 2, 2].length) (baseStart_4081260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4081260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4081260 prefixEnd_4081260 := by exact prefixLift 4081260
  have htrace : WordTrace (prefixWord ++ tailWord_4081260) baseStart_4081260 baseEnd_4081260 := by
    simpa [prefixWord, tailWord_4081260, baseEnd_4081260] using wordTrace_append hprefix tailTrace_4081260
  have hstable : (prefixWord ++ tailWord_4081260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4081260).length < 2 ^ (prefixWord ++ tailWord_4081260).sum := by decide
  have hdescent : baseEnd_4081260 < baseStart_4081260 := by decide
  rcases family_descends (prefixWord ++ tailWord_4081260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4081264 : List Nat := [2, 1, 1, 1, 6, 3, 2, 1, 1, 3, 2]
def baseStart_4081264 : Nat := 118140960795 + 4081264 * 2 ^ 59
def prefixEnd_4081264 : Nat := 4983230072969 + 3 ^ 40 * 4081264 * 2
def baseEnd_4081264 : Nat := 2095650109891425269530615

theorem tailTrace_4081264 : CollatzResearch.WordTrace tailWord_4081264 prefixEnd_4081264 2095650109891425269530615 := by
  unfold tailWord_4081264
  simp only [CollatzResearch.WordTrace]
  refine ⟨74427963543142513621681423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99237284724190018162241897 74427963543142513621681423)
  ·
    refine ⟨111641945314713770432522135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74427963543142513621681423 111641945314713770432522135)
    ·
      refine ⟨167462917972070655648783203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111641945314713770432522135 167462917972070655648783203)
      ·
        refine ⟨251194376958105983473174805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167462917972070655648783203 251194376958105983473174805)
        ·
          refine ⟨11774736419911217975305069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 251194376958105983473174805 11774736419911217975305069)
          ·
            refine ⟨4415526157466706740739401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11774736419911217975305069 4415526157466706740739401)
            ·
              refine ⟨3311644618100030055554551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4415526157466706740739401 3311644618100030055554551)
              ·
                refine ⟨4967466927150045083331827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3311644618100030055554551 4967466927150045083331827)
                ·
                  refine ⟨7451200390725067624997741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4967466927150045083331827 7451200390725067624997741)
                  ·
                    refine ⟨2794200146521900359374153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7451200390725067624997741 2794200146521900359374153)
                    ·
                      refine ⟨2095650109891425269530615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2794200146521900359374153 2095650109891425269530615)
                      ·
                        rfl

theorem cell23_4081264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 2, 1, 1, 3, 2].length) (baseStart_4081264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4081264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4081264 prefixEnd_4081264 := by exact prefixLift 4081264
  have htrace : WordTrace (prefixWord ++ tailWord_4081264) baseStart_4081264 baseEnd_4081264 := by
    simpa [prefixWord, tailWord_4081264, baseEnd_4081264] using wordTrace_append hprefix tailTrace_4081264
  have hstable : (prefixWord ++ tailWord_4081264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4081264).length < 2 ^ (prefixWord ++ tailWord_4081264).sum := by decide
  have hdescent : baseEnd_4081264 < baseStart_4081264 := by decide
  rcases family_descends (prefixWord ++ tailWord_4081264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4081277 : List Nat := [1, 4, 1, 1, 4, 2, 1, 1, 4, 2, 2]
def baseStart_4081277 : Nat := 118140960795 + 4081277 * 2 ^ 59
def prefixEnd_4081277 : Nat := 4983230072969 + 3 ^ 40 * 4081277 * 2
def baseEnd_4081277 : Nat := 2095656785139933718668055

theorem tailTrace_4081277 : CollatzResearch.WordTrace tailWord_4081277 prefixEnd_4081277 2095656785139933718668055 := by
  unfold tailWord_4081277
  simp only [CollatzResearch.WordTrace]
  refine ⟨148856401235237930463586085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99237600823491953642390723 148856401235237930463586085)
  ·
    refine ⟨27910575231607111961922391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 148856401235237930463586085 27910575231607111961922391)
    ·
      refine ⟨41865862847410667942883587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27910575231607111961922391 41865862847410667942883587)
      ·
        refine ⟨62798794271116001914325381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41865862847410667942883587 62798794271116001914325381)
        ·
          refine ⟨11774773925834250358936009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62798794271116001914325381 11774773925834250358936009)
          ·
            refine ⟨8831080444375687769202007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11774773925834250358936009 8831080444375687769202007)
            ·
              refine ⟨13246620666563531653803011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8831080444375687769202007 13246620666563531653803011)
              ·
                refine ⟨19869930999845297480704517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13246620666563531653803011 19869930999845297480704517)
                ·
                  refine ⟨3725612062470993277632097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19869930999845297480704517 3725612062470993277632097)
                  ·
                    refine ⟨2794209046853244958224073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3725612062470993277632097 2794209046853244958224073)
                    ·
                      refine ⟨2095656785139933718668055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2794209046853244958224073 2095656785139933718668055)
                      ·
                        rfl

theorem cell23_4081277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 1, 4, 2, 2].length) (baseStart_4081277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4081277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4081277 prefixEnd_4081277 := by exact prefixLift 4081277
  have htrace : WordTrace (prefixWord ++ tailWord_4081277) baseStart_4081277 baseEnd_4081277 := by
    simpa [prefixWord, tailWord_4081277, baseEnd_4081277] using wordTrace_append hprefix tailTrace_4081277
  have hstable : (prefixWord ++ tailWord_4081277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4081277).length < 2 ^ (prefixWord ++ tailWord_4081277).sum := by decide
  have hdescent : baseEnd_4081277 < baseStart_4081277 := by decide
  rcases family_descends (prefixWord ++ tailWord_4081277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4081313 : List Nat := [1, 2, 3, 3, 2, 1, 2, 1, 1, 7]
def baseStart_4081313 : Nat := 118140960795 + 4081313 * 2 ^ 59
def prefixEnd_4081313 : Nat := 4983230072969 + 3 ^ 40 * 4081313 * 2
def baseEnd_4081313 : Nat := 698558423481165192605963

theorem tailTrace_4081313 : CollatzResearch.WordTrace tailWord_4081313 prefixEnd_4081313 698558423481165192605963 := by
  unfold tailWord_4081313
  simp only [CollatzResearch.WordTrace]
  refine ⟨148857714263107508611896593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99238476175405005741264395 148857714263107508611896593)
  ·
    refine ⟨111643285697330631458922445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148857714263107508611896593 111643285697330631458922445)
    ·
      refine ⟨41866232136498986797095917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111643285697330631458922445 41866232136498986797095917)
      ·
        refine ⟨15699837051187120048910969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41866232136498986797095917 15699837051187120048910969)
        ·
          refine ⟨11774877788390340036683227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15699837051187120048910969 11774877788390340036683227)
          ·
            refine ⟨17662316682585510055024841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11774877788390340036683227 17662316682585510055024841)
            ·
              refine ⟨13246737511939132541268631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17662316682585510055024841 13246737511939132541268631)
              ·
                refine ⟨19870106267908698811902947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13246737511939132541268631 19870106267908698811902947)
                ·
                  refine ⟨29805159401863048217854421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19870106267908698811902947 29805159401863048217854421)
                  ·
                    refine ⟨698558423481165192605963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29805159401863048217854421 698558423481165192605963)
                    ·
                      rfl

theorem cell23_4081313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 1, 1, 7].length) (baseStart_4081313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4081313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4081313 prefixEnd_4081313 := by exact prefixLift 4081313
  have htrace : WordTrace (prefixWord ++ tailWord_4081313) baseStart_4081313 baseEnd_4081313 := by
    simpa [prefixWord, tailWord_4081313, baseEnd_4081313] using wordTrace_append hprefix tailTrace_4081313
  have hstable : (prefixWord ++ tailWord_4081313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4081313).length < 2 ^ (prefixWord ++ tailWord_4081313).sum := by decide
  have hdescent : baseEnd_4081313 < baseStart_4081313 := by decide
  rcases family_descends (prefixWord ++ tailWord_4081313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4081370 : List Nat := [3, 1, 1, 2, 2, 3, 1, 3, 2, 2, 3]
def baseStart_4081370 : Nat := 118140960795 + 4081370 * 2 ^ 59
def prefixEnd_4081370 : Nat := 4983230072969 + 3 ^ 40 * 4081370 * 2
def baseEnd_4081370 : Nat := 2095704538840801854805127

theorem tailTrace_4081370 : CollatzResearch.WordTrace tailWord_4081370 prefixEnd_4081370 2095704538840801854805127 := by
  unfold tailWord_4081370
  simp only [CollatzResearch.WordTrace]
  refine ⟨37214948305975251836680391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99239862149267338231147709 37214948305975251836680391)
  ·
    refine ⟨55822422458962877755020587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37214948305975251836680391 55822422458962877755020587)
    ·
      refine ⟨83733633688444316632530881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55822422458962877755020587 83733633688444316632530881)
      ·
        refine ⟨62800225266333237474398161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83733633688444316632530881 62800225266333237474398161)
        ·
          refine ⟨47100168949749928105798621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62800225266333237474398161 47100168949749928105798621)
          ·
            refine ⟨17662563356156223039674483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47100168949749928105798621 17662563356156223039674483)
            ·
              refine ⟨26493845034234334559511725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17662563356156223039674483 26493845034234334559511725)
              ·
                refine ⟨9935191887837875459816897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26493845034234334559511725 9935191887837875459816897)
                ·
                  refine ⟨7451393915878406594862673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9935191887837875459816897 7451393915878406594862673)
                  ·
                    refine ⟨5588545436908804946147005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7451393915878406594862673 5588545436908804946147005)
                    ·
                      refine ⟨2095704538840801854805127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5588545436908804946147005 2095704538840801854805127)
                      ·
                        rfl

theorem cell23_4081370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 3, 2, 2, 3].length) (baseStart_4081370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4081370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4081370 prefixEnd_4081370 := by exact prefixLift 4081370
  have htrace : WordTrace (prefixWord ++ tailWord_4081370) baseStart_4081370 baseEnd_4081370 := by
    simpa [prefixWord, tailWord_4081370, baseEnd_4081370] using wordTrace_append hprefix tailTrace_4081370
  have hstable : (prefixWord ++ tailWord_4081370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4081370).length < 2 ^ (prefixWord ++ tailWord_4081370).sum := by decide
  have hdescent : baseEnd_4081370 < baseStart_4081370 := by decide
  rcases family_descends (prefixWord ++ tailWord_4081370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4081390 : List Nat := [4, 1, 2, 1, 1, 2, 4, 2, 6]
def baseStart_4081390 : Nat := 118140960795 + 4081390 * 2 ^ 59
def prefixEnd_4081390 : Nat := 4983230072969 + 3 ^ 40 * 4081390 * 2
def baseEnd_4081390 : Nat := 232857200939321308506115

theorem tailTrace_4081390 : CollatzResearch.WordTrace tailWord_4081390 prefixEnd_4081390 232857200939321308506115 := by
  unfold tailWord_4081390
  simp only [CollatzResearch.WordTrace]
  refine ⟨18607565335478568845306203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99240348455885700508299749 18607565335478568845306203)
  ·
    refine ⟨27911348003217853267959305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18607565335478568845306203 27911348003217853267959305)
    ·
      refine ⟨20933511002413389950969479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27911348003217853267959305 20933511002413389950969479)
      ·
        refine ⟨31400266503620084926454219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20933511002413389950969479 31400266503620084926454219)
        ·
          refine ⟨47100399755430127389681329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31400266503620084926454219 47100399755430127389681329)
          ·
            refine ⟨35325299816572595542260997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47100399755430127389681329 35325299816572595542260997)
            ·
              refine ⟨6623493715607361664173937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35325299816572595542260997 6623493715607361664173937)
              ·
                refine ⟨4967620286705521248130453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6623493715607361664173937 4967620286705521248130453)
                ·
                  refine ⟨232857200939321308506115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4967620286705521248130453 232857200939321308506115)
                  ·
                    rfl

theorem cell23_4081390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 4, 2, 6].length) (baseStart_4081390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4081390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4081390 prefixEnd_4081390 := by exact prefixLift 4081390
  have htrace : WordTrace (prefixWord ++ tailWord_4081390) baseStart_4081390 baseEnd_4081390 := by
    simpa [prefixWord, tailWord_4081390, baseEnd_4081390] using wordTrace_append hprefix tailTrace_4081390
  have hstable : (prefixWord ++ tailWord_4081390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4081390).length < 2 ^ (prefixWord ++ tailWord_4081390).sum := by decide
  have hdescent : baseEnd_4081390 < baseStart_4081390 := by decide
  rcases family_descends (prefixWord ++ tailWord_4081390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4081434 : List Nat := [3, 1, 1, 3, 2, 2, 1, 5, 1, 1, 3]
def baseStart_4081434 : Nat := 118140960795 + 4081434 * 2 ^ 59
def prefixEnd_4081434 : Nat := 4983230072969 + 3 ^ 40 * 4081434 * 2
def baseEnd_4081434 : Nat := 2095737401602689604404833

theorem tailTrace_4081434 : CollatzResearch.WordTrace tailWord_4081434 prefixEnd_4081434 2095737401602689604404833 := by
  unfold tailWord_4081434
  simp only [CollatzResearch.WordTrace]
  refine ⟨37215531873917286569262839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99241418330446097518034237 37215531873917286569262839)
  ·
    refine ⟨55823297810875929853894259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37215531873917286569262839 55823297810875929853894259)
    ·
      refine ⟨83734946716313894780841389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55823297810875929853894259 83734946716313894780841389)
      ·
        refine ⟨31400605018617710542815521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83734946716313894780841389 31400605018617710542815521)
        ·
          refine ⟨23550453763963282907111641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31400605018617710542815521 23550453763963282907111641)
          ·
            refine ⟨17662840322972462180333731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23550453763963282907111641 17662840322972462180333731)
            ·
              refine ⟨26494260484458693270500597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17662840322972462180333731 26494260484458693270500597)
              ·
                refine ⟨2483836920418002494109431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26494260484458693270500597 2483836920418002494109431)
                ·
                  refine ⟨3725755380627003741164147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2483836920418002494109431 3725755380627003741164147)
                  ·
                    refine ⟨5588633070940505611746221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3725755380627003741164147 5588633070940505611746221)
                    ·
                      refine ⟨2095737401602689604404833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5588633070940505611746221 2095737401602689604404833)
                      ·
                        rfl

theorem cell23_4081434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 5, 1, 1, 3].length) (baseStart_4081434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4081434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4081434 prefixEnd_4081434 := by exact prefixLift 4081434
  have htrace : WordTrace (prefixWord ++ tailWord_4081434) baseStart_4081434 baseEnd_4081434 := by
    simpa [prefixWord, tailWord_4081434, baseEnd_4081434] using wordTrace_append hprefix tailTrace_4081434
  have hstable : (prefixWord ++ tailWord_4081434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4081434).length < 2 ^ (prefixWord ++ tailWord_4081434).sum := by decide
  have hdescent : baseEnd_4081434 < baseStart_4081434 := by decide
  rcases family_descends (prefixWord ++ tailWord_4081434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4081477 : List Nat := [1, 3, 1, 1, 1, 2, 6, 2, 1, 2, 3]
def baseStart_4081477 : Nat := 118140960795 + 4081477 * 2 ^ 59
def prefixEnd_4081477 : Nat := 4983230072969 + 3 ^ 40 * 4081477 * 2
def baseEnd_4081477 : Nat := 2095759481270832936167135

theorem tailTrace_4081477 : CollatzResearch.WordTrace tailWord_4081477 prefixEnd_4081477 2095759481270832936167135 := by
  unfold tailWord_4081477
  simp only [CollatzResearch.WordTrace]
  refine ⟨148863695834513364620866685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99242463889675576413911123 148863695834513364620866685)
  ·
    refine ⟨55823885937942511732825007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148863695834513364620866685 55823885937942511732825007)
    ·
      refine ⟨83735828906913767599237511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55823885937942511732825007 83735828906913767599237511)
      ·
        refine ⟨125603743360370651398856267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83735828906913767599237511 125603743360370651398856267)
        ·
          refine ⟨188405615040555977098284401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125603743360370651398856267 188405615040555977098284401)
          ·
            refine ⟨141304211280416982823713301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188405615040555977098284401 141304211280416982823713301)
            ·
              refine ⟨6623634903769546069861561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 141304211280416982823713301 6623634903769546069861561)
              ·
                refine ⟨4967726177827159552396171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6623634903769546069861561 4967726177827159552396171)
                ·
                  refine ⟨7451589266740739328594257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4967726177827159552396171 7451589266740739328594257)
                  ·
                    refine ⟨5588691950055554496445693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7451589266740739328594257 5588691950055554496445693)
                    ·
                      refine ⟨2095759481270832936167135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5588691950055554496445693 2095759481270832936167135)
                      ·
                        rfl

theorem cell23_4081477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 6, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 6, 2, 1, 2, 3].length) (baseStart_4081477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4081477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4081477 prefixEnd_4081477 := by exact prefixLift 4081477
  have htrace : WordTrace (prefixWord ++ tailWord_4081477) baseStart_4081477 baseEnd_4081477 := by
    simpa [prefixWord, tailWord_4081477, baseEnd_4081477] using wordTrace_append hprefix tailTrace_4081477
  have hstable : (prefixWord ++ tailWord_4081477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4081477).length < 2 ^ (prefixWord ++ tailWord_4081477).sum := by decide
  have hdescent : baseEnd_4081477 < baseStart_4081477 := by decide
  rcases family_descends (prefixWord ++ tailWord_4081477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4081480 : List Nat := [2, 1, 3, 1, 1, 4, 4, 7]
def baseStart_4081480 : Nat := 118140960795 + 4081480 * 2 ^ 59
def prefixEnd_4081480 : Nat := 4983230072969 + 3 ^ 40 * 4081480 * 2
def baseEnd_4081480 : Nat := 77620778581955423127023

theorem tailTrace_4081480 : CollatzResearch.WordTrace tailWord_4081480 prefixEnd_4081480 77620778581955423127023 := by
  unfold tailWord_4081480
  simp only [CollatzResearch.WordTrace]
  refine ⟨74431902626751248066612947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99242536835668330755483929 74431902626751248066612947)
  ·
    refine ⟨111647853940126872099919421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74431902626751248066612947 111647853940126872099919421)
    ·
      refine ⟨41867945227547577037469783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111647853940126872099919421 41867945227547577037469783)
      ·
        refine ⟨62801917841321365556204675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41867945227547577037469783 62801917841321365556204675)
        ·
          refine ⟨94202876761982048334307013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62801917841321365556204675 94202876761982048334307013)
          ·
            refine ⟨17663039392871634062682565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94202876761982048334307013 17663039392871634062682565)
            ·
              refine ⟨3311819886163431386752981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17663039392871634062682565 3311819886163431386752981)
              ·
                refine ⟨77620778581955423127023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3311819886163431386752981 77620778581955423127023)
                ·
                  rfl

theorem cell23_4081480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 4, 7].length) (baseStart_4081480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4081480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4081480 prefixEnd_4081480 := by exact prefixLift 4081480
  have htrace : WordTrace (prefixWord ++ tailWord_4081480) baseStart_4081480 baseEnd_4081480 := by
    simpa [prefixWord, tailWord_4081480, baseEnd_4081480] using wordTrace_append hprefix tailTrace_4081480
  have hstable : (prefixWord ++ tailWord_4081480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4081480).length < 2 ^ (prefixWord ++ tailWord_4081480).sum := by decide
  have hdescent : baseEnd_4081480 < baseStart_4081480 := by decide
  rcases family_descends (prefixWord ++ tailWord_4081480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4081508 : List Nat := [2, 3, 1, 1, 6, 1, 1, 1, 3, 2, 2]
def baseStart_4081508 : Nat := 118140960795 + 4081508 * 2 ^ 59
def prefixEnd_4081508 : Nat := 4983230072969 + 3 ^ 40 * 4081508 * 2
def baseEnd_4081508 : Nat := 2095775399171122314879493

theorem tailTrace_4081508 : CollatzResearch.WordTrace tailWord_4081508 prefixEnd_4081508 2095775399171122314879493 := by
  unfold tailWord_4081508
  simp only [CollatzResearch.WordTrace]
  refine ⟨74432413248700528457622589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99243217664934037943496785 74432413248700528457622589)
  ·
    refine ⟨27912154968262698171608471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74432413248700528457622589 27912154968262698171608471)
    ·
      refine ⟨41868232452394047257412707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27912154968262698171608471 41868232452394047257412707)
      ·
        refine ⟨62802348678591070886119061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41868232452394047257412707 62802348678591070886119061)
        ·
          refine ⟨2943860094308956447786831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 62802348678591070886119061 2943860094308956447786831)
          ·
            refine ⟨4415790141463434671680247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2943860094308956447786831 4415790141463434671680247)
            ·
              refine ⟨6623685212195152007520371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4415790141463434671680247 6623685212195152007520371)
              ·
                refine ⟨9935527818292728011280557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6623685212195152007520371 9935527818292728011280557)
                ·
                  refine ⟨3725822931859773004230209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9935527818292728011280557 3725822931859773004230209)
                  ·
                    refine ⟨2794367198894829753172657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3725822931859773004230209 2794367198894829753172657)
                    ·
                      refine ⟨2095775399171122314879493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2794367198894829753172657 2095775399171122314879493)
                      ·
                        rfl

theorem cell23_4081508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 1, 1, 3, 2, 2].length) (baseStart_4081508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4081508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4081508 prefixEnd_4081508 := by exact prefixLift 4081508
  have htrace : WordTrace (prefixWord ++ tailWord_4081508) baseStart_4081508 baseEnd_4081508 := by
    simpa [prefixWord, tailWord_4081508, baseEnd_4081508] using wordTrace_append hprefix tailTrace_4081508
  have hstable : (prefixWord ++ tailWord_4081508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4081508).length < 2 ^ (prefixWord ++ tailWord_4081508).sum := by decide
  have hdescent : baseEnd_4081508 < baseStart_4081508 := by decide
  rcases family_descends (prefixWord ++ tailWord_4081508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4081523 : List Nat := [1, 1, 1, 2, 2, 1, 3, 3, 1, 8]
def baseStart_4081523 : Nat := 118140960795 + 4081523 * 2 ^ 59
def prefixEnd_4081523 : Nat := 4983230072969 + 3 ^ 40 * 4081523 * 2
def baseEnd_4081523 : Nat := 698594367126979918730641

theorem tailTrace_4081523 : CollatzResearch.WordTrace tailWord_4081523 prefixEnd_4081523 698594367126979918730641 := by
  unfold tailWord_4081523
  simp only [CollatzResearch.WordTrace]
  refine ⟨148865373592346714477041223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99243582394897809651360815 148865373592346714477041223)
  ·
    refine ⟨223298060388520071715561835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148865373592346714477041223 223298060388520071715561835)
    ·
      refine ⟨334947090582780107573342753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223298060388520071715561835 334947090582780107573342753)
      ·
        refine ⟨251210317937085080680007065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 334947090582780107573342753 251210317937085080680007065)
        ·
          refine ⟨188407738452813810510005299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 251210317937085080680007065 188407738452813810510005299)
          ·
            refine ⟨282611607679220715765007949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188407738452813810510005299 282611607679220715765007949)
            ·
              refine ⟨105979352879707768411877981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 282611607679220715765007949 105979352879707768411877981)
              ·
                refine ⟨39742257329890413154454243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105979352879707768411877981 39742257329890413154454243)
                ·
                  refine ⟨59613385994835619731681365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39742257329890413154454243 59613385994835619731681365)
                  ·
                    refine ⟨698594367126979918730641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 59613385994835619731681365 698594367126979918730641)
                    ·
                      rfl

theorem cell23_4081523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 3, 1, 8].length) (baseStart_4081523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4081523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4081523 prefixEnd_4081523 := by exact prefixLift 4081523
  have htrace : WordTrace (prefixWord ++ tailWord_4081523) baseStart_4081523 baseEnd_4081523 := by
    simpa [prefixWord, tailWord_4081523, baseEnd_4081523] using wordTrace_append hprefix tailTrace_4081523
  have hstable : (prefixWord ++ tailWord_4081523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4081523).length < 2 ^ (prefixWord ++ tailWord_4081523).sum := by decide
  have hdescent : baseEnd_4081523 < baseStart_4081523 := by decide
  rcases family_descends (prefixWord ++ tailWord_4081523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4081600 : List Nat := [2, 1, 1, 2, 3, 2, 3, 1, 1, 7]
def baseStart_4081600 : Nat := 118140960795 + 4081600 * 2 ^ 59
def prefixEnd_4081600 : Nat := 4983230072969 + 3 ^ 40 * 4081600 * 2
def baseEnd_4081600 : Nat := 698607546463778651643023

theorem tailTrace_4081600 : CollatzResearch.WordTrace tailWord_4081600 prefixEnd_4081600 698607546463778651643023 := by
  unfold tailWord_4081600
  simp only [CollatzResearch.WordTrace]
  refine ⟨74434091006533878313797127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99245454675378504418396169 74434091006533878313797127)
  ·
    refine ⟨111651136509800817470695691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74434091006533878313797127 111651136509800817470695691)
    ·
      refine ⟨167476704764701226206043537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111651136509800817470695691 167476704764701226206043537)
      ·
        refine ⟨125607528573525919654532653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167476704764701226206043537 125607528573525919654532653)
        ·
          refine ⟨47102823215072219870449745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125607528573525919654532653 47102823215072219870449745)
          ·
            refine ⟨35327117411304164902837309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47102823215072219870449745 35327117411304164902837309)
            ·
              refine ⟨13247669029239061838563991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35327117411304164902837309 13247669029239061838563991)
              ·
                refine ⟨19871503543858592757845987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13247669029239061838563991 19871503543858592757845987)
                ·
                  refine ⟨29807255315787889136768981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19871503543858592757845987 29807255315787889136768981)
                  ·
                    refine ⟨698607546463778651643023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29807255315787889136768981 698607546463778651643023)
                    ·
                      rfl

theorem cell23_4081600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 1, 1, 7].length) (baseStart_4081600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4081600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4081600 prefixEnd_4081600 := by exact prefixLift 4081600
  have htrace : WordTrace (prefixWord ++ tailWord_4081600) baseStart_4081600 baseEnd_4081600 := by
    simpa [prefixWord, tailWord_4081600, baseEnd_4081600] using wordTrace_append hprefix tailTrace_4081600
  have hstable : (prefixWord ++ tailWord_4081600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4081600).length < 2 ^ (prefixWord ++ tailWord_4081600).sum := by decide
  have hdescent : baseEnd_4081600 < baseStart_4081600 := by decide
  rcases family_descends (prefixWord ++ tailWord_4081600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4081610 : List Nat := [3, 1, 2, 1, 2, 1, 2, 1, 3, 2, 5]
def baseStart_4081610 : Nat := 118140960795 + 4081610 * 2 ^ 59
def prefixEnd_4081610 : Nat := 4983230072969 + 3 ^ 40 * 4081610 * 2
def baseEnd_4081610 : Nat := 2095827774197880915804023

theorem tailTrace_4081610 : CollatzResearch.WordTrace tailWord_4081610 prefixEnd_4081610 2095827774197880915804023 := by
  unfold tailWord_4081610
  simp only [CollatzResearch.WordTrace]
  refine ⟨37217136685757882083864571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99245697828687685556972189 37217136685757882083864571)
  ·
    refine ⟨55825705028636823125796857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37217136685757882083864571 55825705028636823125796857)
    ·
      refine ⟨41869278771477617344347643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55825705028636823125796857 41869278771477617344347643)
      ·
        refine ⟨62803918157216426016521465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41869278771477617344347643 62803918157216426016521465)
        ·
          refine ⟨47102938617912319512391099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62803918157216426016521465 47102938617912319512391099)
          ·
            refine ⟨70654407926868479268586649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47102938617912319512391099 70654407926868479268586649)
            ·
              refine ⟨52990805945151359451439987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70654407926868479268586649 52990805945151359451439987)
              ·
                refine ⟨79486208917727039177159981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52990805945151359451439987 79486208917727039177159981)
                ·
                  refine ⟨29807328344147639691434993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79486208917727039177159981 29807328344147639691434993)
                  ·
                    refine ⟨22355496258110729768576245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29807328344147639691434993 22355496258110729768576245)
                    ·
                      refine ⟨2095827774197880915804023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22355496258110729768576245 2095827774197880915804023)
                      ·
                        rfl

theorem cell23_4081610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 1, 3, 2, 5].length) (baseStart_4081610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4081610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4081610 prefixEnd_4081610 := by exact prefixLift 4081610
  have htrace : WordTrace (prefixWord ++ tailWord_4081610) baseStart_4081610 baseEnd_4081610 := by
    simpa [prefixWord, tailWord_4081610, baseEnd_4081610] using wordTrace_append hprefix tailTrace_4081610
  have hstable : (prefixWord ++ tailWord_4081610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4081610).length < 2 ^ (prefixWord ++ tailWord_4081610).sum := by decide
  have hdescent : baseEnd_4081610 < baseStart_4081610 := by decide
  rcases family_descends (prefixWord ++ tailWord_4081610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4081647 : List Nat := [1, 1, 2, 1, 4, 2, 1, 4, 3, 4]
def baseStart_4081647 : Nat := 118140960795 + 4081647 * 2 ^ 59
def prefixEnd_4081647 : Nat := 4983230072969 + 3 ^ 40 * 4081647 * 2
def baseEnd_4081647 : Nat := 698615590994032423680451

theorem tailTrace_4081647 : CollatzResearch.WordTrace tailWord_4081647 prefixEnd_4081647 698615590994032423680451 := by
  unfold tailWord_4081647
  simp only [CollatzResearch.WordTrace]
  refine ⟨148869896243897483654555195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99246597495931655769703463 148869896243897483654555195)
  ·
    refine ⟨223304844365846225481832793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148869896243897483654555195 223304844365846225481832793)
    ·
      refine ⟨167478633274384669111374595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223304844365846225481832793 167478633274384669111374595)
      ·
        refine ⟨251217949911577003667061893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167478633274384669111374595 251217949911577003667061893)
        ·
          refine ⟨47103365608420688187574105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 251217949911577003667061893 47103365608420688187574105)
          ·
            refine ⟨35327524206315516140680579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47103365608420688187574105 35327524206315516140680579)
            ·
              refine ⟨52991286309473274211020869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35327524206315516140680579 52991286309473274211020869)
              ·
                refine ⟨9935866183026238914566413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52991286309473274211020869 9935866183026238914566413)
                ·
                  refine ⟨3725949818634839592962405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9935866183026238914566413 3725949818634839592962405)
                  ·
                    refine ⟨698615590994032423680451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3725949818634839592962405 698615590994032423680451)
                    ·
                      rfl

theorem cell23_4081647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 4, 3, 4].length) (baseStart_4081647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4081647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4081647 prefixEnd_4081647 := by exact prefixLift 4081647
  have htrace : WordTrace (prefixWord ++ tailWord_4081647) baseStart_4081647 baseEnd_4081647 := by
    simpa [prefixWord, tailWord_4081647, baseEnd_4081647] using wordTrace_append hprefix tailTrace_4081647
  have hstable : (prefixWord ++ tailWord_4081647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4081647).length < 2 ^ (prefixWord ++ tailWord_4081647).sum := by decide
  have hdescent : baseEnd_4081647 < baseStart_4081647 := by decide
  rcases family_descends (prefixWord ++ tailWord_4081647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4081657 : List Nat := [1, 2, 1, 3, 1, 4, 2, 1, 1, 4, 3]
def baseStart_4081657 : Nat := 118140960795 + 4081657 * 2 ^ 59
def prefixEnd_4081657 : Nat := 4983230072969 + 3 ^ 40 * 4081657 * 2
def baseEnd_4081657 : Nat := 2095851907788642231916307

theorem tailTrace_4081657 : CollatzResearch.WordTrace tailWord_4081657 prefixEnd_4081657 2095851907788642231916307 := by
  unfold tailWord_4081657
  simp only [CollatzResearch.WordTrace]
  refine ⟨148870260973861255362419225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99246840649240836908279483 148870260973861255362419225)
  ·
    refine ⟨111652695730395941521814419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148870260973861255362419225 111652695730395941521814419)
    ·
      refine ⟨167479043595593912282721629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111652695730395941521814419 167479043595593912282721629)
      ·
        refine ⟨62804641348347717106020611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167479043595593912282721629 62804641348347717106020611)
        ·
          refine ⟨94206962022521575659030917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62804641348347717106020611 94206962022521575659030917)
          ·
            refine ⟨17663805379222795436068297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94206962022521575659030917 17663805379222795436068297)
            ·
              refine ⟨13247854034417096577051223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17663805379222795436068297 13247854034417096577051223)
              ·
                refine ⟨19871781051625644865576835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13247854034417096577051223 19871781051625644865576835)
                ·
                  refine ⟨29807671577438467298365253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19871781051625644865576835 29807671577438467298365253)
                  ·
                    refine ⟨5588938420769712618443485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29807671577438467298365253 5588938420769712618443485)
                    ·
                      refine ⟨2095851907788642231916307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5588938420769712618443485 2095851907788642231916307)
                      ·
                        rfl

theorem cell23_4081657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 1, 1, 4, 3].length) (baseStart_4081657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4081657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4081657 prefixEnd_4081657 := by exact prefixLift 4081657
  have htrace : WordTrace (prefixWord ++ tailWord_4081657) baseStart_4081657 baseEnd_4081657 := by
    simpa [prefixWord, tailWord_4081657, baseEnd_4081657] using wordTrace_append hprefix tailTrace_4081657
  have hstable : (prefixWord ++ tailWord_4081657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4081657).length < 2 ^ (prefixWord ++ tailWord_4081657).sum := by decide
  have hdescent : baseEnd_4081657 < baseStart_4081657 := by decide
  rcases family_descends (prefixWord ++ tailWord_4081657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4081660 : List Nat := [2, 2, 2, 1, 2, 2, 1, 1, 10]
def baseStart_4081660 : Nat := 118140960795 + 4081660 * 2 ^ 59
def prefixEnd_4081660 : Nat := 4983230072969 + 3 ^ 40 * 4081660 * 2
def baseEnd_4081660 : Nat := 232872605358956191130977

theorem tailTrace_4081660 : CollatzResearch.WordTrace tailWord_4081660 prefixEnd_4081660 232872605358956191130977 := by
  unfold tailWord_4081660
  simp only [CollatzResearch.WordTrace]
  refine ⟨74435185196425193437389217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99246913595233591249852289 74435185196425193437389217)
  ·
    refine ⟨55826388897318895078041913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74435185196425193437389217 55826388897318895078041913)
    ·
      refine ⟨41869791672989171308531435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55826388897318895078041913 41869791672989171308531435)
      ·
        refine ⟨62804687509483756962797153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41869791672989171308531435 62804687509483756962797153)
        ·
          refine ⟨47103515632112817722097865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62804687509483756962797153 47103515632112817722097865)
          ·
            refine ⟨35327636724084613291573399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47103515632112817722097865 35327636724084613291573399)
            ·
              refine ⟨52991455086126919937360099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35327636724084613291573399 52991455086126919937360099)
              ·
                refine ⟨79487182629190379906040149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52991455086126919937360099 79487182629190379906040149)
                ·
                  refine ⟨232872605358956191130977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 79487182629190379906040149 232872605358956191130977)
                  ·
                    rfl

theorem cell23_4081660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 1, 10].length) (baseStart_4081660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4081660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4081660 prefixEnd_4081660 := by exact prefixLift 4081660
  have htrace : WordTrace (prefixWord ++ tailWord_4081660) baseStart_4081660 baseEnd_4081660 := by
    simpa [prefixWord, tailWord_4081660, baseEnd_4081660] using wordTrace_append hprefix tailTrace_4081660
  have hstable : (prefixWord ++ tailWord_4081660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4081660).length < 2 ^ (prefixWord ++ tailWord_4081660).sum := by decide
  have hdescent : baseEnd_4081660 < baseStart_4081660 := by decide
  rcases family_descends (prefixWord ++ tailWord_4081660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4081664 : List Nat := [2, 1, 1, 2, 1, 1, 1, 9, 1, 4]
def baseStart_4081664 : Nat := 118140960795 + 4081664 * 2 ^ 59
def prefixEnd_4081664 : Nat := 4983230072969 + 3 ^ 40 * 4081664 * 2
def baseEnd_4081664 : Nat := 698618500717741234842925

theorem tailTrace_4081664 : CollatzResearch.WordTrace tailWord_4081664 prefixEnd_4081664 698618500717741234842925 := by
  unfold tailWord_4081664
  simp only [CollatzResearch.WordTrace]
  refine ⟨74435258142417947778962023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99247010856557263705282697 74435258142417947778962023)
  ·
    refine ⟨111652887213626921668443035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74435258142417947778962023 111652887213626921668443035)
    ·
      refine ⟨167479330820440382502664553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111652887213626921668443035 167479330820440382502664553)
      ·
        refine ⟨125609498115330286876998415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167479330820440382502664553 125609498115330286876998415)
        ·
          refine ⟨188414247172995430315497623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125609498115330286876998415 188414247172995430315497623)
          ·
            refine ⟨282621370759493145473246435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188414247172995430315497623 282621370759493145473246435)
            ·
              refine ⟨423932056139239718209869653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 282621370759493145473246435 423932056139239718209869653)
              ·
                refine ⟨2483976891440857723885955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 423932056139239718209869653 2483976891440857723885955)
                ·
                  refine ⟨3725965337161286585828933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2483976891440857723885955 3725965337161286585828933)
                  ·
                    refine ⟨698618500717741234842925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3725965337161286585828933 698618500717741234842925)
                    ·
                      rfl

theorem cell23_4081664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 9, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 9, 1, 4].length) (baseStart_4081664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4081664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4081664 prefixEnd_4081664 := by exact prefixLift 4081664
  have htrace : WordTrace (prefixWord ++ tailWord_4081664) baseStart_4081664 baseEnd_4081664 := by
    simpa [prefixWord, tailWord_4081664, baseEnd_4081664] using wordTrace_append hprefix tailTrace_4081664
  have hstable : (prefixWord ++ tailWord_4081664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4081664).length < 2 ^ (prefixWord ++ tailWord_4081664).sum := by decide
  have hdescent : baseEnd_4081664 < baseStart_4081664 := by decide
  rcases family_descends (prefixWord ++ tailWord_4081664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4081707 : List Nat := [1, 1, 1, 1, 2, 1, 4, 6, 1, 5]
def baseStart_4081707 : Nat := 118140960795 + 4081707 * 2 ^ 59
def prefixEnd_4081707 : Nat := 4983230072969 + 3 ^ 40 * 4081707 * 2
def baseEnd_4081707 : Nat := 698625860607122345430359

theorem tailTrace_4081707 : CollatzResearch.WordTrace tailWord_4081707 prefixEnd_4081707 698625860607122345430359 := by
  unfold tailWord_4081707
  simp only [CollatzResearch.WordTrace]
  refine ⟨148872084623680113901739375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99248056415786742601159583 148872084623680113901739375)
  ·
    refine ⟨223308126935520170852609063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148872084623680113901739375 223308126935520170852609063)
    ·
      refine ⟨334962190403280256278913595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223308126935520170852609063 334962190403280256278913595)
      ·
        refine ⟨502443285604920384418370393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334962190403280256278913595 502443285604920384418370393)
        ·
          refine ⟨376832464203690288313777795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 502443285604920384418370393 376832464203690288313777795)
          ·
            refine ⟨565248696305535432470666693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 376832464203690288313777795 565248696305535432470666693)
            ·
              refine ⟨105984130557287893588250005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 565248696305535432470666693 105984130557287893588250005)
              ·
                refine ⟨4968006119872870011949219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 105984130557287893588250005 4968006119872870011949219)
                ·
                  refine ⟨7452009179809305017923829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4968006119872870011949219 7452009179809305017923829)
                  ·
                    refine ⟨698625860607122345430359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7452009179809305017923829 698625860607122345430359)
                    ·
                      rfl

theorem cell23_4081707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 6, 1, 5].length) (baseStart_4081707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4081707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4081707 prefixEnd_4081707 := by exact prefixLift 4081707
  have htrace : WordTrace (prefixWord ++ tailWord_4081707) baseStart_4081707 baseEnd_4081707 := by
    simpa [prefixWord, tailWord_4081707, baseEnd_4081707] using wordTrace_append hprefix tailTrace_4081707
  have hstable : (prefixWord ++ tailWord_4081707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4081707).length < 2 ^ (prefixWord ++ tailWord_4081707).sum := by decide
  have hdescent : baseEnd_4081707 < baseStart_4081707 := by decide
  rcases family_descends (prefixWord ++ tailWord_4081707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4081754 : List Nat := [3, 1, 1, 2, 1, 1, 3, 5, 2, 4]
def baseStart_4081754 : Nat := 118140960795 + 4081754 * 2 ^ 59
def prefixEnd_4081754 : Nat := 4983230072969 + 3 ^ 40 * 4081754 * 2
def baseEnd_4081754 : Nat := 698633905137376117467787

theorem tailTrace_4081754 : CollatzResearch.WordTrace tailWord_4081754 prefixEnd_4081754 698633905137376117467787 := by
  unfold tailWord_4081754
  simp only [CollatzResearch.WordTrace]
  refine ⟨37218449713627460232175079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99249199236339893952466877 37218449713627460232175079)
  ·
    refine ⟨55827674570441190348262619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37218449713627460232175079 55827674570441190348262619)
    ·
      refine ⟨83741511855661785522393929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55827674570441190348262619 83741511855661785522393929)
      ·
        refine ⟨62806133891746339141795447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83741511855661785522393929 62806133891746339141795447)
        ·
          refine ⟨94209200837619508712693171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62806133891746339141795447 94209200837619508712693171)
          ·
            refine ⟨141313801256429263069039757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94209200837619508712693171 141313801256429263069039757)
            ·
              refine ⟨52992675471160973650889909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141313801256429263069039757 52992675471160973650889909)
              ·
                refine ⟨4968063325421341279770929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52992675471160973650889909 4968063325421341279770929)
                ·
                  refine ⟨3726047494066005959828197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4968063325421341279770929 3726047494066005959828197)
                  ·
                    refine ⟨698633905137376117467787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3726047494066005959828197 698633905137376117467787)
                    ·
                      rfl

theorem cell23_4081754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 5, 2, 4].length) (baseStart_4081754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4081754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4081754 prefixEnd_4081754 := by exact prefixLift 4081754
  have htrace : WordTrace (prefixWord ++ tailWord_4081754) baseStart_4081754 baseEnd_4081754 := by
    simpa [prefixWord, tailWord_4081754, baseEnd_4081754] using wordTrace_append hprefix tailTrace_4081754
  have hstable : (prefixWord ++ tailWord_4081754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4081754).length < 2 ^ (prefixWord ++ tailWord_4081754).sum := by decide
  have hdescent : baseEnd_4081754 < baseStart_4081754 := by decide
  rcases family_descends (prefixWord ++ tailWord_4081754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4081764 : List Nat := [2, 3, 1, 1, 2, 1, 4, 1, 3, 2, 3]
def baseStart_4081764 : Nat := 118140960795 + 4081764 * 2 ^ 59
def prefixEnd_4081764 : Nat := 4983230072969 + 3 ^ 40 * 4081764 * 2
def baseEnd_4081764 : Nat := 2095906850218673313278315

theorem tailTrace_4081764 : CollatzResearch.WordTrace tailWord_4081764 prefixEnd_4081764 2095906850218673313278315 := by
  unfold tailWord_4081764
  simp only [CollatzResearch.WordTrace]
  refine ⟨74437081792236806318282173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99249442389649075091042897 74437081792236806318282173)
  ·
    refine ⟨27913905672088802369355815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74437081792236806318282173 27913905672088802369355815)
    ·
      refine ⟨41870858508133203554033723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27913905672088802369355815 41870858508133203554033723)
      ·
        refine ⟨62806287762199805331050585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41870858508133203554033723 62806287762199805331050585)
        ·
          refine ⟨47104715821649853998287939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62806287762199805331050585 47104715821649853998287939)
          ·
            refine ⟨70657073732474780997431909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47104715821649853998287939 70657073732474780997431909)
            ·
              refine ⟨13248201324839021437018483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70657073732474780997431909 13248201324839021437018483)
              ·
                refine ⟨19872301987258532155527725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13248201324839021437018483 19872301987258532155527725)
                ·
                  refine ⟨7452113245221949558322897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19872301987258532155527725 7452113245221949558322897)
                  ·
                    refine ⟨5589084933916462168742173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7452113245221949558322897 5589084933916462168742173)
                    ·
                      refine ⟨2095906850218673313278315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5589084933916462168742173 2095906850218673313278315)
                      ·
                        rfl

theorem cell23_4081764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 1, 3, 2, 3].length) (baseStart_4081764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4081764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4081764 prefixEnd_4081764 := by exact prefixLift 4081764
  have htrace : WordTrace (prefixWord ++ tailWord_4081764) baseStart_4081764 baseEnd_4081764 := by
    simpa [prefixWord, tailWord_4081764, baseEnd_4081764] using wordTrace_append hprefix tailTrace_4081764
  have hstable : (prefixWord ++ tailWord_4081764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4081764).length < 2 ^ (prefixWord ++ tailWord_4081764).sum := by decide
  have hdescent : baseEnd_4081764 < baseStart_4081764 := by decide
  rcases family_descends (prefixWord ++ tailWord_4081764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4081774 : List Nat := [4, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4]
def baseStart_4081774 : Nat := 118140960795 + 4081774 * 2 ^ 59
def prefixEnd_4081774 : Nat := 4983230072969 + 3 ^ 40 * 4081774 * 2
def baseEnd_4081774 : Nat := 2095911985025218274153269

theorem tailTrace_4081774 : CollatzResearch.WordTrace tailWord_4081774 prefixEnd_4081774 2095911985025218274153269 := by
  unfold tailWord_4081774
  simp only [CollatzResearch.WordTrace]
  refine ⟨18609316039304673043053547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99249685542958256229618917 18609316039304673043053547)
  ·
    refine ⟨27913974058957009564580321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18609316039304673043053547 27913974058957009564580321)
    ·
      refine ⟨20935480544217757173435241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27913974058957009564580321 20935480544217757173435241)
      ·
        refine ⟨15701610408163317880076431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20935480544217757173435241 15701610408163317880076431)
        ·
          refine ⟨23552415612244976820114647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15701610408163317880076431 23552415612244976820114647)
          ·
            refine ⟨35328623418367465230171971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23552415612244976820114647 35328623418367465230171971)
            ·
              refine ⟨52992935127551197845257957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35328623418367465230171971 52992935127551197845257957)
              ·
                refine ⟨9936175336415849595985867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52992935127551197845257957 9936175336415849595985867)
                ·
                  refine ⟨14904263004623774393978801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9936175336415849595985867 14904263004623774393978801)
                  ·
                    refine ⟨11178197253467830795484101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14904263004623774393978801 11178197253467830795484101)
                    ·
                      refine ⟨2095911985025218274153269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11178197253467830795484101 2095911985025218274153269)
                      ·
                        rfl

theorem cell23_4081774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_4081774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4081774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4081774 prefixEnd_4081774 := by exact prefixLift 4081774
  have htrace : WordTrace (prefixWord ++ tailWord_4081774) baseStart_4081774 baseEnd_4081774 := by
    simpa [prefixWord, tailWord_4081774, baseEnd_4081774] using wordTrace_append hprefix tailTrace_4081774
  have hstable : (prefixWord ++ tailWord_4081774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4081774).length < 2 ^ (prefixWord ++ tailWord_4081774).sum := by decide
  have hdescent : baseEnd_4081774 < baseStart_4081774 := by decide
  rcases family_descends (prefixWord ++ tailWord_4081774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4081778 : List Nat := [3, 2, 1, 2, 2, 4, 2, 1, 1, 1, 4]
def baseStart_4081778 : Nat := 118140960795 + 4081778 * 2 ^ 59
def prefixEnd_4081778 : Nat := 4983230072969 + 3 ^ 40 * 4081778 * 2
def baseEnd_4081778 : Nat := 2095914038947836258503251

theorem tailTrace_4081778 : CollatzResearch.WordTrace tailWord_4081778 prefixEnd_4081778 2095914038947836258503251 := by
  unfold tailWord_4081778
  simp only [CollatzResearch.WordTrace]
  refine ⟨37218668551605723256893497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99249782804281928685049325 37218668551605723256893497)
  ·
    refine ⟨27914001413704292442670123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37218668551605723256893497 27914001413704292442670123)
    ·
      refine ⟨41871002120556438664005185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27914001413704292442670123 41871002120556438664005185)
      ·
        refine ⟨31403251590417328998003889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41871002120556438664005185 31403251590417328998003889)
        ·
          refine ⟨23552438692812996748502917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31403251590417328998003889 23552438692812996748502917)
          ·
            refine ⟨4416082254902436890344297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23552438692812996748502917 4416082254902436890344297)
            ·
              refine ⟨3312061691176827667758223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4416082254902436890344297 3312061691176827667758223)
              ·
                refine ⟨4968092536765241501637335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3312061691176827667758223 4968092536765241501637335)
                ·
                  refine ⟨7452138805147862252456003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4968092536765241501637335 7452138805147862252456003)
                  ·
                    refine ⟨11178208207721793378684005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7452138805147862252456003 11178208207721793378684005)
                    ·
                      refine ⟨2095914038947836258503251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11178208207721793378684005 2095914038947836258503251)
                      ·
                        rfl

theorem cell23_4081778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 2, 1, 1, 1, 4].length) (baseStart_4081778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4081778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4081778 prefixEnd_4081778 := by exact prefixLift 4081778
  have htrace : WordTrace (prefixWord ++ tailWord_4081778) baseStart_4081778 baseEnd_4081778 := by
    simpa [prefixWord, tailWord_4081778, baseEnd_4081778] using wordTrace_append hprefix tailTrace_4081778
  have hstable : (prefixWord ++ tailWord_4081778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4081778).length < 2 ^ (prefixWord ++ tailWord_4081778).sum := by decide
  have hdescent : baseEnd_4081778 < baseStart_4081778 := by decide
  rcases family_descends (prefixWord ++ tailWord_4081778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4081817 : List Nat := [1, 2, 1, 2, 1, 2, 1, 4, 2, 3, 4]
def baseStart_4081817 : Nat := 118140960795 + 4081817 * 2 ^ 59
def prefixEnd_4081817 : Nat := 4983230072969 + 3 ^ 40 * 4081817 * 2
def baseEnd_4081817 : Nat := 2095934064693361605915571

theorem tailTrace_4081817 : CollatzResearch.WordTrace tailWord_4081817 prefixEnd_4081817 2095934064693361605915571 := by
  unfold tailWord_4081817
  simp only [CollatzResearch.WordTrace]
  refine ⟨148876096653281602688243705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99250731102187735125495803 148876096653281602688243705)
  ·
    refine ⟨111657072489961202016182779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148876096653281602688243705 111657072489961202016182779)
    ·
      refine ⟨167485608734941803024274169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111657072489961202016182779 167485608734941803024274169)
      ·
        refine ⟨125614206551206352268205627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167485608734941803024274169 125614206551206352268205627)
        ·
          refine ⟨188421309826809528402308441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125614206551206352268205627 188421309826809528402308441)
          ·
            refine ⟨141315982370107146301731331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188421309826809528402308441 141315982370107146301731331)
            ·
              refine ⟨211973973555160719452596997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141315982370107146301731331 211973973555160719452596997)
              ·
                refine ⟨39745120041592634897361937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 211973973555160719452596997 39745120041592634897361937)
                ·
                  refine ⟨29808840031194476173021453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39745120041592634897361937 29808840031194476173021453)
                  ·
                    refine ⟨11178315011697928564883045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29808840031194476173021453 11178315011697928564883045)
                    ·
                      refine ⟨2095934064693361605915571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11178315011697928564883045 2095934064693361605915571)
                      ·
                        rfl

theorem cell23_4081817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 4, 2, 3, 4].length) (baseStart_4081817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4081817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4081817 prefixEnd_4081817 := by exact prefixLift 4081817
  have htrace : WordTrace (prefixWord ++ tailWord_4081817) baseStart_4081817 baseEnd_4081817 := by
    simpa [prefixWord, tailWord_4081817, baseEnd_4081817] using wordTrace_append hprefix tailTrace_4081817
  have hstable : (prefixWord ++ tailWord_4081817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4081817).length < 2 ^ (prefixWord ++ tailWord_4081817).sum := by decide
  have hdescent : baseEnd_4081817 < baseStart_4081817 := by decide
  rcases family_descends (prefixWord ++ tailWord_4081817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4081818 : List Nat := [3, 1, 1, 5, 3, 1, 2, 7]
def baseStart_4081818 : Nat := 118140960795 + 4081818 * 2 ^ 59
def prefixEnd_4081818 : Nat := 4983230072969 + 3 ^ 40 * 4081818 * 2
def baseEnd_4081818 : Nat := 77627206599037633407521

theorem tailTrace_4081818 : CollatzResearch.WordTrace tailWord_4081818 prefixEnd_4081818 77627206599037633407521 := by
  unfold tailWord_4081818
  simp only [CollatzResearch.WordTrace]
  refine ⟨37219033281569494964757527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99250755417518653239353405 37219033281569494964757527)
  ·
    refine ⟨55828549922354242447136291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37219033281569494964757527 55828549922354242447136291)
    ·
      refine ⟨83742824883531363670704437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55828549922354242447136291 83742824883531363670704437)
      ·
        refine ⟨7850889832831065344128541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 83742824883531363670704437 7850889832831065344128541)
        ·
          refine ⟨2944083687311649504048203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7850889832831065344128541 2944083687311649504048203)
          ·
            refine ⟨4416125530967474256072305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2944083687311649504048203 4416125530967474256072305)
            ·
              refine ⟨3312094148225605692054229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4416125530967474256072305 3312094148225605692054229)
              ·
                refine ⟨77627206599037633407521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3312094148225605692054229 77627206599037633407521)
                ·
                  rfl

theorem cell23_4081818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 2, 7].length) (baseStart_4081818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4081818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4081818 prefixEnd_4081818 := by exact prefixLift 4081818
  have htrace : WordTrace (prefixWord ++ tailWord_4081818) baseStart_4081818 baseEnd_4081818 := by
    simpa [prefixWord, tailWord_4081818, baseEnd_4081818] using wordTrace_append hprefix tailTrace_4081818
  have hstable : (prefixWord ++ tailWord_4081818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4081818).length < 2 ^ (prefixWord ++ tailWord_4081818).sum := by decide
  have hdescent : baseEnd_4081818 < baseStart_4081818 := by decide
  rcases family_descends (prefixWord ++ tailWord_4081818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4081851 : List Nat := [1, 1, 1, 1, 1, 2, 5, 3, 4, 2, 2]
def baseStart_4081851 : Nat := 118140960795 + 4081851 * 2 ^ 59
def prefixEnd_4081851 : Nat := 4983230072969 + 3 ^ 40 * 4081851 * 2
def baseEnd_4081851 : Nat := 2095951523035614472890415

theorem tailTrace_4081851 : CollatzResearch.WordTrace tailWord_4081851 prefixEnd_4081851 2095951523035614472890415 := by
  unfold tailWord_4081851
  simp only [CollatzResearch.WordTrace]
  refine ⟨148877336735158426494981407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99251557823438950996654271 148877336735158426494981407)
  ·
    refine ⟨223316005102737639742472111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148877336735158426494981407 223316005102737639742472111)
    ·
      refine ⟨334974007654106459613708167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223316005102737639742472111 334974007654106459613708167)
      ·
        refine ⟨502461011481159689420562251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334974007654106459613708167 502461011481159689420562251)
        ·
          refine ⟨753691517221739534130843377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 502461011481159689420562251 753691517221739534130843377)
          ·
            refine ⟨565268637916304650598132533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 753691517221739534130843377 565268637916304650598132533)
            ·
              refine ⟨52993934804653560993574925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 565268637916304650598132533 52993934804653560993574925)
              ·
                refine ⟨19872725551745085372590597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52993934804653560993574925 19872725551745085372590597)
                ·
                  refine ⟨3726136040952203507360737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19872725551745085372590597 3726136040952203507360737)
                  ·
                    refine ⟨2794602030714152630520553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3726136040952203507360737 2794602030714152630520553)
                    ·
                      refine ⟨2095951523035614472890415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2794602030714152630520553 2095951523035614472890415)
                      ·
                        rfl

theorem cell23_4081851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 3, 4, 2, 2].length) (baseStart_4081851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4081851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4081851 prefixEnd_4081851 := by exact prefixLift 4081851
  have htrace : WordTrace (prefixWord ++ tailWord_4081851) baseStart_4081851 baseEnd_4081851 := by
    simpa [prefixWord, tailWord_4081851, baseEnd_4081851] using wordTrace_append hprefix tailTrace_4081851
  have hstable : (prefixWord ++ tailWord_4081851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4081851).length < 2 ^ (prefixWord ++ tailWord_4081851).sum := by decide
  have hdescent : baseEnd_4081851 < baseStart_4081851 := by decide
  rcases family_descends (prefixWord ++ tailWord_4081851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4081897 : List Nat := [1, 2, 1, 1, 1, 2, 2, 2, 3, 1, 7]
def baseStart_4081897 : Nat := 118140960795 + 4081897 * 2 ^ 59
def prefixEnd_4081897 : Nat := 4983230072969 + 3 ^ 40 * 4081897 * 2
def baseEnd_4081897 : Nat := 2095975143145721292915203

theorem tailTrace_4081897 : CollatzResearch.WordTrace tailWord_4081897 prefixEnd_4081897 2095975143145721292915203 := by
  unfold tailWord_4081897
  simp only [CollatzResearch.WordTrace]
  refine ⟨148879014492991776351155945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99252676328661184234103963 148879014492991776351155945)
  ·
    refine ⟨111659260869743832263366959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148879014492991776351155945 111659260869743832263366959)
    ·
      refine ⟨167488891304615748395050439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111659260869743832263366959 167488891304615748395050439)
      ·
        refine ⟨251233336956923622592575659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167488891304615748395050439 251233336956923622592575659)
        ·
          refine ⟨376850005435385433888863489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251233336956923622592575659 376850005435385433888863489)
          ·
            refine ⟨282637504076539075416647617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 376850005435385433888863489 282637504076539075416647617)
            ·
              refine ⟨211978128057404306562485713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 282637504076539075416647617 211978128057404306562485713)
              ·
                refine ⟨158983596043053229921864285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 211978128057404306562485713 158983596043053229921864285)
                ·
                  refine ⟨59618848516144961220699107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 158983596043053229921864285 59618848516144961220699107)
                  ·
                    refine ⟨89428272774217441831048661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59618848516144961220699107 89428272774217441831048661)
                    ·
                      refine ⟨2095975143145721292915203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 89428272774217441831048661 2095975143145721292915203)
                      ·
                        rfl

theorem cell23_4081897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 3, 1, 7].length) (baseStart_4081897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4081897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4081897 prefixEnd_4081897 := by exact prefixLift 4081897
  have htrace : WordTrace (prefixWord ++ tailWord_4081897) baseStart_4081897 baseEnd_4081897 := by
    simpa [prefixWord, tailWord_4081897, baseEnd_4081897] using wordTrace_append hprefix tailTrace_4081897
  have hstable : (prefixWord ++ tailWord_4081897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4081897).length < 2 ^ (prefixWord ++ tailWord_4081897).sum := by decide
  have hdescent : baseEnd_4081897 < baseStart_4081897 := by decide
  rcases family_descends (prefixWord ++ tailWord_4081897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4081914 : List Nat := [3, 1, 1, 1, 1, 5, 2, 1, 1, 2, 5]
def baseStart_4081914 : Nat := 118140960795 + 4081914 * 2 ^ 59
def prefixEnd_4081914 : Nat := 4983230072969 + 3 ^ 40 * 4081914 * 2
def baseEnd_4081914 : Nat := 2095983872316847726402625

theorem tailTrace_4081914 : CollatzResearch.WordTrace tailWord_4081914 prefixEnd_4081914 2095983872316847726402625 := by
  unfold tailWord_4081914
  simp only [CollatzResearch.WordTrace]
  refine ⟨37219908633482547063631199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99253089689286792169683197 37219908633482547063631199)
  ·
    refine ⟨55829862950223820595446799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37219908633482547063631199 55829862950223820595446799)
    ·
      refine ⟨83744794425335730893170199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55829862950223820595446799 83744794425335730893170199)
      ·
        refine ⟨125617191638003596339755299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83744794425335730893170199 125617191638003596339755299)
        ·
          refine ⟨188425787457005394509632949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125617191638003596339755299 188425787457005394509632949)
          ·
            refine ⟨17664917574094255735278089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 188425787457005394509632949 17664917574094255735278089)
            ·
              refine ⟨13248688180570691801458567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17664917574094255735278089 13248688180570691801458567)
              ·
                refine ⟨19873032270856037702187851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13248688180570691801458567 19873032270856037702187851)
                ·
                  refine ⟨29809548406284056553281777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19873032270856037702187851 29809548406284056553281777)
                  ·
                    refine ⟨22357161304713042414961333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29809548406284056553281777 22357161304713042414961333)
                    ·
                      refine ⟨2095983872316847726402625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22357161304713042414961333 2095983872316847726402625)
                      ·
                        rfl

theorem cell23_4081914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 1, 1, 2, 5].length) (baseStart_4081914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4081914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4081914 prefixEnd_4081914 := by exact prefixLift 4081914
  have htrace : WordTrace (prefixWord ++ tailWord_4081914) baseStart_4081914 baseEnd_4081914 := by
    simpa [prefixWord, tailWord_4081914, baseEnd_4081914] using wordTrace_append hprefix tailTrace_4081914
  have hstable : (prefixWord ++ tailWord_4081914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4081914).length < 2 ^ (prefixWord ++ tailWord_4081914).sum := by decide
  have hdescent : baseEnd_4081914 < baseStart_4081914 := by decide
  rcases family_descends (prefixWord ++ tailWord_4081914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4081941 : List Nat := [1, 3, 2, 1, 2, 1, 5, 1, 2, 1, 4]
def baseStart_4081941 : Nat := 118140960795 + 4081941 * 2 ^ 59
def prefixEnd_4081941 : Nat := 4983230072969 + 3 ^ 40 * 4081941 * 2
def baseEnd_4081941 : Nat := 2095997736294519120765001

theorem tailTrace_4081941 : CollatzResearch.WordTrace tailWord_4081941 prefixEnd_4081941 2095997736294519120765001 := by
  unfold tailWord_4081941
  simp only [CollatzResearch.WordTrace]
  refine ⟨148880619304832371865757677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99253746203221581243838451 148880619304832371865757677)
  ·
    refine ⟨55830232239312139449659129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148880619304832371865757677 55830232239312139449659129)
    ·
      refine ⟨41872674179484104587244347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55830232239312139449659129 41872674179484104587244347)
      ·
        refine ⟨62809011269226156880866521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41872674179484104587244347 62809011269226156880866521)
        ·
          refine ⟨47106758451919617660649891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62809011269226156880866521 47106758451919617660649891)
          ·
            refine ⟨70660137677879426490974837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47106758451919617660649891 70660137677879426490974837)
            ·
              refine ⟨6624387907301196233528891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70660137677879426490974837 6624387907301196233528891)
              ·
                refine ⟨9936581860951794350293337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6624387907301196233528891 9936581860951794350293337)
                ·
                  refine ⟨7452436395713845762720003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9936581860951794350293337 7452436395713845762720003)
                  ·
                    refine ⟨11178654593570768644080005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7452436395713845762720003 11178654593570768644080005)
                    ·
                      refine ⟨2095997736294519120765001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11178654593570768644080005 2095997736294519120765001)
                      ·
                        rfl

theorem cell23_4081941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 5, 1, 2, 1, 4].length) (baseStart_4081941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4081941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4081941 prefixEnd_4081941 := by exact prefixLift 4081941
  have htrace : WordTrace (prefixWord ++ tailWord_4081941) baseStart_4081941 baseEnd_4081941 := by
    simpa [prefixWord, tailWord_4081941, baseEnd_4081941] using wordTrace_append hprefix tailTrace_4081941
  have hstable : (prefixWord ++ tailWord_4081941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4081941).length < 2 ^ (prefixWord ++ tailWord_4081941).sum := by decide
  have hdescent : baseEnd_4081941 < baseStart_4081941 := by decide
  rcases family_descends (prefixWord ++ tailWord_4081941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4082031 : List Nat := [1, 1, 2, 1, 3, 1, 2, 2, 2, 6, 2]
def baseStart_4082031 : Nat := 118140960795 + 4082031 * 2 ^ 59
def prefixEnd_4082031 : Nat := 4983230072969 + 3 ^ 40 * 4082031 * 2
def baseEnd_4082031 : Nat := 2096043949553423768639587

theorem tailTrace_4082031 : CollatzResearch.WordTrace tailWord_4082031 prefixEnd_4082031 2096043949553423768639587 := by
  unfold tailWord_4082031
  simp only [CollatzResearch.WordTrace]
  refine ⟨148883901874506317236533947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99255934583004211491022631 148883901874506317236533947)
  ·
    refine ⟨223325852811759475854800921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148883901874506317236533947 223325852811759475854800921)
    ·
      refine ⟨167494389608819606891100691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223325852811759475854800921 167494389608819606891100691)
      ·
        refine ⟨251241584413229410336651037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167494389608819606891100691 251241584413229410336651037)
        ·
          refine ⟨94215594154961028876244139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 251241584413229410336651037 94215594154961028876244139)
          ·
            refine ⟨141323391232441543314366209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94215594154961028876244139 141323391232441543314366209)
            ·
              refine ⟨105992543424331157485774657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141323391232441543314366209 105992543424331157485774657)
              ·
                refine ⟨79494407568248368114330993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105992543424331157485774657 79494407568248368114330993)
                ·
                  refine ⟨59620805676186276085748245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79494407568248368114330993 59620805676186276085748245)
                  ·
                    refine ⟨2794725266071231691519449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 59620805676186276085748245 2794725266071231691519449)
                    ·
                      refine ⟨2096043949553423768639587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2794725266071231691519449 2096043949553423768639587)
                      ·
                        rfl

theorem cell23_4082031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 2, 2, 6, 2].length) (baseStart_4082031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4082031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4082031 prefixEnd_4082031 := by exact prefixLift 4082031
  have htrace : WordTrace (prefixWord ++ tailWord_4082031) baseStart_4082031 baseEnd_4082031 := by
    simpa [prefixWord, tailWord_4082031, baseEnd_4082031] using wordTrace_append hprefix tailTrace_4082031
  have hstable : (prefixWord ++ tailWord_4082031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4082031).length < 2 ^ (prefixWord ++ tailWord_4082031).sum := by decide
  have hdescent : baseEnd_4082031 < baseStart_4082031 := by decide
  rcases family_descends (prefixWord ++ tailWord_4082031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4082070 : List Nat := [5, 3, 1, 2, 2, 1, 2, 2, 1, 4]
def baseStart_4082070 : Nat := 118140960795 + 4082070 * 2 ^ 59
def prefixEnd_4082070 : Nat := 4983230072969 + 3 ^ 40 * 4082070 * 2
def baseEnd_4082070 : Nat := 698687991766316372017303

theorem tailTrace_4082070 : CollatzResearch.WordTrace tailWord_4082070 prefixEnd_4082070 698687991766316372017303 := by
  unfold tailWord_4082070
  simp only [CollatzResearch.WordTrace]
  refine ⟨9305332770085314181075229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 99256882880910017931469109 9305332770085314181075229)
  ·
    refine ⟨3489499788781992817903211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9305332770085314181075229 3489499788781992817903211)
    ·
      refine ⟨5234249683172989226854817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3489499788781992817903211 5234249683172989226854817)
      ·
        refine ⟨3925687262379741920141113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5234249683172989226854817 3925687262379741920141113)
        ·
          refine ⟨2944265446784806440105835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3925687262379741920141113 2944265446784806440105835)
          ·
            refine ⟨4416398170177209660158753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2944265446784806440105835 4416398170177209660158753)
            ·
              refine ⟨3312298627632907245119065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4416398170177209660158753 3312298627632907245119065)
              ·
                refine ⟨2484223970724680433839299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3312298627632907245119065 2484223970724680433839299)
                ·
                  refine ⟨3726335956087020650758949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2484223970724680433839299 3726335956087020650758949)
                  ·
                    refine ⟨698687991766316372017303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3726335956087020650758949 698687991766316372017303)
                    ·
                      rfl

theorem cell23_4082070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_4082070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4082070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4082070 prefixEnd_4082070 := by exact prefixLift 4082070
  have htrace : WordTrace (prefixWord ++ tailWord_4082070) baseStart_4082070 baseEnd_4082070 := by
    simpa [prefixWord, tailWord_4082070, baseEnd_4082070] using wordTrace_append hprefix tailTrace_4082070
  have hstable : (prefixWord ++ tailWord_4082070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4082070).length < 2 ^ (prefixWord ++ tailWord_4082070).sum := by decide
  have hdescent : baseEnd_4082070 < baseStart_4082070 := by decide
  rcases family_descends (prefixWord ++ tailWord_4082070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4082088 : List Nat := [2, 1, 6, 1, 1, 1, 3, 8]
def baseStart_4082088 : Nat := 118140960795 + 4082088 * 2 ^ 59
def prefixEnd_4082088 : Nat := 4983230072969 + 3 ^ 40 * 4082088 * 2
def baseEnd_4082088 : Nat := 77632341405582594282475

theorem tailTrace_4082088 : CollatzResearch.WordTrace tailWord_4082088 prefixEnd_4082088 77632341405582594282475 := by
  unfold tailWord_4082088
  simp only [CollatzResearch.WordTrace]
  refine ⟨74442990417649907985679459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99257320556866543980905945 74442990417649907985679459)
  ·
    refine ⟨111664485626474861978519189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74442990417649907985679459 111664485626474861978519189)
    ·
      refine ⟨5234272763741009155243087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 111664485626474861978519189 5234272763741009155243087)
      ·
        refine ⟨7851409145611513732864631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5234272763741009155243087 7851409145611513732864631)
        ·
          refine ⟨11777113718417270599296947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7851409145611513732864631 11777113718417270599296947)
          ·
            refine ⟨17665670577625905898945421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11777113718417270599296947 17665670577625905898945421)
            ·
              refine ⟨6624626466609714712104533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17665670577625905898945421 6624626466609714712104533)
              ·
                refine ⟨77632341405582594282475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6624626466609714712104533 77632341405582594282475)
                ·
                  rfl

theorem cell23_4082088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 3, 8].length) (baseStart_4082088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4082088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4082088 prefixEnd_4082088 := by exact prefixLift 4082088
  have htrace : WordTrace (prefixWord ++ tailWord_4082088) baseStart_4082088 baseEnd_4082088 := by
    simpa [prefixWord, tailWord_4082088, baseEnd_4082088] using wordTrace_append hprefix tailTrace_4082088
  have hstable : (prefixWord ++ tailWord_4082088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4082088).length < 2 ^ (prefixWord ++ tailWord_4082088).sum := by decide
  have hdescent : baseEnd_4082088 < baseStart_4082088 := by decide
  rcases family_descends (prefixWord ++ tailWord_4082088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4082098 : List Nat := [3, 2, 1, 1, 1, 1, 6, 1, 1, 3, 3]
def baseStart_4082098 : Nat := 118140960795 + 4082098 * 2 ^ 59
def prefixEnd_4082098 : Nat := 4983230072969 + 3 ^ 40 * 4082098 * 2
def baseEnd_4082098 : Nat := 2096078352757275006501779

theorem tailTrace_4082098 : CollatzResearch.WordTrace tailWord_4082098 prefixEnd_4082098 2096078352757275006501779 := by
  unfold tailWord_4082098
  simp only [CollatzResearch.WordTrace]
  refine ⟨37221586391315896919805737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99257563710175725119481965 37221586391315896919805737)
  ·
    refine ⟨27916189793486922689854303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37221586391315896919805737 27916189793486922689854303)
    ·
      refine ⟨41874284690230384034781455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27916189793486922689854303 41874284690230384034781455)
      ·
        refine ⟨62811427035345576052172183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41874284690230384034781455 62811427035345576052172183)
        ·
          refine ⟨94217140553018364078258275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62811427035345576052172183 94217140553018364078258275)
          ·
            refine ⟨141325710829527546117387413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94217140553018364078258275 141325710829527546117387413)
            ·
              refine ⟨6624642695134103724252535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 141325710829527546117387413 6624642695134103724252535)
              ·
                refine ⟨9936964042701155586378803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6624642695134103724252535 9936964042701155586378803)
                ·
                  refine ⟨14905446064051733379568205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9936964042701155586378803 14905446064051733379568205)
                  ·
                    refine ⟨5589542274019400017338077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14905446064051733379568205 5589542274019400017338077)
                    ·
                      refine ⟨2096078352757275006501779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5589542274019400017338077 2096078352757275006501779)
                      ·
                        rfl

theorem cell23_4082098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 6, 1, 1, 3, 3].length) (baseStart_4082098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4082098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4082098 prefixEnd_4082098 := by exact prefixLift 4082098
  have htrace : WordTrace (prefixWord ++ tailWord_4082098) baseStart_4082098 baseEnd_4082098 := by
    simpa [prefixWord, tailWord_4082098, baseEnd_4082098] using wordTrace_append hprefix tailTrace_4082098
  have hstable : (prefixWord ++ tailWord_4082098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4082098).length < 2 ^ (prefixWord ++ tailWord_4082098).sum := by decide
  have hdescent : baseEnd_4082098 < baseStart_4082098 := by decide
  rcases family_descends (prefixWord ++ tailWord_4082098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4082116 : List Nat := [2, 3, 3, 2, 2, 1, 2, 3, 1, 2, 2]
def baseStart_4082116 : Nat := 118140960795 + 4082116 * 2 ^ 59
def prefixEnd_4082116 : Nat := 4983230072969 + 3 ^ 40 * 4082116 * 2
def baseEnd_4082116 : Nat := 2096087595409055936076697

theorem tailTrace_4082116 : CollatzResearch.WordTrace tailWord_4082116 prefixEnd_4082116 2096087595409055936076697 := by
  unfold tailWord_4082116
  simp only [CollatzResearch.WordTrace]
  refine ⟨74443501039599188376689101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99258001386132251168918801 74443501039599188376689101)
  ·
    refine ⟨27916312889849695641258413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74443501039599188376689101 27916312889849695641258413)
    ·
      refine ⟨10468617333693635865471905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27916312889849695641258413 10468617333693635865471905)
      ·
        refine ⟨7851463000270226899103929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10468617333693635865471905 7851463000270226899103929)
        ·
          refine ⟨5888597250202670174327947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7851463000270226899103929 5888597250202670174327947)
          ·
            refine ⟨8832895875304005261491921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5888597250202670174327947 8832895875304005261491921)
            ·
              refine ⟨6624671906478003946118941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8832895875304005261491921 6624671906478003946118941)
              ·
                refine ⟨2484251964929251479794603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6624671906478003946118941 2484251964929251479794603)
                ·
                  refine ⟨3726377947393877219691905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2484251964929251479794603 3726377947393877219691905)
                  ·
                    refine ⟨2794783460545407914768929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3726377947393877219691905 2794783460545407914768929)
                    ·
                      refine ⟨2096087595409055936076697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2794783460545407914768929 2096087595409055936076697)
                      ·
                        rfl

theorem cell23_4082116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 2, 3, 1, 2, 2].length) (baseStart_4082116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4082116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4082116 prefixEnd_4082116 := by exact prefixLift 4082116
  have htrace : WordTrace (prefixWord ++ tailWord_4082116) baseStart_4082116 baseEnd_4082116 := by
    simpa [prefixWord, tailWord_4082116, baseEnd_4082116] using wordTrace_append hprefix tailTrace_4082116
  have hstable : (prefixWord ++ tailWord_4082116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4082116).length < 2 ^ (prefixWord ++ tailWord_4082116).sum := by decide
  have hdescent : baseEnd_4082116 < baseStart_4082116 := by decide
  rcases family_descends (prefixWord ++ tailWord_4082116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4082132 : List Nat := [2, 4, 1, 2, 2, 1, 3, 2, 2, 1, 3]
def baseStart_4082132 : Nat := 118140960795 + 4082132 * 2 ^ 59
def prefixEnd_4082132 : Nat := 4983230072969 + 3 ^ 40 * 4082132 * 2
def baseEnd_4082132 : Nat := 2096095811099527873476623

theorem tailTrace_4082132 : CollatzResearch.WordTrace tailWord_4082132 prefixEnd_4082132 2096095811099527873476623 := by
  unfold tailWord_4082132
  simp only [CollatzResearch.WordTrace]
  refine ⟨74443792823570205742980325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99258390431426940990640433 74443792823570205742980325)
  ·
    refine ⟨13958211154419413576808811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74443792823570205742980325 13958211154419413576808811)
    ·
      refine ⟨20937316731629120365213217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13958211154419413576808811 20937316731629120365213217)
      ·
        refine ⟨15702987548721840273909913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20937316731629120365213217 15702987548721840273909913)
        ·
          refine ⟨11777240661541380205432435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15702987548721840273909913 11777240661541380205432435)
          ·
            refine ⟨17665860992312070308148653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11777240661541380205432435 17665860992312070308148653)
            ·
              refine ⟨6624697872117026365555745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17665860992312070308148653 6624697872117026365555745)
              ·
                refine ⟨4968523404087769774166809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6624697872117026365555745 4968523404087769774166809)
                ·
                  refine ⟨3726392553065827330625107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4968523404087769774166809 3726392553065827330625107)
                  ·
                    refine ⟨5589588829598740995937661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3726392553065827330625107 5589588829598740995937661)
                    ·
                      refine ⟨2096095811099527873476623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5589588829598740995937661 2096095811099527873476623)
                      ·
                        rfl

theorem cell23_4082132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 3, 2, 2, 1, 3].length) (baseStart_4082132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4082132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4082132 prefixEnd_4082132 := by exact prefixLift 4082132
  have htrace : WordTrace (prefixWord ++ tailWord_4082132) baseStart_4082132 baseEnd_4082132 := by
    simpa [prefixWord, tailWord_4082132, baseEnd_4082132] using wordTrace_append hprefix tailTrace_4082132
  have hstable : (prefixWord ++ tailWord_4082132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4082132).length < 2 ^ (prefixWord ++ tailWord_4082132).sum := by decide
  have hdescent : baseEnd_4082132 < baseStart_4082132 := by decide
  rcases family_descends (prefixWord ++ tailWord_4082132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4082149 : List Nat := [1, 3, 1, 5, 2, 1, 3, 1, 2, 1, 3]
def baseStart_4082149 : Nat := 118140960795 + 4082149 * 2 ^ 59
def prefixEnd_4082149 : Nat := 4983230072969 + 3 ^ 40 * 4082149 * 2
def baseEnd_4082149 : Nat := 2096104540270654306964045

theorem tailTrace_4082149 : CollatzResearch.WordTrace tailWord_4082149 prefixEnd_4082149 2096104540270654306964045 := by
  unfold tailWord_4082149
  simp only [CollatzResearch.WordTrace]
  refine ⟨148888205688078823389329501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99258803792052548926219667 148888205688078823389329501)
  ·
    refine ⟨55833077133029558770998563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148888205688078823389329501 55833077133029558770998563)
    ·
      refine ⟨83749615699544338156497845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55833077133029558770998563 83749615699544338156497845)
      ·
        refine ⟨7851526471832281702171673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 83749615699544338156497845 7851526471832281702171673)
        ·
          refine ⟨5888644853874211276628755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7851526471832281702171673 5888644853874211276628755)
          ·
            refine ⟨8832967280811316914943133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5888644853874211276628755 8832967280811316914943133)
            ·
              refine ⟨3312362730304243843103675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8832967280811316914943133 3312362730304243843103675)
              ·
                refine ⟨4968544095456365764655513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3312362730304243843103675 4968544095456365764655513)
                ·
                  refine ⟨3726408071592274323491635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4968544095456365764655513 3726408071592274323491635)
                  ·
                    refine ⟨5589612107388411485237453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3726408071592274323491635 5589612107388411485237453)
                    ·
                      refine ⟨2096104540270654306964045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5589612107388411485237453 2096104540270654306964045)
                      ·
                        rfl

theorem cell23_4082149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 3, 1, 2, 1, 3].length) (baseStart_4082149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4082149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4082149 prefixEnd_4082149 := by exact prefixLift 4082149
  have htrace : WordTrace (prefixWord ++ tailWord_4082149) baseStart_4082149 baseEnd_4082149 := by
    simpa [prefixWord, tailWord_4082149, baseEnd_4082149] using wordTrace_append hprefix tailTrace_4082149
  have hstable : (prefixWord ++ tailWord_4082149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4082149).length < 2 ^ (prefixWord ++ tailWord_4082149).sum := by decide
  have hdescent : baseEnd_4082149 < baseStart_4082149 := by decide
  rcases family_descends (prefixWord ++ tailWord_4082149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4082161 : List Nat := [1, 2, 2, 2, 3, 1, 1, 4, 7]
def baseStart_4082161 : Nat := 118140960795 + 4082161 * 2 ^ 59
def prefixEnd_4082161 : Nat := 4983230072969 + 3 ^ 40 * 4082161 * 2
def baseEnd_4082161 : Nat := 232901189115389806668221

theorem tailTrace_4082161 : CollatzResearch.WordTrace tailWord_4082161 prefixEnd_4082161 232901189115389806668221 := by
  unfold tailWord_4082161
  simp only [CollatzResearch.WordTrace]
  refine ⟨148888643364035349438766337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99259095576023566292510891 148888643364035349438766337)
  ·
    refine ⟨111666482523026512079074753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148888643364035349438766337 111666482523026512079074753)
    ·
      refine ⟨83749861892269884059306065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111666482523026512079074753 83749861892269884059306065)
      ·
        refine ⟨62812396419202413044479549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83749861892269884059306065 62812396419202413044479549)
        ·
          refine ⟨23554648657200904891679831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62812396419202413044479549 23554648657200904891679831)
          ·
            refine ⟨35331972985801357337519747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23554648657200904891679831 35331972985801357337519747)
            ·
              refine ⟨52997959478702036006279621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35331972985801357337519747 52997959478702036006279621)
              ·
                refine ⟨9937117402256631751177429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52997959478702036006279621 9937117402256631751177429)
                ·
                  refine ⟨232901189115389806668221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9937117402256631751177429 232901189115389806668221)
                  ·
                    rfl

theorem cell23_4082161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 4, 7].length) (baseStart_4082161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4082161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4082161 prefixEnd_4082161 := by exact prefixLift 4082161
  have htrace : WordTrace (prefixWord ++ tailWord_4082161) baseStart_4082161 baseEnd_4082161 := by
    simpa [prefixWord, tailWord_4082161, baseEnd_4082161] using wordTrace_append hprefix tailTrace_4082161
  have hstable : (prefixWord ++ tailWord_4082161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4082161).length < 2 ^ (prefixWord ++ tailWord_4082161).sum := by decide
  have hdescent : baseEnd_4082161 < baseStart_4082161 := by decide
  rcases family_descends (prefixWord ++ tailWord_4082161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4082191 : List Nat := [1, 1, 2, 1, 1, 1, 2, 5, 4, 5]
def baseStart_4082191 : Nat := 118140960795 + 4082191 * 2 ^ 59
def prefixEnd_4082191 : Nat := 4983230072969 + 3 ^ 40 * 4082191 * 2
def baseEnd_4082191 : Nat := 698708702152714380879617

theorem tailTrace_4082191 : CollatzResearch.WordTrace tailWord_4082191 prefixEnd_4082191 698708702152714380879617 := by
  unfold tailWord_4082191
  simp only [CollatzResearch.WordTrace]
  refine ⟨148889737553926664562358427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99259825035951109708238951 148889737553926664562358427)
  ·
    refine ⟨223334606330889996843537641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148889737553926664562358427 223334606330889996843537641)
    ·
      refine ⟨167500954748167497632653231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223334606330889996843537641 167500954748167497632653231)
      ·
        refine ⟨251251432122251246448979847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167500954748167497632653231 251251432122251246448979847)
        ·
          refine ⟨376877148183376869673469771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251251432122251246448979847 376877148183376869673469771)
          ·
            refine ⟨565315722275065304510204657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 376877148183376869673469771 565315722275065304510204657)
            ·
              refine ⟨423986791706298978382653493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 565315722275065304510204657 423986791706298978382653493)
              ·
                refine ⟨39748761722465529223373765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 423986791706298978382653493 39748761722465529223373765)
                ·
                  refine ⟨7452892822962286729382581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39748761722465529223373765 7452892822962286729382581)
                  ·
                    refine ⟨698708702152714380879617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7452892822962286729382581 698708702152714380879617)
                    ·
                      rfl

theorem cell23_4082191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 5, 4, 5].length) (baseStart_4082191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4082191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4082191 prefixEnd_4082191 := by exact prefixLift 4082191
  have htrace : WordTrace (prefixWord ++ tailWord_4082191) baseStart_4082191 baseEnd_4082191 := by
    simpa [prefixWord, tailWord_4082191, baseEnd_4082191] using wordTrace_append hprefix tailTrace_4082191
  have hstable : (prefixWord ++ tailWord_4082191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4082191).length < 2 ^ (prefixWord ++ tailWord_4082191).sum := by decide
  have hdescent : baseEnd_4082191 < baseStart_4082191 := by decide
  rcases family_descends (prefixWord ++ tailWord_4082191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4082195 : List Nat := [1, 1, 1, 2, 1, 5, 5, 2, 5]
def baseStart_4082195 : Nat := 118140960795 + 4082195 * 2 ^ 59
def prefixEnd_4082195 : Nat := 4983230072969 + 3 ^ 40 * 4082195 * 2
def baseEnd_4082195 : Nat := 232903128931195680776537

theorem tailTrace_4082195 : CollatzResearch.WordTrace tailWord_4082195 prefixEnd_4082195 232903128931195680776537 := by
  unfold tailWord_4082195
  simp only [CollatzResearch.WordTrace]
  refine ⟨148889883445912173245504039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99259922297274782163669359 148889883445912173245504039)
  ·
    refine ⟨223334825168868259868256059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148889883445912173245504039 223334825168868259868256059)
    ·
      refine ⟨335002237753302389802384089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223334825168868259868256059 335002237753302389802384089)
      ·
        refine ⟨251251678314976792351788067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 335002237753302389802384089 251251678314976792351788067)
        ·
          refine ⟨376877517472465188527682101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251251678314976792351788067 376877517472465188527682101)
          ·
            refine ⟨35332267263043611424470197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 376877517472465188527682101 35332267263043611424470197)
            ·
              refine ⟨3312400055910338571044081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35332267263043611424470197 3312400055910338571044081)
              ·
                refine ⟨2484300041932753928283061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3312400055910338571044081 2484300041932753928283061)
                ·
                  refine ⟨232903128931195680776537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2484300041932753928283061 232903128931195680776537)
                  ·
                    rfl

theorem cell23_4082195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 5, 2, 5].length) (baseStart_4082195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4082195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4082195 prefixEnd_4082195 := by exact prefixLift 4082195
  have htrace : WordTrace (prefixWord ++ tailWord_4082195) baseStart_4082195 baseEnd_4082195 := by
    simpa [prefixWord, tailWord_4082195, baseEnd_4082195] using wordTrace_append hprefix tailTrace_4082195
  have hstable : (prefixWord ++ tailWord_4082195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4082195).length < 2 ^ (prefixWord ++ tailWord_4082195).sum := by decide
  have hdescent : baseEnd_4082195 < baseStart_4082195 := by decide
  rcases family_descends (prefixWord ++ tailWord_4082195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4082201 : List Nat := [1, 2, 1, 2, 1, 1, 2, 5, 1, 2, 5]
def baseStart_4082201 : Nat := 118140960795 + 4082201 * 2 ^ 59
def prefixEnd_4082201 : Nat := 4983230072969 + 3 ^ 40 * 4082201 * 2
def baseEnd_4082201 : Nat := 2096131241264688103513805

theorem tailTrace_4082201 : CollatzResearch.WordTrace tailWord_4082201 prefixEnd_4082201 2096131241264688103513805 := by
  unfold tailWord_4082201
  simp only [CollatzResearch.WordTrace]
  refine ⟨148890102283890436270222457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99260068189260290846814971 148890102283890436270222457)
  ·
    refine ⟨111667576712917827202666843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148890102283890436270222457 111667576712917827202666843)
    ·
      refine ⟨167501365069376740804000265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111667576712917827202666843 167501365069376740804000265)
      ·
        refine ⟨125626023802032555603000199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167501365069376740804000265 125626023802032555603000199)
        ·
          refine ⟨188439035703048833404500299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125626023802032555603000199 188439035703048833404500299)
          ·
            refine ⟨282658553554573250106750449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188439035703048833404500299 282658553554573250106750449)
            ·
              refine ⟨211993915165929937580062837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 282658553554573250106750449 211993915165929937580062837)
              ·
                refine ⟨19874429546805931648130891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 211993915165929937580062837 19874429546805931648130891)
                ·
                  refine ⟨29811644320208897472196337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19874429546805931648130891 29811644320208897472196337)
                  ·
                    refine ⟨22358733240156673104147253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29811644320208897472196337 22358733240156673104147253)
                    ·
                      refine ⟨2096131241264688103513805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22358733240156673104147253 2096131241264688103513805)
                      ·
                        rfl

theorem cell23_4082201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 5, 1, 2, 5].length) (baseStart_4082201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4082201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4082201 prefixEnd_4082201 := by exact prefixLift 4082201
  have htrace : WordTrace (prefixWord ++ tailWord_4082201) baseStart_4082201 baseEnd_4082201 := by
    simpa [prefixWord, tailWord_4082201, baseEnd_4082201] using wordTrace_append hprefix tailTrace_4082201
  have hstable : (prefixWord ++ tailWord_4082201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4082201).length < 2 ^ (prefixWord ++ tailWord_4082201).sum := by decide
  have hdescent : baseEnd_4082201 < baseStart_4082201 := by decide
  rcases family_descends (prefixWord ++ tailWord_4082201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4082246 : List Nat := [6, 1, 1, 1, 2, 3, 2, 2, 5]
def baseStart_4082246 : Nat := 118140960795 + 4082246 * 2 ^ 59
def prefixEnd_4082246 : Nat := 4983230072969 + 3 ^ 40 * 4082246 * 2
def baseEnd_4082246 : Nat := 232906038654904491939011

theorem tailTrace_4082246 : CollatzResearch.WordTrace tailWord_4082246 prefixEnd_4082246 232906038654904491939011 := by
  unfold tailWord_4082246
  simp only [CollatzResearch.WordTrace]
  refine ⟨4652866986522731529862831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 99261162379151605970407061 4652866986522731529862831)
  ·
    refine ⟨6979300479784097294794247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4652866986522731529862831 6979300479784097294794247)
    ·
      refine ⟨10468950719676145942191371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6979300479784097294794247 10468950719676145942191371)
      ·
        refine ⟨15703426079514218913287057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10468950719676145942191371 15703426079514218913287057)
        ·
          refine ⟨11777569559635664184965293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15703426079514218913287057 11777569559635664184965293)
          ·
            refine ⟨4416588584863374069361985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11777569559635664184965293 4416588584863374069361985)
            ·
              refine ⟨3312441438647530552021489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4416588584863374069361985 3312441438647530552021489)
              ·
                refine ⟨2484331078985647914016117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3312441438647530552021489 2484331078985647914016117)
                ·
                  refine ⟨232906038654904491939011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2484331078985647914016117 232906038654904491939011)
                  ·
                    rfl

theorem cell23_4082246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 2, 2, 5].length) (baseStart_4082246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4082246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4082246 prefixEnd_4082246 := by exact prefixLift 4082246
  have htrace : WordTrace (prefixWord ++ tailWord_4082246) baseStart_4082246 baseEnd_4082246 := by
    simpa [prefixWord, tailWord_4082246, baseEnd_4082246] using wordTrace_append hprefix tailTrace_4082246
  have hstable : (prefixWord ++ tailWord_4082246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4082246).length < 2 ^ (prefixWord ++ tailWord_4082246).sum := by decide
  have hdescent : baseEnd_4082246 < baseStart_4082246 := by decide
  rcases family_descends (prefixWord ++ tailWord_4082246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4082251 : List Nat := [1, 1, 1, 1, 3, 1, 4, 3, 8]
def baseStart_4082251 : Nat := 118140960795 + 4082251 * 2 ^ 59
def prefixEnd_4082251 : Nat := 4983230072969 + 3 ^ 40 * 4082251 * 2
def baseEnd_4082251 : Nat := 232906323921934767543175

theorem tailTrace_4082251 : CollatzResearch.WordTrace tailWord_4082251 prefixEnd_4082251 232906323921934767543175 := by
  unfold tailWord_4082251
  simp only [CollatzResearch.WordTrace]
  refine ⟨148891925933709294809542607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99261283955806196539695071 148891925933709294809542607)
  ·
    refine ⟨223337888900563942214313911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148891925933709294809542607 223337888900563942214313911)
    ·
      refine ⟨335006833350845913321470867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223337888900563942214313911 335006833350845913321470867)
      ·
        refine ⟨502510250026268869982206301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335006833350845913321470867 502510250026268869982206301)
        ·
          refine ⟨188441343759850826243327363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 502510250026268869982206301 188441343759850826243327363)
          ·
            refine ⟨282662015639776239364991045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188441343759850826243327363 282662015639776239364991045)
            ·
              refine ⟨52999127932458044880935821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 282662015639776239364991045 52999127932458044880935821)
              ·
                refine ⟨19874672974671766830350933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52999127932458044880935821 19874672974671766830350933)
                ·
                  refine ⟨232906323921934767543175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19874672974671766830350933 232906323921934767543175)
                  ·
                    rfl

theorem cell23_4082251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 3, 8].length) (baseStart_4082251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4082251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4082251 prefixEnd_4082251 := by exact prefixLift 4082251
  have htrace : WordTrace (prefixWord ++ tailWord_4082251) baseStart_4082251 baseEnd_4082251 := by
    simpa [prefixWord, tailWord_4082251, baseEnd_4082251] using wordTrace_append hprefix tailTrace_4082251
  have hstable : (prefixWord ++ tailWord_4082251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4082251).length < 2 ^ (prefixWord ++ tailWord_4082251).sum := by decide
  have hdescent : baseEnd_4082251 < baseStart_4082251 := by decide
  rcases family_descends (prefixWord ++ tailWord_4082251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4082322 : List Nat := [3, 2, 3, 1, 2, 1, 1, 2, 1, 5, 2]
def baseStart_4082322 : Nat := 118140960795 + 4082322 * 2 ^ 59
def prefixEnd_4082322 : Nat := 4983230072969 + 3 ^ 40 * 4082322 * 2
def baseEnd_4082322 : Nat := 2096193372423882130100749

theorem tailTrace_4082322 : CollatzResearch.WordTrace tailWord_4082322 prefixEnd_4082322 2096193372423882130100749 := by
  unfold tailWord_4082322
  simp only [CollatzResearch.WordTrace]
  refine ⟨37223628879113018483844305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99263010344301382623584813 37223628879113018483844305)
  ·
    refine ⟨27917721659334763862883229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37223628879113018483844305 27917721659334763862883229)
    ·
      refine ⟨10469145622250536448581211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27917721659334763862883229 10469145622250536448581211)
      ·
        refine ⟨15703718433375804672871817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10469145622250536448581211 15703718433375804672871817)
        ·
          refine ⟨11777788825031853504653863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15703718433375804672871817 11777788825031853504653863)
          ·
            refine ⟨17666683237547780256980795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11777788825031853504653863 17666683237547780256980795)
            ·
              refine ⟨26500024856321670385471193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17666683237547780256980795 26500024856321670385471193)
              ·
                refine ⟨19875018642241252789103395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26500024856321670385471193 19875018642241252789103395)
                ·
                  refine ⟨29812527963361879183655093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19875018642241252789103395 29812527963361879183655093)
                  ·
                    refine ⟨2794924496565176173467665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29812527963361879183655093 2794924496565176173467665)
                    ·
                      refine ⟨2096193372423882130100749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2794924496565176173467665 2096193372423882130100749)
                      ·
                        rfl

theorem cell23_4082322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 2, 1, 5, 2].length) (baseStart_4082322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4082322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4082322 prefixEnd_4082322 := by exact prefixLift 4082322
  have htrace : WordTrace (prefixWord ++ tailWord_4082322) baseStart_4082322 baseEnd_4082322 := by
    simpa [prefixWord, tailWord_4082322, baseEnd_4082322] using wordTrace_append hprefix tailTrace_4082322
  have hstable : (prefixWord ++ tailWord_4082322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4082322).length < 2 ^ (prefixWord ++ tailWord_4082322).sum := by decide
  have hdescent : baseEnd_4082322 < baseStart_4082322 := by decide
  rcases family_descends (prefixWord ++ tailWord_4082322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4082332 : List Nat := [2, 2, 3, 2, 2, 2, 2, 2, 1, 5]
def baseStart_4082332 : Nat := 118140960795 + 4082332 * 2 ^ 59
def prefixEnd_4082332 : Nat := 4983230072969 + 3 ^ 40 * 4082332 * 2
def baseEnd_4082332 : Nat := 698732835743475696991901

theorem tailTrace_4082332 : CollatzResearch.WordTrace tailWord_4082332 prefixEnd_4082332 698732835743475696991901 := by
  unfold tailWord_4082332
  simp only [CollatzResearch.WordTrace]
  refine ⟨74447440123207922821620625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99263253497610563762160833 74447440123207922821620625)
  ·
    refine ⟨55835580092405942116215469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74447440123207922821620625 55835580092405942116215469)
    ·
      refine ⟨20938342534652228293580801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55835580092405942116215469 20938342534652228293580801)
      ·
        refine ⟨15703756900989171220185601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20938342534652228293580801 15703756900989171220185601)
        ·
          refine ⟨11777817675741878415139201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15703756900989171220185601 11777817675741878415139201)
          ·
            refine ⟨8833363256806408811354401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11777817675741878415139201 8833363256806408811354401)
            ·
              refine ⟨6625022442604806608515801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8833363256806408811354401 6625022442604806608515801)
              ·
                refine ⟨4968766831953604956386851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6625022442604806608515801 4968766831953604956386851)
                ·
                  refine ⟨7453150247930407434580277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4968766831953604956386851 7453150247930407434580277)
                  ·
                    refine ⟨698732835743475696991901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7453150247930407434580277 698732835743475696991901)
                    ·
                      rfl

theorem cell23_4082332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 2, 2, 1, 5].length) (baseStart_4082332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4082332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4082332 prefixEnd_4082332 := by exact prefixLift 4082332
  have htrace : WordTrace (prefixWord ++ tailWord_4082332) baseStart_4082332 baseEnd_4082332 := by
    simpa [prefixWord, tailWord_4082332, baseEnd_4082332] using wordTrace_append hprefix tailTrace_4082332
  have hstable : (prefixWord ++ tailWord_4082332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4082332).length < 2 ^ (prefixWord ++ tailWord_4082332).sum := by decide
  have hdescent : baseEnd_4082332 < baseStart_4082332 := by decide
  rcases family_descends (prefixWord ++ tailWord_4082332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4082355 : List Nat := [1, 1, 1, 2, 3, 5, 2, 1, 1, 1, 5]
def baseStart_4082355 : Nat := 118140960795 + 4082355 * 2 ^ 59
def prefixEnd_4082355 : Nat := 4983230072969 + 3 ^ 40 * 4082355 * 2
def baseEnd_4082355 : Nat := 2096210317285480500988097

theorem tailTrace_4082355 : CollatzResearch.WordTrace tailWord_4082355 prefixEnd_4082355 2096210317285480500988097 := by
  unfold tailWord_4082355
  simp only [CollatzResearch.WordTrace]
  refine ⟨148895719125332520571328519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99263812750221680380885679 148895719125332520571328519)
  ·
    refine ⟨223343578687998780856992779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148895719125332520571328519 223343578687998780856992779)
    ·
      refine ⟨335015368031998171285489169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223343578687998780856992779 335015368031998171285489169)
      ·
        refine ⟨251261526023998628464116877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 335015368031998171285489169 251261526023998628464116877)
        ·
          refine ⟨94223072258999485674043829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 251261526023998628464116877 94223072258999485674043829)
          ·
            refine ⟨8833413024281201781941609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 94223072258999485674043829 8833413024281201781941609)
            ·
              refine ⟨6625059768210901336456207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8833413024281201781941609 6625059768210901336456207)
              ·
                refine ⟨9937589652316352004684311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6625059768210901336456207 9937589652316352004684311)
                ·
                  refine ⟨14906384478474528007026467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9937589652316352004684311 14906384478474528007026467)
                  ·
                    refine ⟨22359576717711792010539701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14906384478474528007026467 22359576717711792010539701)
                    ·
                      refine ⟨2096210317285480500988097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22359576717711792010539701 2096210317285480500988097)
                      ·
                        rfl

theorem cell23_4082355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 2, 1, 1, 1, 5].length) (baseStart_4082355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4082355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4082355 prefixEnd_4082355 := by exact prefixLift 4082355
  have htrace : WordTrace (prefixWord ++ tailWord_4082355) baseStart_4082355 baseEnd_4082355 := by
    simpa [prefixWord, tailWord_4082355, baseEnd_4082355] using wordTrace_append hprefix tailTrace_4082355
  have hstable : (prefixWord ++ tailWord_4082355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4082355).length < 2 ^ (prefixWord ++ tailWord_4082355).sum := by decide
  have hdescent : baseEnd_4082355 < baseStart_4082355 := by decide
  rcases family_descends (prefixWord ++ tailWord_4082355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4082385 : List Nat := [1, 2, 2, 1, 2, 3, 2, 3, 1, 3, 3]
def baseStart_4082385 : Nat := 118140960795 + 4082385 * 2 ^ 59
def prefixEnd_4082385 : Nat := 4983230072969 + 3 ^ 40 * 4082385 * 2
def baseEnd_4082385 : Nat := 2096225721705115383612959

theorem tailTrace_4082385 : CollatzResearch.WordTrace tailWord_4082385 prefixEnd_4082385 2096225721705115383612959 := by
  unfold tailWord_4082385
  simp only [CollatzResearch.WordTrace]
  refine ⟨148896813315223835694920609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99264542210149223796613739 148896813315223835694920609)
  ·
    refine ⟨111672609986417876771190457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148896813315223835694920609 111672609986417876771190457)
    ·
      refine ⟨83754457489813407578392843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111672609986417876771190457 83754457489813407578392843)
      ·
        refine ⟨125631686234720111367589265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83754457489813407578392843 125631686234720111367589265)
        ·
          refine ⟨94223764676040083525691949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125631686234720111367589265 94223764676040083525691949)
          ·
            refine ⟨35333911753515031322134481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94223764676040083525691949 35333911753515031322134481)
            ·
              refine ⟨26500433815136273491600861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35333911753515031322134481 26500433815136273491600861)
              ·
                refine ⟨9937662680676102559350323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26500433815136273491600861 9937662680676102559350323)
                ·
                  refine ⟨14906494021014153839025485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9937662680676102559350323 14906494021014153839025485)
                  ·
                    refine ⟨5589935257880307689634557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14906494021014153839025485 5589935257880307689634557)
                    ·
                      refine ⟨2096225721705115383612959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5589935257880307689634557 2096225721705115383612959)
                      ·
                        rfl

theorem cell23_4082385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 3, 1, 3, 3].length) (baseStart_4082385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4082385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4082385 prefixEnd_4082385 := by exact prefixLift 4082385
  have htrace : WordTrace (prefixWord ++ tailWord_4082385) baseStart_4082385 baseEnd_4082385 := by
    simpa [prefixWord, tailWord_4082385, baseEnd_4082385] using wordTrace_append hprefix tailTrace_4082385
  have hstable : (prefixWord ++ tailWord_4082385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4082385).length < 2 ^ (prefixWord ++ tailWord_4082385).sum := by decide
  have hdescent : baseEnd_4082385 < baseStart_4082385 := by decide
  rcases family_descends (prefixWord ++ tailWord_4082385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4082386 : List Nat := [3, 2, 2, 2, 4, 1, 1, 2, 1, 1, 4]
def baseStart_4082386 : Nat := 118140960795 + 4082386 * 2 ^ 59
def prefixEnd_4082386 : Nat := 4983230072969 + 3 ^ 40 * 4082386 * 2
def baseEnd_4082386 : Nat := 2096226235185769879700455

theorem tailTrace_4082386 : CollatzResearch.WordTrace tailWord_4082386 prefixEnd_4082386 2096226235185769879700455 := by
  unfold tailWord_4082386
  simp only [CollatzResearch.WordTrace]
  refine ⟨37224212447055053216426753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99264566525480141910471341 37224212447055053216426753)
  ·
    refine ⟨27918159335291289912320065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37224212447055053216426753 27918159335291289912320065)
    ·
      refine ⟨20938619501468467434240049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27918159335291289912320065 20938619501468467434240049)
      ·
        refine ⟨15703964626101350575680037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20938619501468467434240049 15703964626101350575680037)
        ·
          refine ⟨2944493367394003232940007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15703964626101350575680037 2944493367394003232940007)
          ·
            refine ⟨4416740051091004849410011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2944493367394003232940007 4416740051091004849410011)
            ·
              refine ⟨6625110076636507274115017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4416740051091004849410011 6625110076636507274115017)
              ·
                refine ⟨4968832557477380455586263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6625110076636507274115017 4968832557477380455586263)
                ·
                  refine ⟨7453248836216070683379395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4968832557477380455586263 7453248836216070683379395)
                  ·
                    refine ⟨11179873254324106025069093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7453248836216070683379395 11179873254324106025069093)
                    ·
                      refine ⟨2096226235185769879700455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11179873254324106025069093 2096226235185769879700455)
                      ·
                        rfl

theorem cell23_4082386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 1, 2, 1, 1, 4].length) (baseStart_4082386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4082386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4082386 prefixEnd_4082386 := by exact prefixLift 4082386
  have htrace : WordTrace (prefixWord ++ tailWord_4082386) baseStart_4082386 baseEnd_4082386 := by
    simpa [prefixWord, tailWord_4082386, baseEnd_4082386] using wordTrace_append hprefix tailTrace_4082386
  have hstable : (prefixWord ++ tailWord_4082386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4082386).length < 2 ^ (prefixWord ++ tailWord_4082386).sum := by decide
  have hdescent : baseEnd_4082386 < baseStart_4082386 := by decide
  rcases family_descends (prefixWord ++ tailWord_4082386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4082389 : List Nat := [1, 3, 2, 5, 1, 1, 1, 1, 3, 2, 3]
def baseStart_4082389 : Nat := 118140960795 + 4082389 * 2 ^ 59
def prefixEnd_4082389 : Nat := 4983230072969 + 3 ^ 40 * 4082389 * 2
def baseEnd_4082389 : Nat := 2096227775627733367962941

theorem tailTrace_4082389 : CollatzResearch.WordTrace tailWord_4082389 prefixEnd_4082389 2096227775627733367962941 := by
  unfold tailWord_4082389
  simp only [CollatzResearch.WordTrace]
  refine ⟨148896959207209344378066221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99264639471472896252044147 148896959207209344378066221)
  ·
    refine ⟨55836359702703504141774833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148896959207209344378066221 55836359702703504141774833)
    ·
      refine ⟨41877269777027628106331125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55836359702703504141774833 41877269777027628106331125)
      ·
        refine ⟨3925994041596340134968543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41877269777027628106331125 3925994041596340134968543)
        ·
          refine ⟨5888991062394510202452815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3925994041596340134968543 5888991062394510202452815)
          ·
            refine ⟨8833486593591765303679223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5888991062394510202452815 8833486593591765303679223)
            ·
              refine ⟨13250229890387647955518835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8833486593591765303679223 13250229890387647955518835)
              ·
                refine ⟨19875344835581471933278253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13250229890387647955518835 19875344835581471933278253)
                ·
                  refine ⟨7453254313343051974979345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19875344835581471933278253 7453254313343051974979345)
                  ·
                    refine ⟨5589940735007288981234509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7453254313343051974979345 5589940735007288981234509)
                    ·
                      refine ⟨2096227775627733367962941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5589940735007288981234509 2096227775627733367962941)
                      ·
                        rfl

theorem cell23_4082389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_4082389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4082389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4082389 prefixEnd_4082389 := by exact prefixLift 4082389
  have htrace : WordTrace (prefixWord ++ tailWord_4082389) baseStart_4082389 baseEnd_4082389 := by
    simpa [prefixWord, tailWord_4082389, baseEnd_4082389] using wordTrace_append hprefix tailTrace_4082389
  have hstable : (prefixWord ++ tailWord_4082389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4082389).length < 2 ^ (prefixWord ++ tailWord_4082389).sum := by decide
  have hdescent : baseEnd_4082389 < baseStart_4082389 := by decide
  rcases family_descends (prefixWord ++ tailWord_4082389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4082475 : List Nat := [1, 1, 1, 1, 2, 1, 2, 6, 2, 3, 3]
def baseStart_4082475 : Nat := 118140960795 + 4082475 * 2 ^ 59
def prefixEnd_4082475 : Nat := 4983230072969 + 3 ^ 40 * 4082475 * 2
def baseEnd_4082475 : Nat := 2096271934964020031487545

theorem tailTrace_4082475 : CollatzResearch.WordTrace tailWord_4082475 prefixEnd_4082475 2096271934964020031487545 := by
  unfold tailWord_4082475
  simp only [CollatzResearch.WordTrace]
  refine ⟨148900095884897781065696879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99266730589931854043797919 148900095884897781065696879)
  ·
    refine ⟨223350143827346671598545319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148900095884897781065696879 223350143827346671598545319)
    ·
      refine ⟨335025215741020007397817979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223350143827346671598545319 335025215741020007397817979)
      ·
        refine ⟨502537823611530011096726969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335025215741020007397817979 502537823611530011096726969)
        ·
          refine ⟨376903367708647508322545227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 502537823611530011096726969 376903367708647508322545227)
          ·
            refine ⟨565355051562971262483817841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 376903367708647508322545227 565355051562971262483817841)
            ·
              refine ⟨424016288672228446862863381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 565355051562971262483817841 424016288672228446862863381)
              ·
                refine ⟨19875763531510708446696721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 424016288672228446862863381 19875763531510708446696721)
                ·
                  refine ⟨14906822648633031335022541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19875763531510708446696721 14906822648633031335022541)
                  ·
                    refine ⟨5590058493237386750633453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14906822648633031335022541 5590058493237386750633453)
                    ·
                      refine ⟨2096271934964020031487545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5590058493237386750633453 2096271934964020031487545)
                      ·
                        rfl

theorem cell23_4082475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 6, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 6, 2, 3, 3].length) (baseStart_4082475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4082475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4082475 prefixEnd_4082475 := by exact prefixLift 4082475
  have htrace : WordTrace (prefixWord ++ tailWord_4082475) baseStart_4082475 baseEnd_4082475 := by
    simpa [prefixWord, tailWord_4082475, baseEnd_4082475] using wordTrace_append hprefix tailTrace_4082475
  have hstable : (prefixWord ++ tailWord_4082475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4082475).length < 2 ^ (prefixWord ++ tailWord_4082475).sum := by decide
  have hdescent : baseEnd_4082475 < baseStart_4082475 := by decide
  rcases family_descends (prefixWord ++ tailWord_4082475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4082482 : List Nat := [3, 2, 1, 1, 3, 1, 1, 6, 5]
def baseStart_4082482 : Nat := 118140960795 + 4082482 * 2 ^ 59
def prefixEnd_4082482 : Nat := 4983230072969 + 3 ^ 40 * 4082482 * 2
def baseEnd_4082482 : Nat := 232919503258733500455557

theorem tailTrace_4082482 : CollatzResearch.WordTrace tailWord_4082482 prefixEnd_4082482 232919503258733500455557 := by
  unfold tailWord_4082482
  simp only [CollatzResearch.WordTrace]
  refine ⟨37225087798968105315300425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99266900797248280840801133 37225087798968105315300425)
  ·
    refine ⟨27918815849226078986475319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37225087798968105315300425 27918815849226078986475319)
    ·
      refine ⟨41878223773839118479712979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27918815849226078986475319 41878223773839118479712979)
      ·
        refine ⟨62817335660758677719569469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41878223773839118479712979 62817335660758677719569469)
        ·
          refine ⟨23556500872784504144838551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62817335660758677719569469 23556500872784504144838551)
          ·
            refine ⟨35334751309176756217257827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23556500872784504144838551 35334751309176756217257827)
            ·
              refine ⟨53002126963765134325886741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35334751309176756217257827 53002126963765134325886741)
              ·
                refine ⟨2484474701426490671525941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 53002126963765134325886741 2484474701426490671525941)
                ·
                  refine ⟨232919503258733500455557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2484474701426490671525941 232919503258733500455557)
                  ·
                    rfl

theorem cell23_4082482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 6, 5].length) (baseStart_4082482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4082482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4082482 prefixEnd_4082482 := by exact prefixLift 4082482
  have htrace : WordTrace (prefixWord ++ tailWord_4082482) baseStart_4082482 baseEnd_4082482 := by
    simpa [prefixWord, tailWord_4082482, baseEnd_4082482] using wordTrace_append hprefix tailTrace_4082482
  have hstable : (prefixWord ++ tailWord_4082482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4082482).length < 2 ^ (prefixWord ++ tailWord_4082482).sum := by decide
  have hdescent : baseEnd_4082482 < baseStart_4082482 := by decide
  rcases family_descends (prefixWord ++ tailWord_4082482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4082493 : List Nat := [1, 4, 1, 4, 3, 1, 1, 1, 1, 4, 2]
def baseStart_4082493 : Nat := 118140960795 + 4082493 * 2 ^ 59
def prefixEnd_4082493 : Nat := 4983230072969 + 3 ^ 40 * 4082493 * 2
def baseEnd_4082493 : Nat := 2096281177615800961062463

theorem tailTrace_4082493 : CollatzResearch.WordTrace tailWord_4082493 prefixEnd_4082493 2096281177615800961062463 := by
  unfold tailWord_4082493
  simp only [CollatzResearch.WordTrace]
  refine ⟨148900752398832570139852133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99267168265888380093234755 148900752398832570139852133)
  ·
    refine ⟨27918891074781106901222275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 148900752398832570139852133 27918891074781106901222275)
    ·
      refine ⟨41878336612171660351833413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27918891074781106901222275 41878336612171660351833413)
      ·
        refine ⟨7852188114782186315968765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41878336612171660351833413 7852188114782186315968765)
        ·
          refine ⟨2944570543043319868488287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7852188114782186315968765 2944570543043319868488287)
          ·
            refine ⟨4416855814564979802732431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2944570543043319868488287 4416855814564979802732431)
            ·
              refine ⟨6625283721847469704098647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4416855814564979802732431 6625283721847469704098647)
              ·
                refine ⟨9937925582771204556147971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6625283721847469704098647 9937925582771204556147971)
                ·
                  refine ⟨14906888374156806834221957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9937925582771204556147971 14906888374156806834221957)
                  ·
                    refine ⟨2795041570154401281416617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14906888374156806834221957 2795041570154401281416617)
                    ·
                      refine ⟨2096281177615800961062463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2795041570154401281416617 2096281177615800961062463)
                      ·
                        rfl

theorem cell23_4082493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 1, 1, 1, 4, 2].length) (baseStart_4082493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4082493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4082493 prefixEnd_4082493 := by exact prefixLift 4082493
  have htrace : WordTrace (prefixWord ++ tailWord_4082493) baseStart_4082493 baseEnd_4082493 := by
    simpa [prefixWord, tailWord_4082493, baseEnd_4082493] using wordTrace_append hprefix tailTrace_4082493
  have hstable : (prefixWord ++ tailWord_4082493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4082493).length < 2 ^ (prefixWord ++ tailWord_4082493).sum := by decide
  have hdescent : baseEnd_4082493 < baseStart_4082493 := by decide
  rcases family_descends (prefixWord ++ tailWord_4082493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4082495 : List Nat := [1, 1, 2, 2, 5, 1, 1, 2, 1, 7]
def baseStart_4082495 : Nat := 118140960795 + 4082495 * 2 ^ 59
def prefixEnd_4082495 : Nat := 4983230072969 + 3 ^ 40 * 4082495 * 2
def baseEnd_4082495 : Nat := 698760734859036651079151

theorem tailTrace_4082495 : CollatzResearch.WordTrace tailWord_4082495 prefixEnd_4082495 698760734859036651079151 := by
  unfold tailWord_4082495
  simp only [CollatzResearch.WordTrace]
  refine ⟨148900825344825324481424939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99267216896550216320949959 148900825344825324481424939)
  ·
    refine ⟨223351238017237986722137409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148900825344825324481424939 223351238017237986722137409)
    ·
      refine ⟨167513428512928490041603057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223351238017237986722137409 167513428512928490041603057)
      ·
        refine ⟨125635071384696367531202293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167513428512928490041603057 125635071384696367531202293)
        ·
          refine ⟨11778287942315284456050215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 125635071384696367531202293 11778287942315284456050215)
          ·
            refine ⟨17667431913472926684075323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11778287942315284456050215 17667431913472926684075323)
            ·
              refine ⟨26501147870209390026112985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17667431913472926684075323 26501147870209390026112985)
              ·
                refine ⟨19875860902657042519584739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26501147870209390026112985 19875860902657042519584739)
                ·
                  refine ⟨29813791353985563779377109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19875860902657042519584739 29813791353985563779377109)
                  ·
                    refine ⟨698760734859036651079151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29813791353985563779377109 698760734859036651079151)
                    ·
                      rfl

theorem cell23_4082495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 2, 1, 7].length) (baseStart_4082495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4082495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4082495 prefixEnd_4082495 := by exact prefixLift 4082495
  have htrace : WordTrace (prefixWord ++ tailWord_4082495) baseStart_4082495 baseEnd_4082495 := by
    simpa [prefixWord, tailWord_4082495, baseEnd_4082495] using wordTrace_append hprefix tailTrace_4082495
  have hstable : (prefixWord ++ tailWord_4082495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4082495).length < 2 ^ (prefixWord ++ tailWord_4082495).sum := by decide
  have hdescent : baseEnd_4082495 < baseStart_4082495 := by decide
  rcases family_descends (prefixWord ++ tailWord_4082495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4082515 : List Nat := [1, 1, 1, 2, 1, 1, 3, 2, 6, 1, 4]
def baseStart_4082515 : Nat := 118140960795 + 4082515 * 2 ^ 59
def prefixEnd_4082515 : Nat := 4983230072969 + 3 ^ 40 * 4082515 * 2
def baseEnd_4082515 : Nat := 2096292474190199874987361

theorem tailTrace_4082515 : CollatzResearch.WordTrace tailWord_4082515 prefixEnd_4082515 2096292474190199874987361 := by
  unfold tailWord_4082515
  simp only [CollatzResearch.WordTrace]
  refine ⟨148901554804752867897152999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99267703203168578598101999 148901554804752867897152999)
  ·
    refine ⟨223352332207129301845729499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148901554804752867897152999 223352332207129301845729499)
    ·
      refine ⟨335028498310693952768594249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223352332207129301845729499 335028498310693952768594249)
      ·
        refine ⟨251271373733020464576445687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 335028498310693952768594249 251271373733020464576445687)
        ·
          refine ⟨376907060599530696864668531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251271373733020464576445687 376907060599530696864668531)
          ·
            refine ⟨565360590899296045297002797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 376907060599530696864668531 565360590899296045297002797)
            ·
              refine ⟨212010221587236016986376049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 565360590899296045297002797 212010221587236016986376049)
              ·
                refine ⟨159007666190427012739782037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 212010221587236016986376049 159007666190427012739782037)
                ·
                  refine ⟨7453484352676266222177283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 159007666190427012739782037 7453484352676266222177283)
                  ·
                    refine ⟨11180226529014399333265925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7453484352676266222177283 11180226529014399333265925)
                    ·
                      refine ⟨2096292474190199874987361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11180226529014399333265925 2096292474190199874987361)
                      ·
                        rfl

theorem cell23_4082515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 6, 1, 4].length) (baseStart_4082515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4082515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4082515 prefixEnd_4082515 := by exact prefixLift 4082515
  have htrace : WordTrace (prefixWord ++ tailWord_4082515) baseStart_4082515 baseEnd_4082515 := by
    simpa [prefixWord, tailWord_4082515, baseEnd_4082515] using wordTrace_append hprefix tailTrace_4082515
  have hstable : (prefixWord ++ tailWord_4082515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4082515).length < 2 ^ (prefixWord ++ tailWord_4082515).sum := by decide
  have hdescent : baseEnd_4082515 < baseStart_4082515 := by decide
  rcases family_descends (prefixWord ++ tailWord_4082515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4082516 : List Nat := [2, 4, 1, 1, 4, 2, 1, 3, 5]
def baseStart_4082516 : Nat := 118140960795 + 4082516 * 2 ^ 59
def prefixEnd_4082516 : Nat := 4983230072969 + 3 ^ 40 * 4082516 * 2
def baseEnd_4082516 : Nat := 232921443074539374563873

theorem tailTrace_4082516 : CollatzResearch.WordTrace tailWord_4082516 prefixEnd_4082516 232921443074539374563873 := by
  unfold tailWord_4082516
  simp only [CollatzResearch.WordTrace]
  refine ⟨74450795638874622533969701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99267727518499496711959601 74450795638874622533969701)
  ·
    refine ⟨13959524182288991725119319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74450795638874622533969701 13959524182288991725119319)
    ·
      refine ⟨20939286273433487587678979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13959524182288991725119319 20939286273433487587678979)
      ·
        refine ⟨31408929410150231381518469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20939286273433487587678979 31408929410150231381518469)
        ·
          refine ⟨5889174264403168384034713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31408929410150231381518469 5889174264403168384034713)
          ·
            refine ⟨4416880698302376288026035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5889174264403168384034713 4416880698302376288026035)
            ·
              refine ⟨6625321047453564432039053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4416880698302376288026035 6625321047453564432039053)
              ·
                refine ⟨2484495392795086662014645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6625321047453564432039053 2484495392795086662014645)
                ·
                  refine ⟨232921443074539374563873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2484495392795086662014645 232921443074539374563873)
                  ·
                    rfl

theorem cell23_4082516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 1, 3, 5].length) (baseStart_4082516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4082516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4082516 prefixEnd_4082516 := by exact prefixLift 4082516
  have htrace : WordTrace (prefixWord ++ tailWord_4082516) baseStart_4082516 baseEnd_4082516 := by
    simpa [prefixWord, tailWord_4082516, baseEnd_4082516] using wordTrace_append hprefix tailTrace_4082516
  have hstable : (prefixWord ++ tailWord_4082516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4082516).length < 2 ^ (prefixWord ++ tailWord_4082516).sum := by decide
  have hdescent : baseEnd_4082516 < baseStart_4082516 := by decide
  rcases family_descends (prefixWord ++ tailWord_4082516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4082532 : List Nat := [2, 3, 1, 1, 4, 1, 1, 1, 4, 1, 4]
def baseStart_4082532 : Nat := 118140960795 + 4082532 * 2 ^ 59
def prefixEnd_4082532 : Nat := 4983230072969 + 3 ^ 40 * 4082532 * 2
def baseEnd_4082532 : Nat := 2096301203361326308474783

theorem tailTrace_4082532 : CollatzResearch.WordTrace tailWord_4082532 prefixEnd_4082532 2096301203361326308474783 := by
  unfold tailWord_4082532
  simp only [CollatzResearch.WordTrace]
  refine ⟨74451087422845639900260925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99268116563794186533681233 74451087422845639900260925)
  ·
    refine ⟨27919157783567114962597847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74451087422845639900260925 27919157783567114962597847)
    ·
      refine ⟨41878736675350672443896771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27919157783567114962597847 41878736675350672443896771)
      ·
        refine ⟨62818105013026008665845157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41878736675350672443896771 62818105013026008665845157)
        ·
          refine ⟨11778394689942376624845967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62818105013026008665845157 11778394689942376624845967)
          ·
            refine ⟨17667592034913564937268951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11778394689942376624845967 17667592034913564937268951)
            ·
              refine ⟨26501388052370347405903427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17667592034913564937268951 26501388052370347405903427)
              ·
                refine ⟨39752082078555521108855141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26501388052370347405903427 39752082078555521108855141)
                ·
                  refine ⟨7453515389729160207910339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39752082078555521108855141 7453515389729160207910339)
                  ·
                    refine ⟨11180273084593740311865509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7453515389729160207910339 11180273084593740311865509)
                    ·
                      refine ⟨2096301203361326308474783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11180273084593740311865509 2096301203361326308474783)
                      ·
                        rfl

theorem cell23_4082532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 1, 4, 1, 4].length) (baseStart_4082532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4082532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4082532 prefixEnd_4082532 := by exact prefixLift 4082532
  have htrace : WordTrace (prefixWord ++ tailWord_4082532) baseStart_4082532 baseEnd_4082532 := by
    simpa [prefixWord, tailWord_4082532, baseEnd_4082532] using wordTrace_append hprefix tailTrace_4082532
  have hstable : (prefixWord ++ tailWord_4082532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4082532).length < 2 ^ (prefixWord ++ tailWord_4082532).sum := by decide
  have hdescent : baseEnd_4082532 < baseStart_4082532 := by decide
  rcases family_descends (prefixWord ++ tailWord_4082532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4082569 : List Nat := [1, 2, 1, 1, 5, 3, 2, 1, 2, 2, 3]
def baseStart_4082569 : Nat := 118140960795 + 4082569 * 2 ^ 59
def prefixEnd_4082569 : Nat := 4983230072969 + 3 ^ 40 * 4082569 * 2
def baseEnd_4082569 : Nat := 2096320202145542663712113

theorem tailTrace_4082569 : CollatzResearch.WordTrace tailWord_4082569 prefixEnd_4082569 2096320202145542663712113 := by
  unfold tailWord_4082569
  simp only [CollatzResearch.WordTrace]
  refine ⟨148903524346557235119618761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99269016231038156746412507 148903524346557235119618761)
  ·
    refine ⟨111677643259917926339714071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148903524346557235119618761 111677643259917926339714071)
    ·
      refine ⟨167516464889876889509571107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111677643259917926339714071 167516464889876889509571107)
      ·
        refine ⟨251274697334815334264356661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167516464889876889509571107 251274697334815334264356661)
        ·
          refine ⟨23557002875138937587283437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 251274697334815334264356661 23557002875138937587283437)
          ·
            refine ⟨8833876078177101595231289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23557002875138937587283437 8833876078177101595231289)
            ·
              refine ⟨6625407058632826196423467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8833876078177101595231289 6625407058632826196423467)
              ·
                refine ⟨9938110587949239294635201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6625407058632826196423467 9938110587949239294635201)
                ·
                  refine ⟨7453582940961929470976401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9938110587949239294635201 7453582940961929470976401)
                  ·
                    refine ⟨5590187205721447103232301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7453582940961929470976401 5590187205721447103232301)
                    ·
                      refine ⟨2096320202145542663712113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5590187205721447103232301 2096320202145542663712113)
                      ·
                        rfl

theorem cell23_4082569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 2, 1, 2, 2, 3].length) (baseStart_4082569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4082569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4082569 prefixEnd_4082569 := by exact prefixLift 4082569
  have htrace : WordTrace (prefixWord ++ tailWord_4082569) baseStart_4082569 baseEnd_4082569 := by
    simpa [prefixWord, tailWord_4082569, baseEnd_4082569] using wordTrace_append hprefix tailTrace_4082569
  have hstable : (prefixWord ++ tailWord_4082569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4082569).length < 2 ^ (prefixWord ++ tailWord_4082569).sum := by decide
  have hdescent : baseEnd_4082569 < baseStart_4082569 := by decide
  rcases family_descends (prefixWord ++ tailWord_4082569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4082593 : List Nat := [1, 2, 3, 4, 1, 1, 4, 2, 1, 4]
def baseStart_4082593 : Nat := 118140960795 + 4082593 * 2 ^ 59
def prefixEnd_4082593 : Nat := 4983230072969 + 3 ^ 40 * 4082593 * 2
def baseEnd_4082593 : Nat := 698777508560416856604001

theorem tailTrace_4082593 : CollatzResearch.WordTrace tailWord_4082593 prefixEnd_4082593 698777508560416856604001 := by
  unfold tailWord_4082593
  simp only [CollatzResearch.WordTrace]
  refine ⟨148904399698470287218492433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99269599798980191478994955 148904399698470287218492433)
  ·
    refine ⟨111678299773852715413869325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148904399698470287218492433 111678299773852715413869325)
    ·
      refine ⟨41879362415194768280200997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111678299773852715413869325 41879362415194768280200997)
      ·
        refine ⟨7852380452849019052537687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41879362415194768280200997 7852380452849019052537687)
        ·
          refine ⟨11778570679273528578806531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7852380452849019052537687 11778570679273528578806531)
          ·
            refine ⟨17667856018910292868209797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11778570679273528578806531 17667856018910292868209797)
            ·
              refine ⟨3312723003545679912789337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17667856018910292868209797 3312723003545679912789337)
              ·
                refine ⟨2484542252659259934592003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3312723003545679912789337 2484542252659259934592003)
                ·
                  refine ⟨3726813378988889901888005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2484542252659259934592003 3726813378988889901888005)
                  ·
                    refine ⟨698777508560416856604001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3726813378988889901888005 698777508560416856604001)
                    ·
                      rfl

theorem cell23_4082593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 4, 2, 1, 4].length) (baseStart_4082593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4082593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4082593 prefixEnd_4082593 := by exact prefixLift 4082593
  have htrace : WordTrace (prefixWord ++ tailWord_4082593) baseStart_4082593 baseEnd_4082593 := by
    simpa [prefixWord, tailWord_4082593, baseEnd_4082593] using wordTrace_append hprefix tailTrace_4082593
  have hstable : (prefixWord ++ tailWord_4082593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4082593).length < 2 ^ (prefixWord ++ tailWord_4082593).sum := by decide
  have hdescent : baseEnd_4082593 < baseStart_4082593 := by decide
  rcases family_descends (prefixWord ++ tailWord_4082593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4082639 : List Nat := [1, 1, 2, 1, 1, 7, 1, 3, 1, 1, 4]
def baseStart_4082639 : Nat := 118140960795 + 4082639 * 2 ^ 59
def prefixEnd_4082639 : Nat := 4983230072969 + 3 ^ 40 * 4082639 * 2
def baseEnd_4082639 : Nat := 2096356145791357389836791

theorem tailTrace_4082639 : CollatzResearch.WordTrace tailWord_4082639 prefixEnd_4082639 2096356145791357389836791 := by
  unfold tailWord_4082639
  simp only [CollatzResearch.WordTrace]
  refine ⟨148906077456303637074666971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99270718304202424716444647 148906077456303637074666971)
  ·
    refine ⟨223359116184455455612000457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148906077456303637074666971 223359116184455455612000457)
    ·
      refine ⟨167519337138341591709000343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223359116184455455612000457 167519337138341591709000343)
      ·
        refine ⟨251279005707512387563500515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167519337138341591709000343 251279005707512387563500515)
        ·
          refine ⟨376918508561268581345250773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251279005707512387563500515 376918508561268581345250773)
          ·
            refine ⟨8834027544404732375279315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 376918508561268581345250773 8834027544404732375279315)
            ·
              refine ⟨13251041316607098562918973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8834027544404732375279315 13251041316607098562918973)
              ·
                refine ⟨4969140493727661961094615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13251041316607098562918973 4969140493727661961094615)
                ·
                  refine ⟨7453710740591492941641923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4969140493727661961094615 7453710740591492941641923)
                  ·
                    refine ⟨11180566110887239412462885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7453710740591492941641923 11180566110887239412462885)
                    ·
                      refine ⟨2096356145791357389836791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11180566110887239412462885 2096356145791357389836791)
                      ·
                        rfl

theorem cell23_4082639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 3, 1, 1, 4].length) (baseStart_4082639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4082639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4082639 prefixEnd_4082639 := by exact prefixLift 4082639
  have htrace : WordTrace (prefixWord ++ tailWord_4082639) baseStart_4082639 baseEnd_4082639 := by
    simpa [prefixWord, tailWord_4082639, baseEnd_4082639] using wordTrace_append hprefix tailTrace_4082639
  have hstable : (prefixWord ++ tailWord_4082639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4082639).length < 2 ^ (prefixWord ++ tailWord_4082639).sum := by decide
  have hdescent : baseEnd_4082639 < baseStart_4082639 := by decide
  rcases family_descends (prefixWord ++ tailWord_4082639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4082649 : List Nat := [1, 2, 1, 2, 5, 2, 1, 1, 4, 4]
def baseStart_4082649 : Nat := 118140960795 + 4082649 * 2 ^ 59
def prefixEnd_4082649 : Nat := 4983230072969 + 3 ^ 40 * 4082649 * 2
def baseEnd_4082649 : Nat := 698787093532634116903915

theorem tailTrace_4082649 : CollatzResearch.WordTrace tailWord_4082649 prefixEnd_4082649 698787093532634116903915 := by
  unfold tailWord_4082649
  simp only [CollatzResearch.WordTrace]
  refine ⟨148906442186267408782531001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99270961457511605855020667 148906442186267408782531001)
  ·
    refine ⟨111679831639700556586898251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148906442186267408782531001 111679831639700556586898251)
    ·
      refine ⟨167519747459550834880347377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111679831639700556586898251 167519747459550834880347377)
      ·
        refine ⟨125639810594663126160260533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167519747459550834880347377 125639810594663126160260533)
        ·
          refine ⟨11778732243249668077524425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 125639810594663126160260533 11778732243249668077524425)
          ·
            refine ⟨8834049182437251058143319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11778732243249668077524425 8834049182437251058143319)
            ·
              refine ⟨13251073773655876587214979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8834049182437251058143319 13251073773655876587214979)
              ·
                refine ⟨19876610660483814880822469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13251073773655876587214979 19876610660483814880822469)
                ·
                  refine ⟨3726864498840715290154213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19876610660483814880822469 3726864498840715290154213)
                  ·
                    refine ⟨698787093532634116903915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3726864498840715290154213 698787093532634116903915)
                    ·
                      rfl

theorem cell23_4082649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 1, 4, 4].length) (baseStart_4082649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4082649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4082649 prefixEnd_4082649 := by exact prefixLift 4082649
  have htrace : WordTrace (prefixWord ++ tailWord_4082649) baseStart_4082649 baseEnd_4082649 := by
    simpa [prefixWord, tailWord_4082649, baseEnd_4082649] using wordTrace_append hprefix tailTrace_4082649
  have hstable : (prefixWord ++ tailWord_4082649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4082649).length < 2 ^ (prefixWord ++ tailWord_4082649).sum := by decide
  have hdescent : baseEnd_4082649 < baseStart_4082649 := by decide
  rcases family_descends (prefixWord ++ tailWord_4082649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4082723 : List Nat := [1, 1, 1, 4, 3, 2, 4, 1, 2, 1, 3]
def baseStart_4082723 : Nat := 118140960795 + 4082723 * 2 ^ 59
def prefixEnd_4082723 : Nat := 4983230072969 + 3 ^ 40 * 4082723 * 2
def baseEnd_4082723 : Nat := 2096399278166335061186405

theorem tailTrace_4082723 : CollatzResearch.WordTrace tailWord_4082723 prefixEnd_4082723 2096399278166335061186405 := by
  unfold tailWord_4082723
  simp only [CollatzResearch.WordTrace]
  refine ⟨148909141187999319420724823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99272760791999546280483215 148909141187999319420724823)
  ·
    refine ⟨223363711781998979131087235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148909141187999319420724823 223363711781998979131087235)
    ·
      refine ⟨335045567672998468696630853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223363711781998979131087235 335045567672998468696630853)
      ·
        refine ⟨62821043938687212880618285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 335045567672998468696630853 62821043938687212880618285)
        ·
          refine ⟨23557891477007704830231857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62821043938687212880618285 23557891477007704830231857)
          ·
            refine ⟨17668418607755778622673893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23557891477007704830231857 17668418607755778622673893)
            ·
              refine ⟨3312828488954208491751355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17668418607755778622673893 3312828488954208491751355)
              ·
                refine ⟨4969242733431312737627033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3312828488954208491751355 4969242733431312737627033)
                ·
                  refine ⟨3726932050073484553220275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4969242733431312737627033 3726932050073484553220275)
                  ·
                    refine ⟨5590398075110226829830413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3726932050073484553220275 5590398075110226829830413)
                    ·
                      refine ⟨2096399278166335061186405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5590398075110226829830413 2096399278166335061186405)
                      ·
                        rfl

theorem cell23_4082723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 4, 1, 2, 1, 3].length) (baseStart_4082723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4082723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4082723 prefixEnd_4082723 := by exact prefixLift 4082723
  have htrace : WordTrace (prefixWord ++ tailWord_4082723) baseStart_4082723 baseEnd_4082723 := by
    simpa [prefixWord, tailWord_4082723, baseEnd_4082723] using wordTrace_append hprefix tailTrace_4082723
  have hstable : (prefixWord ++ tailWord_4082723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4082723).length < 2 ^ (prefixWord ++ tailWord_4082723).sum := by decide
  have hdescent : baseEnd_4082723 < baseStart_4082723 := by decide
  rcases family_descends (prefixWord ++ tailWord_4082723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4082732 : List Nat := [2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 5]
def baseStart_4082732 : Nat := 118140960795 + 4082732 * 2 ^ 59
def prefixEnd_4082732 : Nat := 4983230072969 + 3 ^ 40 * 4082732 * 2
def baseEnd_4082732 : Nat := 2096403899492225525973863

theorem tailTrace_4082732 : CollatzResearch.WordTrace tailWord_4082732 prefixEnd_4082732 2096403899492225525973863 := by
  unfold tailWord_4082732
  simp only [CollatzResearch.WordTrace]
  refine ⟨74454734722483356978901225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99272979629977809305201633 74454734722483356978901225)
  ·
    refine ⟨55841051041862517734175919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74454734722483356978901225 55841051041862517734175919)
    ·
      refine ⟨83761576562793776601263879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55841051041862517734175919 83761576562793776601263879)
      ·
        refine ⟨125642364844190664901895819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83761576562793776601263879 125642364844190664901895819)
        ·
          refine ⟨188463547266285997352843729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125642364844190664901895819 188463547266285997352843729)
          ·
            refine ⟨141347660449714498014632797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188463547266285997352843729 141347660449714498014632797)
            ·
              refine ⟨53005372668642936755487299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141347660449714498014632797 53005372668642936755487299)
              ·
                refine ⟨79508059002964405133230949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53005372668642936755487299 79508059002964405133230949)
                ·
                  refine ⟨14907761063055825962480803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79508059002964405133230949 14907761063055825962480803)
                  ·
                    refine ⟨22361641594583738943721205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14907761063055825962480803 22361641594583738943721205)
                    ·
                      refine ⟨2096403899492225525973863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22361641594583738943721205 2096403899492225525973863)
                      ·
                        rfl

theorem cell23_4082732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 5].length) (baseStart_4082732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4082732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4082732 prefixEnd_4082732 := by exact prefixLift 4082732
  have htrace : WordTrace (prefixWord ++ tailWord_4082732) baseStart_4082732 baseEnd_4082732 := by
    simpa [prefixWord, tailWord_4082732, baseEnd_4082732] using wordTrace_append hprefix tailTrace_4082732
  have hstable : (prefixWord ++ tailWord_4082732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4082732).length < 2 ^ (prefixWord ++ tailWord_4082732).sum := by decide
  have hdescent : baseEnd_4082732 < baseStart_4082732 := by decide
  rcases family_descends (prefixWord ++ tailWord_4082732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4082746 : List Nat := [3, 1, 1, 1, 3, 1, 2, 1, 6, 2, 2]
def baseStart_4082746 : Nat := 118140960795 + 4082746 * 2 ^ 59
def prefixEnd_4082746 : Nat := 4983230072969 + 3 ^ 40 * 4082746 * 2
def baseEnd_4082746 : Nat := 2096411088221388471198799

theorem tailTrace_4082746 : CollatzResearch.WordTrace tailWord_4082746 prefixEnd_4082746 2096411088221388471198799 := by
  unfold tailWord_4082746
  simp only [CollatzResearch.WordTrace]
  refine ⟨37227495016728998587203023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99273320044610662899208061 37227495016728998587203023)
  ·
    refine ⟨55841242525093497880804535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37227495016728998587203023 55841242525093497880804535)
    ·
      refine ⟨83761863787640246821206803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55841242525093497880804535 83761863787640246821206803)
      ·
        refine ⟨125642795681460370231810205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83761863787640246821206803 125642795681460370231810205)
        ·
          refine ⟨47116048380547638836928827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125642795681460370231810205 47116048380547638836928827)
          ·
            refine ⟨70674072570821458255393241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47116048380547638836928827 70674072570821458255393241)
            ·
              refine ⟨53005554428116093691544931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70674072570821458255393241 53005554428116093691544931)
              ·
                refine ⟨79508331642174140537317397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53005554428116093691544931 79508331642174140537317397)
                ·
                  refine ⟨3726953045726912837686753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 79508331642174140537317397 3726953045726912837686753)
                  ·
                    refine ⟨2795214784295184628265065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3726953045726912837686753 2795214784295184628265065)
                    ·
                      refine ⟨2096411088221388471198799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2795214784295184628265065 2096411088221388471198799)
                      ·
                        rfl

theorem cell23_4082746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 1, 6, 2, 2].length) (baseStart_4082746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4082746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4082746 prefixEnd_4082746 := by exact prefixLift 4082746
  have htrace : WordTrace (prefixWord ++ tailWord_4082746) baseStart_4082746 baseEnd_4082746 := by
    simpa [prefixWord, tailWord_4082746, baseEnd_4082746] using wordTrace_append hprefix tailTrace_4082746
  have hstable : (prefixWord ++ tailWord_4082746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4082746).length < 2 ^ (prefixWord ++ tailWord_4082746).sum := by decide
  have hdescent : baseEnd_4082746 < baseStart_4082746 := by decide
  rcases family_descends (prefixWord ++ tailWord_4082746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4082749 : List Nat := [1, 4, 1, 3, 1, 2, 2, 1, 2, 1, 5]
def baseStart_4082749 : Nat := 118140960795 + 4082749 * 2 ^ 59
def prefixEnd_4082749 : Nat := 4983230072969 + 3 ^ 40 * 4082749 * 2
def baseEnd_4082749 : Nat := 2096412628663351959461285

theorem tailTrace_4082749 : CollatzResearch.WordTrace tailWord_4082749 prefixEnd_4082749 2096412628663351959461285 := by
  unfold tailWord_4082749
  simp only [CollatzResearch.WordTrace]
  refine ⟨148910089485905125861171301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99273392990603417240780867 148910089485905125861171301)
  ·
    refine ⟨27920641778607211098969619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 148910089485905125861171301 27920641778607211098969619)
    ·
      refine ⟨41880962667910816648454429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27920641778607211098969619 41880962667910816648454429)
      ·
        refine ⟨15705361000466556243170411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41880962667910816648454429 15705361000466556243170411)
        ·
          refine ⟨23558041500699834364755617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15705361000466556243170411 23558041500699834364755617)
          ·
            refine ⟨17668531125524875773566713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23558041500699834364755617 17668531125524875773566713)
            ·
              refine ⟨13251398344143656830175035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17668531125524875773566713 13251398344143656830175035)
              ·
                refine ⟨19877097516215485245262553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13251398344143656830175035 19877097516215485245262553)
                ·
                  refine ⟨14907823137161613933946915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19877097516215485245262553 14907823137161613933946915)
                  ·
                    refine ⟨22361734705742420900920373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14907823137161613933946915 22361734705742420900920373)
                    ·
                      refine ⟨2096412628663351959461285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22361734705742420900920373 2096412628663351959461285)
                      ·
                        rfl

theorem cell23_4082749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_4082749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4082749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4082749 prefixEnd_4082749 := by exact prefixLift 4082749
  have htrace : WordTrace (prefixWord ++ tailWord_4082749) baseStart_4082749 baseEnd_4082749 := by
    simpa [prefixWord, tailWord_4082749, baseEnd_4082749] using wordTrace_append hprefix tailTrace_4082749
  have hstable : (prefixWord ++ tailWord_4082749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4082749).length < 2 ^ (prefixWord ++ tailWord_4082749).sum := by decide
  have hdescent : baseEnd_4082749 < baseStart_4082749 := by decide
  rcases family_descends (prefixWord ++ tailWord_4082749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4082762 : List Nat := [3, 1, 2, 1, 1, 2, 2, 1, 1, 2, 7]
def baseStart_4082762 : Nat := 118140960795 + 4082762 * 2 ^ 59
def prefixEnd_4082762 : Nat := 4983230072969 + 3 ^ 40 * 4082762 * 2
def baseEnd_4082762 : Nat := 2096419303911860408598725

theorem tailTrace_4082762 : CollatzResearch.WordTrace tailWord_4082762 prefixEnd_4082762 2096419303911860408598725 := by
  unfold tailWord_4082762
  simp only [CollatzResearch.WordTrace]
  refine ⟨37227640908714507270348635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99273709089905352720929693 37227640908714507270348635)
  ·
    refine ⟨55841461363071760905522953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37227640908714507270348635 55841461363071760905522953)
    ·
      refine ⟨41881096022303820679142215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55841461363071760905522953 41881096022303820679142215)
      ·
        refine ⟨62821644033455731018713323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41881096022303820679142215 62821644033455731018713323)
        ·
          refine ⟨94232466050183596528069985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62821644033455731018713323 94232466050183596528069985)
          ·
            refine ⟨70674349537637697396052489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94232466050183596528069985 70674349537637697396052489)
            ·
              refine ⟨53005762153228273047039367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70674349537637697396052489 53005762153228273047039367)
              ·
                refine ⟨79508643229842409570559051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53005762153228273047039367 79508643229842409570559051)
                ·
                  refine ⟨119262964844763614355838577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79508643229842409570559051 119262964844763614355838577)
                  ·
                    refine ⟨89447223633572710766878933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 119262964844763614355838577 89447223633572710766878933)
                    ·
                      refine ⟨2096419303911860408598725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 89447223633572710766878933 2096419303911860408598725)
                      ·
                        rfl

theorem cell23_4082762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 1, 1, 2, 7].length) (baseStart_4082762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4082762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4082762 prefixEnd_4082762 := by exact prefixLift 4082762
  have htrace : WordTrace (prefixWord ++ tailWord_4082762) baseStart_4082762 baseEnd_4082762 := by
    simpa [prefixWord, tailWord_4082762, baseEnd_4082762] using wordTrace_append hprefix tailTrace_4082762
  have hstable : (prefixWord ++ tailWord_4082762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4082762).length < 2 ^ (prefixWord ++ tailWord_4082762).sum := by decide
  have hdescent : baseEnd_4082762 < baseStart_4082762 := by decide
  rcases family_descends (prefixWord ++ tailWord_4082762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4082786 : List Nat := [3, 3, 2, 2, 1, 2, 1, 2, 7]
def baseStart_4082786 : Nat := 118140960795 + 4082786 * 2 ^ 59
def prefixEnd_4082786 : Nat := 4983230072969 + 3 ^ 40 * 4082786 * 2
def baseEnd_4082786 : Nat := 232936847494174257188735

theorem tailTrace_4082786 : CollatzResearch.WordTrace tailWord_4082786 prefixEnd_4082786 232936847494174257188735 := by
  unfold tailWord_4082786
  simp only [CollatzResearch.WordTrace]
  refine ⟨37227859746692770295067053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99274292657847387453512141 37227859746692770295067053)
  ·
    refine ⟨13960447405009788860650145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37227859746692770295067053 13960447405009788860650145)
    ·
      refine ⟨10470335553757341645487609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13960447405009788860650145 10470335553757341645487609)
      ·
        refine ⟨7852751665318006234115707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10470335553757341645487609 7852751665318006234115707)
        ·
          refine ⟨11779127497977009351173561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7852751665318006234115707 11779127497977009351173561)
          ·
            refine ⟨8834345623482757013380171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11779127497977009351173561 8834345623482757013380171)
            ·
              refine ⟨13251518435224135520070257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8834345623482757013380171 13251518435224135520070257)
              ·
                refine ⟨9938638826418101640052693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13251518435224135520070257 9938638826418101640052693)
                ·
                  refine ⟨232936847494174257188735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9938638826418101640052693 232936847494174257188735)
                  ·
                    rfl

theorem cell23_4082786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 2, 7].length) (baseStart_4082786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4082786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4082786 prefixEnd_4082786 := by exact prefixLift 4082786
  have htrace : WordTrace (prefixWord ++ tailWord_4082786) baseStart_4082786 baseEnd_4082786 := by
    simpa [prefixWord, tailWord_4082786, baseEnd_4082786] using wordTrace_append hprefix tailTrace_4082786
  have hstable : (prefixWord ++ tailWord_4082786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4082786).length < 2 ^ (prefixWord ++ tailWord_4082786).sum := by decide
  have hdescent : baseEnd_4082786 < baseStart_4082786 := by decide
  rcases family_descends (prefixWord ++ tailWord_4082786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4082814 : List Nat := [4, 2, 4, 1, 1, 1, 1, 1, 4, 2, 2]
def baseStart_4082814 : Nat := 118140960795 + 4082814 * 2 ^ 59
def prefixEnd_4082814 : Nat := 4983230072969 + 3 ^ 40 * 4082814 * 2
def baseEnd_4082814 : Nat := 2096446004905894205148487

theorem tailTrace_4082814 : CollatzResearch.WordTrace tailWord_4082814 prefixEnd_4082814 2096446004905894205148487 := by
  unfold tailWord_4082814
  simp only [CollatzResearch.WordTrace]
  refine ⟨18614057528833705245285937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99274973487113094641524997 18614057528833705245285937)
  ·
    refine ⟨13960543146625278933964453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18614057528833705245285937 13960543146625278933964453)
    ·
      refine ⟨2617601839992239800118335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13960543146625278933964453 2617601839992239800118335)
      ·
        refine ⟨3926402759988359700177503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2617601839992239800118335 3926402759988359700177503)
        ·
          refine ⟨5889604139982539550266255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3926402759988359700177503 5889604139982539550266255)
          ·
            refine ⟨8834406209973809325399383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5889604139982539550266255 8834406209973809325399383)
            ·
              refine ⟨13251609314960713988099075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8834406209973809325399383 13251609314960713988099075)
              ·
                refine ⟨19877413972441070982148613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13251609314960713988099075 19877413972441070982148613)
                ·
                  refine ⟨3727015119832700809152865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19877413972441070982148613 3727015119832700809152865)
                  ·
                    refine ⟨2795261339874525606864649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3727015119832700809152865 2795261339874525606864649)
                    ·
                      refine ⟨2096446004905894205148487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2795261339874525606864649 2096446004905894205148487)
                      ·
                        rfl

theorem cell23_4082814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_4082814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4082814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4082814 prefixEnd_4082814 := by exact prefixLift 4082814
  have htrace : WordTrace (prefixWord ++ tailWord_4082814) baseStart_4082814 baseEnd_4082814 := by
    simpa [prefixWord, tailWord_4082814, baseEnd_4082814] using wordTrace_append hprefix tailTrace_4082814
  have hstable : (prefixWord ++ tailWord_4082814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4082814).length < 2 ^ (prefixWord ++ tailWord_4082814).sum := by decide
  have hdescent : baseEnd_4082814 < baseStart_4082814 := by decide
  rcases family_descends (prefixWord ++ tailWord_4082814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4082819 : List Nat := [1, 1, 1, 3, 3, 2, 2, 1, 4, 1, 4]
def baseStart_4082819 : Nat := 118140960795 + 4082819 * 2 ^ 59
def prefixEnd_4082819 : Nat := 4983230072969 + 3 ^ 40 * 4082819 * 2
def baseEnd_4082819 : Nat := 2096448572309166685585963

theorem tailTrace_4082819 : CollatzResearch.WordTrace tailWord_4082819 prefixEnd_4082819 2096448572309166685585963 := by
  unfold tailWord_4082819
  simp only [CollatzResearch.WordTrace]
  refine ⟨148912642595651527816219511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99275095063767685210813007 148912642595651527816219511)
  ·
    refine ⟨223368963893477291724329267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148912642595651527816219511 223368963893477291724329267)
    ·
      refine ⟨335053445840215937586493901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223368963893477291724329267 335053445840215937586493901)
      ·
        refine ⟨125645042190080976594935213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 335053445840215937586493901 125645042190080976594935213)
        ·
          refine ⟨47116890821280366223100705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125645042190080976594935213 47116890821280366223100705)
          ·
            refine ⟨35337668115960274667325529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47116890821280366223100705 35337668115960274667325529)
            ·
              refine ⟨26503251086970206000494147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35337668115960274667325529 26503251086970206000494147)
              ·
                refine ⟨39754876630455309000741221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26503251086970206000494147 39754876630455309000741221)
                ·
                  refine ⟨7454039368210370437638979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39754876630455309000741221 7454039368210370437638979)
                  ·
                    refine ⟨11181059052315555656458469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7454039368210370437638979 11181059052315555656458469)
                    ·
                      refine ⟨2096448572309166685585963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11181059052315555656458469 2096448572309166685585963)
                      ·
                        rfl

theorem cell23_4082819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 1, 4, 1, 4].length) (baseStart_4082819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4082819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4082819 prefixEnd_4082819 := by exact prefixLift 4082819
  have htrace : WordTrace (prefixWord ++ tailWord_4082819) baseStart_4082819 baseEnd_4082819 := by
    simpa [prefixWord, tailWord_4082819, baseEnd_4082819] using wordTrace_append hprefix tailTrace_4082819
  have hstable : (prefixWord ++ tailWord_4082819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4082819).length < 2 ^ (prefixWord ++ tailWord_4082819).sum := by decide
  have hdescent : baseEnd_4082819 < baseStart_4082819 := by decide
  rcases family_descends (prefixWord ++ tailWord_4082819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4082849 : List Nat := [1, 2, 3, 3, 1, 1, 1, 1, 2, 4, 4]
def baseStart_4082849 : Nat := 118140960795 + 4082849 * 2 ^ 59
def prefixEnd_4082849 : Nat := 4983230072969 + 3 ^ 40 * 4082849 * 2
def baseEnd_4082849 : Nat := 2096463976728801568210825

theorem tailTrace_4082849 : CollatzResearch.WordTrace tailWord_4082849 prefixEnd_4082849 2096463976728801568210825 := by
  unfold tailWord_4082849
  simp only [CollatzResearch.WordTrace]
  refine ⟨148913736785542842939811601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99275824523695228626541067 148913736785542842939811601)
  ·
    refine ⟨111685302589157132204858701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148913736785542842939811601 111685302589157132204858701)
    ·
      refine ⟨41881988470933924576822013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111685302589157132204858701 41881988470933924576822013)
      ·
        refine ⟨15705745676600221716308255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41881988470933924576822013 15705745676600221716308255)
        ·
          refine ⟨23558618514900332574462383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15705745676600221716308255 23558618514900332574462383)
          ·
            refine ⟨35337927772350498861693575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23558618514900332574462383 35337927772350498861693575)
            ·
              refine ⟨53006891658525748292540363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35337927772350498861693575 53006891658525748292540363)
              ·
                refine ⟨79510337487788622438810545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53006891658525748292540363 79510337487788622438810545)
                ·
                  refine ⟨59632753115841466829107909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79510337487788622438810545 59632753115841466829107909)
                  ·
                    refine ⟨11181141209220275030457733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59632753115841466829107909 11181141209220275030457733)
                    ·
                      refine ⟨2096463976728801568210825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11181141209220275030457733 2096463976728801568210825)
                      ·
                        rfl

theorem cell23_4082849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_4082849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4082849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4082849 prefixEnd_4082849 := by exact prefixLift 4082849
  have htrace : WordTrace (prefixWord ++ tailWord_4082849) baseStart_4082849 baseEnd_4082849 := by
    simpa [prefixWord, tailWord_4082849, baseEnd_4082849] using wordTrace_append hprefix tailTrace_4082849
  have hstable : (prefixWord ++ tailWord_4082849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4082849).length < 2 ^ (prefixWord ++ tailWord_4082849).sum := by decide
  have hdescent : baseEnd_4082849 < baseStart_4082849 := by decide
  rcases family_descends (prefixWord ++ tailWord_4082849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4082863 : List Nat := [1, 1, 2, 1, 2, 3, 5, 3, 1, 4]
def baseStart_4082863 : Nat := 118140960795 + 4082863 * 2 ^ 59
def prefixEnd_4082863 : Nat := 4983230072969 + 3 ^ 40 * 4082863 * 2
def baseEnd_4082863 : Nat := 698823721819321504478587

theorem tailTrace_4082863 : CollatzResearch.WordTrace tailWord_4082863 prefixEnd_4082863 698823721819321504478587 := by
  unfold tailWord_4082863
  simp only [CollatzResearch.WordTrace]
  refine ⟨148914247407492123330821243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99276164938328082220547495 148914247407492123330821243)
  ·
    refine ⟨223371371111238184996231865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148914247407492123330821243 223371371111238184996231865)
    ·
      refine ⟨167528528333428638747173899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223371371111238184996231865 167528528333428638747173899)
      ·
        refine ⟨251292792500142958120760849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167528528333428638747173899 251292792500142958120760849)
        ·
          refine ⟨188469594375107218590570637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 251292792500142958120760849 188469594375107218590570637)
          ·
            refine ⟨70676097890665206971463989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 188469594375107218590570637 70676097890665206971463989)
            ·
              refine ⟨6625884177249863153574749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70676097890665206971463989 6625884177249863153574749)
              ·
                refine ⟨2484706566468698682590531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6625884177249863153574749 2484706566468698682590531)
                ·
                  refine ⟨3727059849703048023885797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2484706566468698682590531 3727059849703048023885797)
                  ·
                    refine ⟨698823721819321504478587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3727059849703048023885797 698823721819321504478587)
                    ·
                      rfl

theorem cell23_4082863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 5, 3, 1, 4].length) (baseStart_4082863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4082863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4082863 prefixEnd_4082863 := by exact prefixLift 4082863
  have htrace : WordTrace (prefixWord ++ tailWord_4082863) baseStart_4082863 baseEnd_4082863 := by
    simpa [prefixWord, tailWord_4082863, baseEnd_4082863] using wordTrace_append hprefix tailTrace_4082863
  have hstable : (prefixWord ++ tailWord_4082863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4082863).length < 2 ^ (prefixWord ++ tailWord_4082863).sum := by decide
  have hdescent : baseEnd_4082863 < baseStart_4082863 := by decide
  rcases family_descends (prefixWord ++ tailWord_4082863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4082880 : List Nat := [2, 1, 1, 2, 7, 1, 1, 1, 3, 4]
def baseStart_4082880 : Nat := 118140960795 + 4082880 * 2 ^ 59
def prefixEnd_4082880 : Nat := 4983230072969 + 3 ^ 40 * 4082880 * 2
def baseEnd_4082880 : Nat := 698826631543030315641061

theorem tailTrace_4082880 : CollatzResearch.WordTrace tailWord_4082880 prefixEnd_4082880 698826631543030315641061 := by
  unfold tailWord_4082880
  simp only [CollatzResearch.WordTrace]
  refine ⟨74457433724215267617095047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99276578298953690156126729 74457433724215267617095047)
  ·
    refine ⟨111686150586322901425642571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74457433724215267617095047 111686150586322901425642571)
    ·
      refine ⟨167529225879484352138463857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111686150586322901425642571 167529225879484352138463857)
      ·
        refine ⟨125646919409613264103847893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167529225879484352138463857 125646919409613264103847893)
        ·
          refine ⟨2944849673662810877433935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 125646919409613264103847893 2944849673662810877433935)
          ·
            refine ⟨4417274510494216316150903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2944849673662810877433935 4417274510494216316150903)
            ·
              refine ⟨6625911765741324474226355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4417274510494216316150903 6625911765741324474226355)
              ·
                refine ⟨9938867648611986711339533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6625911765741324474226355 9938867648611986711339533)
                ·
                  refine ⟨3727075368229495016752325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9938867648611986711339533 3727075368229495016752325)
                  ·
                    refine ⟨698826631543030315641061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3727075368229495016752325 698826631543030315641061)
                    ·
                      rfl

theorem cell23_4082880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 1, 1, 3, 4].length) (baseStart_4082880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4082880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4082880 prefixEnd_4082880 := by exact prefixLift 4082880
  have htrace : WordTrace (prefixWord ++ tailWord_4082880) baseStart_4082880 baseEnd_4082880 := by
    simpa [prefixWord, tailWord_4082880, baseEnd_4082880] using wordTrace_append hprefix tailTrace_4082880
  have hstable : (prefixWord ++ tailWord_4082880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4082880).length < 2 ^ (prefixWord ++ tailWord_4082880).sum := by decide
  have hdescent : baseEnd_4082880 < baseStart_4082880 := by decide
  rcases family_descends (prefixWord ++ tailWord_4082880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4082913 : List Nat := [1, 2, 3, 1, 3, 2, 1, 3, 2, 3, 2]
def baseStart_4082913 : Nat := 118140960795 + 4082913 * 2 ^ 59
def prefixEnd_4082913 : Nat := 4983230072969 + 3 ^ 40 * 4082913 * 2
def baseEnd_4082913 : Nat := 2096496839490689317810531

theorem tailTrace_4082913 : CollatzResearch.WordTrace tailWord_4082913 prefixEnd_4082913 2096496839490689317810531 := by
  unfold tailWord_4082913
  simp only [CollatzResearch.WordTrace]
  refine ⟨148916071057310981870141393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99277380704873987913427595 148916071057310981870141393)
  ·
    refine ⟨111687053292983236402606045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148916071057310981870141393 111687053292983236402606045)
    ·
      refine ⟨41882644984868713650977267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111687053292983236402606045 41882644984868713650977267)
      ·
        refine ⟨62823967477303070476465901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41882644984868713650977267 62823967477303070476465901)
        ·
          refine ⟨23558987803988651428674713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62823967477303070476465901 23558987803988651428674713)
          ·
            refine ⟨17669240852991488571506035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23558987803988651428674713 17669240852991488571506035)
            ·
              refine ⟨26503861279487232857259053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17669240852991488571506035 26503861279487232857259053)
              ·
                refine ⟨9938947979807712321472145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26503861279487232857259053 9938947979807712321472145)
                ·
                  refine ⟨7454210984855784241104109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9938947979807712321472145 7454210984855784241104109)
                  ·
                    refine ⟨2795329119320919090414041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7454210984855784241104109 2795329119320919090414041)
                    ·
                      refine ⟨2096496839490689317810531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2795329119320919090414041 2096496839490689317810531)
                      ·
                        rfl

theorem cell23_4082913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 3, 2, 3, 2].length) (baseStart_4082913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4082913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4082913 prefixEnd_4082913 := by exact prefixLift 4082913
  have htrace : WordTrace (prefixWord ++ tailWord_4082913) baseStart_4082913 baseEnd_4082913 := by
    simpa [prefixWord, tailWord_4082913, baseEnd_4082913] using wordTrace_append hprefix tailTrace_4082913
  have hstable : (prefixWord ++ tailWord_4082913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4082913).length < 2 ^ (prefixWord ++ tailWord_4082913).sum := by decide
  have hdescent : baseEnd_4082913 < baseStart_4082913 := by decide
  rcases family_descends (prefixWord ++ tailWord_4082913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4082920 : List Nat := [2, 1, 4, 1, 2, 1, 2, 5, 1, 1, 3]
def baseStart_4082920 : Nat := 118140960795 + 4082920 * 2 ^ 59
def prefixEnd_4082920 : Nat := 4983230072969 + 3 ^ 40 * 4082920 * 2
def baseEnd_4082920 : Nat := 2096500433855270790422999

theorem tailTrace_4082920 : CollatzResearch.WordTrace tailWord_4082920 prefixEnd_4082920 2096500433855270790422999 := by
  unfold tailWord_4082920
  simp only [CollatzResearch.WordTrace]
  refine ⟨74458163184142811032823107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99277550912190414710430809 74458163184142811032823107)
  ·
    refine ⟨111687244776214216549234661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74458163184142811032823107 111687244776214216549234661)
    ·
      refine ⟨20941358395540165602981499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111687244776214216549234661 20941358395540165602981499)
      ·
        refine ⟨31412037593310248404472249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20941358395540165602981499 31412037593310248404472249)
        ·
          refine ⟨23559028194982686303354187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31412037593310248404472249 23559028194982686303354187)
          ·
            refine ⟨35338542292474029455031281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23559028194982686303354187 35338542292474029455031281)
            ·
              refine ⟨26503906719355522091273461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35338542292474029455031281 26503906719355522091273461)
              ·
                refine ⟨2484741254939580196056887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26503906719355522091273461 2484741254939580196056887)
                ·
                  refine ⟨3727111882409370294085331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2484741254939580196056887 3727111882409370294085331)
                  ·
                    refine ⟨5590667823614055441127997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3727111882409370294085331 5590667823614055441127997)
                    ·
                      refine ⟨2096500433855270790422999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5590667823614055441127997 2096500433855270790422999)
                      ·
                        rfl

theorem cell23_4082920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 5, 1, 1, 3].length) (baseStart_4082920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4082920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4082920 prefixEnd_4082920 := by exact prefixLift 4082920
  have htrace : WordTrace (prefixWord ++ tailWord_4082920) baseStart_4082920 baseEnd_4082920 := by
    simpa [prefixWord, tailWord_4082920, baseEnd_4082920] using wordTrace_append hprefix tailTrace_4082920
  have hstable : (prefixWord ++ tailWord_4082920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4082920).length < 2 ^ (prefixWord ++ tailWord_4082920).sum := by decide
  have hdescent : baseEnd_4082920 < baseStart_4082920 := by decide
  rcases family_descends (prefixWord ++ tailWord_4082920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4082923 : List Nat := [1, 1, 1, 1, 2, 7, 3, 1, 1, 5]
def baseStart_4082923 : Nat := 118140960795 + 4082923 * 2 ^ 59
def prefixEnd_4082923 : Nat := 4983230072969 + 3 ^ 40 * 4082923 * 2
def baseEnd_4082923 : Nat := 698833991432411426228495

theorem tailTrace_4082923 : CollatzResearch.WordTrace tailWord_4082923 prefixEnd_4082923 698833991432411426228495 := by
  unfold tailWord_4082923
  simp only [CollatzResearch.WordTrace]
  refine ⟨148916435787274753578005423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99277623858183169052003615 148916435787274753578005423)
  ·
    refine ⟨223374653680912130367008135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148916435787274753578005423 223374653680912130367008135)
    ·
      refine ⟨335061980521368195550512203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223374653680912130367008135 335061980521368195550512203)
      ·
        refine ⟨502592970782052293325768305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335061980521368195550512203 502592970782052293325768305)
        ·
          refine ⟨376944728086539219994326229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 502592970782052293325768305 376944728086539219994326229)
          ·
            refine ⟨8834642064528262968617021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 376944728086539219994326229 8834642064528262968617021)
            ·
              refine ⟨3312990774198098613231383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8834642064528262968617021 3312990774198098613231383)
              ·
                refine ⟨4969486161297147919847075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3312990774198098613231383 4969486161297147919847075)
                ·
                  refine ⟨7454229241945721879770613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4969486161297147919847075 7454229241945721879770613)
                  ·
                    refine ⟨698833991432411426228495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7454229241945721879770613 698833991432411426228495)
                    ·
                      rfl

theorem cell23_4082923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 3, 1, 1, 5].length) (baseStart_4082923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4082923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4082923 prefixEnd_4082923 := by exact prefixLift 4082923
  have htrace : WordTrace (prefixWord ++ tailWord_4082923) baseStart_4082923 baseEnd_4082923 := by
    simpa [prefixWord, tailWord_4082923, baseEnd_4082923] using wordTrace_append hprefix tailTrace_4082923
  have hstable : (prefixWord ++ tailWord_4082923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4082923).length < 2 ^ (prefixWord ++ tailWord_4082923).sum := by decide
  have hdescent : baseEnd_4082923 < baseStart_4082923 := by decide
  rcases family_descends (prefixWord ++ tailWord_4082923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4082956 : List Nat := [2, 2, 1, 2, 2, 3, 1, 3, 1, 2, 4]
def baseStart_4082956 : Nat := 118140960795 + 4082956 * 2 ^ 59
def prefixEnd_4082956 : Nat := 4983230072969 + 3 ^ 40 * 4082956 * 2
def baseEnd_4082956 : Nat := 2096518919158832649572833

theorem tailTrace_4082956 : CollatzResearch.WordTrace tailWord_4082956 prefixEnd_4082956 2096518919158832649572833 := by
  unfold tailWord_4082956
  simp only [CollatzResearch.WordTrace]
  refine ⟨74458819698077600106978361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99278426264103466809304481 74458819698077600106978361)
  ·
    refine ⟨55844114773558200080233771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74458819698077600106978361 55844114773558200080233771)
    ·
      refine ⟨83766172160337300120350657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55844114773558200080233771 83766172160337300120350657)
      ·
        refine ⟨62824629120252975090262993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83766172160337300120350657 62824629120252975090262993)
        ·
          refine ⟨47118471840189731317697245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62824629120252975090262993 47118471840189731317697245)
          ·
            refine ⟨17669426940071149244136467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47118471840189731317697245 17669426940071149244136467)
            ·
              refine ⟨26504140410106723866204701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17669426940071149244136467 26504140410106723866204701)
              ·
                refine ⟨9939052653790021449826763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26504140410106723866204701 9939052653790021449826763)
                ·
                  refine ⟨14908578980685032174740145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9939052653790021449826763 14908578980685032174740145)
                  ·
                    refine ⟨11181434235513774131055109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14908578980685032174740145 11181434235513774131055109)
                    ·
                      refine ⟨2096518919158832649572833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11181434235513774131055109 2096518919158832649572833)
                      ·
                        rfl

theorem cell23_4082956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 3, 1, 2, 4].length) (baseStart_4082956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4082956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4082956 prefixEnd_4082956 := by exact prefixLift 4082956
  have htrace : WordTrace (prefixWord ++ tailWord_4082956) baseStart_4082956 baseEnd_4082956 := by
    simpa [prefixWord, tailWord_4082956, baseEnd_4082956] using wordTrace_append hprefix tailTrace_4082956
  have hstable : (prefixWord ++ tailWord_4082956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4082956).length < 2 ^ (prefixWord ++ tailWord_4082956).sum := by decide
  have hdescent : baseEnd_4082956 < baseStart_4082956 := by decide
  rcases family_descends (prefixWord ++ tailWord_4082956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4082973 : List Nat := [1, 4, 2, 3, 1, 1, 2, 2, 1, 2, 4]
def baseStart_4082973 : Nat := 118140960795 + 4082973 * 2 ^ 59
def prefixEnd_4082973 : Nat := 4983230072969 + 3 ^ 40 * 4082973 * 2
def baseEnd_4082973 : Nat := 2096527648329959083060255

theorem tailTrace_4082973 : CollatzResearch.WordTrace tailWord_4082973 prefixEnd_4082973 2096527648329959083060255 := by
  unfold tailWord_4082973
  simp only [CollatzResearch.WordTrace]
  refine ⟨148918259437093612117325573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99278839624729074744883715 148918259437093612117325573)
  ·
    refine ⟨27922173644455052271998545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 148918259437093612117325573 27922173644455052271998545)
    ·
      refine ⟨20941630233341289203998909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27922173644455052271998545 20941630233341289203998909)
      ·
        refine ⟨7853111337502983451499591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20941630233341289203998909 7853111337502983451499591)
        ·
          refine ⟨11779667006254475177249387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7853111337502983451499591 11779667006254475177249387)
          ·
            refine ⟨17669500509381712765874081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11779667006254475177249387 17669500509381712765874081)
            ·
              refine ⟨13252125382036284574405561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17669500509381712765874081 13252125382036284574405561)
              ·
                refine ⟨9939094036527213430804171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13252125382036284574405561 9939094036527213430804171)
                ·
                  refine ⟨14908641054790820146206257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9939094036527213430804171 14908641054790820146206257)
                  ·
                    refine ⟨11181480791093115109654693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14908641054790820146206257 11181480791093115109654693)
                    ·
                      refine ⟨2096527648329959083060255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11181480791093115109654693 2096527648329959083060255)
                      ·
                        rfl

theorem cell23_4082973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_4082973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4082973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4082973 prefixEnd_4082973 := by exact prefixLift 4082973
  have htrace : WordTrace (prefixWord ++ tailWord_4082973) baseStart_4082973 baseEnd_4082973 := by
    simpa [prefixWord, tailWord_4082973, baseEnd_4082973] using wordTrace_append hprefix tailTrace_4082973
  have hstable : (prefixWord ++ tailWord_4082973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4082973).length < 2 ^ (prefixWord ++ tailWord_4082973).sum := by decide
  have hdescent : baseEnd_4082973 < baseStart_4082973 := by decide
  rcases family_descends (prefixWord ++ tailWord_4082973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4082974 : List Nat := [4, 3, 2, 1, 2, 2, 2, 1, 1, 5]
def baseStart_4082974 : Nat := 118140960795 + 4082974 * 2 ^ 59
def prefixEnd_4082974 : Nat := 4983230072969 + 3 ^ 40 * 4082974 * 2
def baseEnd_4082974 : Nat := 698842720603537859715917

theorem tailTrace_4082974 : CollatzResearch.WordTrace tailWord_4082974 prefixEnd_4082974 698842720603537859715917 := by
  unfold tailWord_4082974
  simp only [CollatzResearch.WordTrace]
  refine ⟨18614786988761248661013997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99278863940059992858741317 18614786988761248661013997)
  ·
    refine ⟨6980545120785468247880249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18614786988761248661013997 6980545120785468247880249)
    ·
      refine ⟨5235408840589101185910187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6980545120785468247880249 5235408840589101185910187)
      ·
        refine ⟨7853113260883651778865281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5235408840589101185910187 7853113260883651778865281)
        ·
          refine ⟨5889834945662738834148961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7853113260883651778865281 5889834945662738834148961)
          ·
            refine ⟨4417376209247054125611721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5889834945662738834148961 4417376209247054125611721)
            ·
              refine ⟨3313032156935290594208791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4417376209247054125611721 3313032156935290594208791)
              ·
                refine ⟨4969548235402935891313187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3313032156935290594208791 4969548235402935891313187)
                ·
                  refine ⟨7454322353104403836969781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4969548235402935891313187 7454322353104403836969781)
                  ·
                    refine ⟨698842720603537859715917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7454322353104403836969781 698842720603537859715917)
                    ·
                      rfl

theorem cell23_4082974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_4082974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4082974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4082974 prefixEnd_4082974 := by exact prefixLift 4082974
  have htrace : WordTrace (prefixWord ++ tailWord_4082974) baseStart_4082974 baseEnd_4082974 := by
    simpa [prefixWord, tailWord_4082974, baseEnd_4082974] using wordTrace_append hprefix tailTrace_4082974
  have hstable : (prefixWord ++ tailWord_4082974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4082974).length < 2 ^ (prefixWord ++ tailWord_4082974).sum := by decide
  have hdescent : baseEnd_4082974 < baseStart_4082974 := by decide
  rcases family_descends (prefixWord ++ tailWord_4082974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4083020 : List Nat := [2, 2, 1, 3, 2, 2, 1, 4, 1, 3, 2]
def baseStart_4083020 : Nat := 118140960795 + 4083020 * 2 ^ 59
def prefixEnd_4083020 : Nat := 4983230072969 + 3 ^ 40 * 4083020 * 2
def baseEnd_4083020 : Nat := 2096551781920720399172539

theorem tailTrace_4083020 : CollatzResearch.WordTrace tailWord_4083020 prefixEnd_4083020 2096551781920720399172539 := by
  unfold tailWord_4083020
  simp only [CollatzResearch.WordTrace]
  refine ⟨74459986833961669572143257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99279982445282226096191009 74459986833961669572143257)
  ·
    refine ⟨55844990125471252179107443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74459986833961669572143257 55844990125471252179107443)
    ·
      refine ⟨83767485188206878268661165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55844990125471252179107443 83767485188206878268661165)
      ·
        refine ⟨31412806945577579350747937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83767485188206878268661165 31412806945577579350747937)
        ·
          refine ⟨23559605209183184513060953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31412806945577579350747937 23559605209183184513060953)
          ·
            refine ⟨17669703906887388384795715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23559605209183184513060953 17669703906887388384795715)
            ·
              refine ⟨26504555860331082577193573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17669703906887388384795715 26504555860331082577193573)
              ·
                refine ⟨4969604223812077983223795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26504555860331082577193573 4969604223812077983223795)
                ·
                  refine ⟨7454406335718116974835693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4969604223812077983223795 7454406335718116974835693)
                  ·
                    refine ⟨2795402375894293865563385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7454406335718116974835693 2795402375894293865563385)
                    ·
                      refine ⟨2096551781920720399172539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2795402375894293865563385 2096551781920720399172539)
                      ·
                        rfl

theorem cell23_4083020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 4, 1, 3, 2].length) (baseStart_4083020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4083020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4083020 prefixEnd_4083020 := by exact prefixLift 4083020
  have htrace : WordTrace (prefixWord ++ tailWord_4083020) baseStart_4083020 baseEnd_4083020 := by
    simpa [prefixWord, tailWord_4083020, baseEnd_4083020] using wordTrace_append hprefix tailTrace_4083020
  have hstable : (prefixWord ++ tailWord_4083020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4083020).length < 2 ^ (prefixWord ++ tailWord_4083020).sum := by decide
  have hdescent : baseEnd_4083020 < baseStart_4083020 := by decide
  rcases family_descends (prefixWord ++ tailWord_4083020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4083033 : List Nat := [1, 2, 1, 2, 2, 2, 2, 4, 1, 4, 2]
def baseStart_4083033 : Nat := 118140960795 + 4083033 * 2 ^ 59
def prefixEnd_4083033 : Nat := 4983230072969 + 3 ^ 40 * 4083033 * 2
def baseEnd_4083033 : Nat := 2096558457169228848309979

theorem tailTrace_4083033 : CollatzResearch.WordTrace tailWord_4083033 prefixEnd_4083033 2096558457169228848309979 := by
  unfold tailWord_4083033
  simp only [CollatzResearch.WordTrace]
  refine ⟨148920447816876242364509753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99280298544584161576339835 148920447816876242364509753)
  ·
    refine ⟨111690335862657181773382315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148920447816876242364509753 111690335862657181773382315)
    ·
      refine ⟨167535503793985772660073473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111690335862657181773382315 167535503793985772660073473)
      ·
        refine ⟨125651627845489329495055105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167535503793985772660073473 125651627845489329495055105)
        ·
          refine ⟨94238720884116997121291329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125651627845489329495055105 94238720884116997121291329)
          ·
            refine ⟨70679040663087747840968497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94238720884116997121291329 70679040663087747840968497)
            ·
              refine ⟨53009280497315810880726373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70679040663087747840968497 53009280497315810880726373)
              ·
                refine ⟨9939240093246714540136195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53009280497315810880726373 9939240093246714540136195)
                ·
                  refine ⟨14908860139870071810204293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9939240093246714540136195 14908860139870071810204293)
                  ·
                    refine ⟨2795411276225638464413305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14908860139870071810204293 2795411276225638464413305)
                    ·
                      refine ⟨2096558457169228848309979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2795411276225638464413305 2096558457169228848309979)
                      ·
                        rfl

theorem cell23_4083033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 4, 1, 4, 2].length) (baseStart_4083033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4083033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4083033 prefixEnd_4083033 := by exact prefixLift 4083033
  have htrace : WordTrace (prefixWord ++ tailWord_4083033) baseStart_4083033 baseEnd_4083033 := by
    simpa [prefixWord, tailWord_4083033, baseEnd_4083033] using wordTrace_append hprefix tailTrace_4083033
  have hstable : (prefixWord ++ tailWord_4083033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4083033).length < 2 ^ (prefixWord ++ tailWord_4083033).sum := by decide
  have hdescent : baseEnd_4083033 < baseStart_4083033 := by decide
  rcases family_descends (prefixWord ++ tailWord_4083033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4083061 : List Nat := [1, 3, 4, 1, 4, 1, 2, 1, 2, 1, 3]
def baseStart_4083061 : Nat := 118140960795 + 4083061 * 2 ^ 59
def prefixEnd_4083061 : Nat := 4983230072969 + 3 ^ 40 * 4083061 * 2
def baseEnd_4083061 : Nat := 2096572834627554738759851

theorem tailTrace_4083061 : CollatzResearch.WordTrace tailWord_4083061 prefixEnd_4083061 2096572834627554738759851 := by
  unfold tailWord_4083061
  simp only [CollatzResearch.WordTrace]
  refine ⟨148921469060774803146529037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99280979373849868764352691 148921469060774803146529037)
  ·
    refine ⟨55845550897790551179948389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148921469060774803146529037 55845550897790551179948389)
    ·
      refine ⟨10471040793335728346240323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55845550897790551179948389 10471040793335728346240323)
      ·
        refine ⟨15706561190003592519360485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10471040793335728346240323 15706561190003592519360485)
        ·
          refine ⟨2944980223125673597380091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15706561190003592519360485 2944980223125673597380091)
          ·
            refine ⟨4417470334688510396070137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2944980223125673597380091 4417470334688510396070137)
            ·
              refine ⟨3313102751016382797052603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4417470334688510396070137 3313102751016382797052603)
              ·
                refine ⟨4969654126524574195578905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3313102751016382797052603 4969654126524574195578905)
                ·
                  refine ⟨3727240594893430646684179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4969654126524574195578905 3727240594893430646684179)
                  ·
                    refine ⟨5590860892340145970026269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3727240594893430646684179 5590860892340145970026269)
                    ·
                      refine ⟨2096572834627554738759851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5590860892340145970026269 2096572834627554738759851)
                      ·
                        rfl

theorem cell23_4083061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 2, 1, 2, 1, 3].length) (baseStart_4083061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4083061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4083061 prefixEnd_4083061 := by exact prefixLift 4083061
  have htrace : WordTrace (prefixWord ++ tailWord_4083061) baseStart_4083061 baseEnd_4083061 := by
    simpa [prefixWord, tailWord_4083061, baseEnd_4083061] using wordTrace_append hprefix tailTrace_4083061
  have hstable : (prefixWord ++ tailWord_4083061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4083061).length < 2 ^ (prefixWord ++ tailWord_4083061).sum := by decide
  have hdescent : baseEnd_4083061 < baseStart_4083061 := by decide
  rcases family_descends (prefixWord ++ tailWord_4083061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4083103 : List Nat := [1, 1, 2, 5, 1, 2, 2, 2, 2, 5]
def baseStart_4083103 : Nat := 118140960795 + 4083103 * 2 ^ 59
def prefixEnd_4083103 : Nat := 4983230072969 + 3 ^ 40 * 4083103 * 2
def baseEnd_4083103 : Nat := 698864800271681191478219

theorem tailTrace_4083103 : CollatzResearch.WordTrace tailWord_4083103 prefixEnd_4083103 698864800271681191478219 := by
  unfold tailWord_4083103
  simp only [CollatzResearch.WordTrace]
  refine ⟨148923000926622644319557963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99282000617748429546371975 148923000926622644319557963)
  ·
    refine ⟨223384501389933966479336945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148923000926622644319557963 223384501389933966479336945)
    ·
      refine ⟨167538376042450474859502709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223384501389933966479336945 167538376042450474859502709)
      ·
        refine ⟨15706722753979732018078379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 167538376042450474859502709 15706722753979732018078379)
        ·
          refine ⟨23560084130969598027117569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15706722753979732018078379 23560084130969598027117569)
          ·
            refine ⟨17670063098227198520338177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23560084130969598027117569 17670063098227198520338177)
            ·
              refine ⟨13252547323670398890253633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17670063098227198520338177 13252547323670398890253633)
              ·
                refine ⟨9939410492752799167690225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13252547323670398890253633 9939410492752799167690225)
                ·
                  refine ⟨7454557869564599375767669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9939410492752799167690225 7454557869564599375767669)
                  ·
                    refine ⟨698864800271681191478219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7454557869564599375767669 698864800271681191478219)
                    ·
                      rfl

theorem cell23_4083103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 2, 2, 5].length) (baseStart_4083103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4083103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4083103 prefixEnd_4083103 := by exact prefixLift 4083103
  have htrace : WordTrace (prefixWord ++ tailWord_4083103) baseStart_4083103 baseEnd_4083103 := by
    simpa [prefixWord, tailWord_4083103, baseEnd_4083103] using wordTrace_append hprefix tailTrace_4083103
  have hstable : (prefixWord ++ tailWord_4083103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4083103).length < 2 ^ (prefixWord ++ tailWord_4083103).sum := by decide
  have hdescent : baseEnd_4083103 < baseStart_4083103 := by decide
  rcases family_descends (prefixWord ++ tailWord_4083103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4083140 : List Nat := [2, 3, 3, 2, 1, 2, 1, 1, 1, 3, 4]
def baseStart_4083140 : Nat := 118140960795 + 4083140 * 2 ^ 59
def prefixEnd_4083140 : Nat := 4983230072969 + 3 ^ 40 * 4083140 * 2
def baseEnd_4083140 : Nat := 2096613399599259929671987

theorem tailTrace_4083140 : CollatzResearch.WordTrace tailWord_4083140 prefixEnd_4083140 2096613399599259929671987 := by
  unfold tailWord_4083140
  simp only [CollatzResearch.WordTrace]
  refine ⟨74462175213744299819327437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99282900284992399759103249 74462175213744299819327437)
  ·
    refine ⟨27923315705154112432247789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74462175213744299819327437 27923315705154112432247789)
    ·
      refine ⟨10471243389432792162092921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27923315705154112432247789 10471243389432792162092921)
      ·
        refine ⟨7853432542074594121569691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10471243389432792162092921 7853432542074594121569691)
        ·
          refine ⟨11780148813111891182354537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7853432542074594121569691 11780148813111891182354537)
          ·
            refine ⟨8835111609833918386765903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11780148813111891182354537 8835111609833918386765903)
            ·
              refine ⟨13252667414750877580148855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8835111609833918386765903 13252667414750877580148855)
              ·
                refine ⟨19879001122126316370223283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13252667414750877580148855 19879001122126316370223283)
                ·
                  refine ⟨29818501683189474555334925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19879001122126316370223283 29818501683189474555334925)
                  ·
                    refine ⟨11181938131196052958250597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29818501683189474555334925 11181938131196052958250597)
                    ·
                      refine ⟨2096613399599259929671987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11181938131196052958250597 2096613399599259929671987)
                      ·
                        rfl

theorem cell23_4083140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_4083140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4083140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4083140 prefixEnd_4083140 := by exact prefixLift 4083140
  have htrace : WordTrace (prefixWord ++ tailWord_4083140) baseStart_4083140 baseEnd_4083140 := by
    simpa [prefixWord, tailWord_4083140, baseEnd_4083140] using wordTrace_append hprefix tailTrace_4083140
  have hstable : (prefixWord ++ tailWord_4083140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4083140).length < 2 ^ (prefixWord ++ tailWord_4083140).sum := by decide
  have hdescent : baseEnd_4083140 < baseStart_4083140 := by decide
  rcases family_descends (prefixWord ++ tailWord_4083140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4083143 : List Nat := [1, 1, 4, 1, 1, 3, 3, 1, 1, 4, 3]
def baseStart_4083143 : Nat := 118140960795 + 4083143 * 2 ^ 59
def prefixEnd_4083143 : Nat := 4983230072969 + 3 ^ 40 * 4083143 * 2
def baseEnd_4083143 : Nat := 2096614940041223417934473

theorem tailTrace_4083143 : CollatzResearch.WordTrace tailWord_4083143 prefixEnd_4083143 2096614940041223417934473 := by
  unfold tailWord_4083143
  simp only [CollatzResearch.WordTrace]
  refine ⟨148924459846477731151014083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99282973230985154100676055 148924459846477731151014083)
  ·
    refine ⟨223386689769716596726521125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148924459846477731151014083 223386689769716596726521125)
    ·
      refine ⟨41885004331821861886222711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 223386689769716596726521125 41885004331821861886222711)
      ·
        refine ⟨62827506497732792829334067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41885004331821861886222711 62827506497732792829334067)
        ·
          refine ⟨94241259746599189244001101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62827506497732792829334067 94241259746599189244001101)
          ·
            refine ⟨35340472404974695966500413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94241259746599189244001101 35340472404974695966500413)
            ·
              refine ⟨13252677151865510987437655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35340472404974695966500413 13252677151865510987437655)
              ·
                refine ⟨19879015727798266481156483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13252677151865510987437655 19879015727798266481156483)
                ·
                  refine ⟨29818523591697399721734725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19879015727798266481156483 29818523591697399721734725)
                  ·
                    refine ⟨5590973173443262447825261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29818523591697399721734725 5590973173443262447825261)
                    ·
                      refine ⟨2096614940041223417934473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5590973173443262447825261 2096614940041223417934473)
                      ·
                        rfl

theorem cell23_4083143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 1, 1, 4, 3].length) (baseStart_4083143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4083143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4083143 prefixEnd_4083143 := by exact prefixLift 4083143
  have htrace : WordTrace (prefixWord ++ tailWord_4083143) baseStart_4083143 baseEnd_4083143 := by
    simpa [prefixWord, tailWord_4083143, baseEnd_4083143] using wordTrace_append hprefix tailTrace_4083143
  have hstable : (prefixWord ++ tailWord_4083143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4083143).length < 2 ^ (prefixWord ++ tailWord_4083143).sum := by decide
  have hdescent : baseEnd_4083143 < baseStart_4083143 := by decide
  rcases family_descends (prefixWord ++ tailWord_4083143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4083201 : List Nat := [1, 2, 4, 1, 5, 1, 1, 3, 1, 4]
def baseStart_4083201 : Nat := 118140960795 + 4083201 * 2 ^ 59
def prefixEnd_4083201 : Nat := 4983230072969 + 3 ^ 40 * 4083201 * 2
def baseEnd_4083201 : Nat := 698881573973061397003069

theorem tailTrace_4083201 : CollatzResearch.WordTrace tailWord_4083201 prefixEnd_4083201 698881573973061397003069 := by
  unfold tailWord_4083201
  simp only [CollatzResearch.WordTrace]
  refine ⟨148926575280267607056625457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99284383520178404704416971 148926575280267607056625457)
  ·
    refine ⟨111694931460200705292469093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148926575280267607056625457 111694931460200705292469093)
    ·
      refine ⟨20942799648787632242337955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111694931460200705292469093 20942799648787632242337955)
      ·
        refine ⟨31414199473181448363506933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20942799648787632242337955 31414199473181448363506933)
        ·
          refine ⟨2945081200610760784078775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31414199473181448363506933 2945081200610760784078775)
          ·
            refine ⟨4417621800916141176118163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2945081200610760784078775 4417621800916141176118163)
            ·
              refine ⟨6626432701374211764177245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4417621800916141176118163 6626432701374211764177245)
              ·
                refine ⟨2484912263015329411566467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6626432701374211764177245 2484912263015329411566467)
                ·
                  refine ⟨3727368394522994117349701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2484912263015329411566467 3727368394522994117349701)
                  ·
                    refine ⟨698881573973061397003069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3727368394522994117349701 698881573973061397003069)
                    ·
                      rfl

theorem cell23_4083201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 1, 3, 1, 4].length) (baseStart_4083201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4083201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4083201 prefixEnd_4083201 := by exact prefixLift 4083201
  have htrace : WordTrace (prefixWord ++ tailWord_4083201) baseStart_4083201 baseEnd_4083201 := by
    simpa [prefixWord, tailWord_4083201, baseEnd_4083201] using wordTrace_append hprefix tailTrace_4083201
  have hstable : (prefixWord ++ tailWord_4083201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4083201).length < 2 ^ (prefixWord ++ tailWord_4083201).sum := by decide
  have hdescent : baseEnd_4083201 < baseStart_4083201 := by decide
  rcases family_descends (prefixWord ++ tailWord_4083201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4083210 : List Nat := [3, 1, 2, 2, 2, 2, 2, 3, 1, 5]
def baseStart_4083210 : Nat := 118140960795 + 4083210 * 2 ^ 59
def prefixEnd_4083210 : Nat := 4983230072969 + 3 ^ 40 * 4083210 * 2
def baseEnd_4083210 : Nat := 698883114415024885265555

theorem tailTrace_4083210 : CollatzResearch.WordTrace tailWord_4083210 prefixEnd_4083210 698883114415024885265555 := by
  unfold tailWord_4083210
  simp only [CollatzResearch.WordTrace]
  refine ⟨37231725884308750398425771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99284602358156667729135389 37231725884308750398425771)
  ·
    refine ⟨55847588826463125597638657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37231725884308750398425771 55847588826463125597638657)
    ·
      refine ⟨41885691619847344198228993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55847588826463125597638657 41885691619847344198228993)
      ·
        refine ⟨31414268714885508148671745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41885691619847344198228993 31414268714885508148671745)
        ·
          refine ⟨23560701536164131111503809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31414268714885508148671745 23560701536164131111503809)
          ·
            refine ⟨17670526152123098333627857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23560701536164131111503809 17670526152123098333627857)
            ·
              refine ⟨13252894614092323750220893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17670526152123098333627857 13252894614092323750220893)
              ·
                refine ⟨4969835480284621406332835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13252894614092323750220893 4969835480284621406332835)
                ·
                  refine ⟨7454753220426932109499253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4969835480284621406332835 7454753220426932109499253)
                  ·
                    refine ⟨698883114415024885265555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7454753220426932109499253 698883114415024885265555)
                    ·
                      rfl

theorem cell23_4083210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 3, 1, 5].length) (baseStart_4083210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4083210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4083210 prefixEnd_4083210 := by exact prefixLift 4083210
  have htrace : WordTrace (prefixWord ++ tailWord_4083210) baseStart_4083210 baseEnd_4083210 := by
    simpa [prefixWord, tailWord_4083210, baseEnd_4083210] using wordTrace_append hprefix tailTrace_4083210
  have hstable : (prefixWord ++ tailWord_4083210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4083210).length < 2 ^ (prefixWord ++ tailWord_4083210).sum := by decide
  have hdescent : baseEnd_4083210 < baseStart_4083210 := by decide
  rcases family_descends (prefixWord ++ tailWord_4083210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4083224 : List Nat := [2, 1, 2, 3, 4, 2, 1, 1, 3, 1, 3]
def baseStart_4083224 : Nat := 118140960795 + 4083224 * 2 ^ 59
def prefixEnd_4083224 : Nat := 4983230072969 + 3 ^ 40 * 4083224 * 2
def baseEnd_4083224 : Nat := 2096656531974237601021601

theorem tailTrace_4083224 : CollatzResearch.WordTrace tailWord_4083224 prefixEnd_4083224 2096656531974237601021601 := by
  unfold tailWord_4083224
  simp only [CollatzResearch.WordTrace]
  refine ⟨74463707079592140992356363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99284942772789521323141817 74463707079592140992356363)
  ·
    refine ⟨111695560619388211488534545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74463707079592140992356363 111695560619388211488534545)
    ·
      refine ⟨83771670464541158616400909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111695560619388211488534545 83771670464541158616400909)
      ·
        refine ⟨31414376424202934481150341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83771670464541158616400909 31414376424202934481150341)
        ·
          refine ⟨5890195579538050215215689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31414376424202934481150341 5890195579538050215215689)
          ·
            refine ⟨4417646684653537661411767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5890195579538050215215689 4417646684653537661411767)
            ·
              refine ⟨6626470026980306492117651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4417646684653537661411767 6626470026980306492117651)
              ·
                refine ⟨9939705040470459738176477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6626470026980306492117651 9939705040470459738176477)
                ·
                  refine ⟨3727389390176422401816179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9939705040470459738176477 3727389390176422401816179)
                  ·
                    refine ⟨5591084085264633602724269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3727389390176422401816179 5591084085264633602724269)
                    ·
                      refine ⟨2096656531974237601021601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5591084085264633602724269 2096656531974237601021601)
                      ·
                        rfl

theorem cell23_4083224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 1, 1, 3, 1, 3].length) (baseStart_4083224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4083224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4083224 prefixEnd_4083224 := by exact prefixLift 4083224
  have htrace : WordTrace (prefixWord ++ tailWord_4083224) baseStart_4083224 baseEnd_4083224 := by
    simpa [prefixWord, tailWord_4083224, baseEnd_4083224] using wordTrace_append hprefix tailTrace_4083224
  have hstable : (prefixWord ++ tailWord_4083224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4083224).length < 2 ^ (prefixWord ++ tailWord_4083224).sum := by decide
  have hdescent : baseEnd_4083224 < baseStart_4083224 := by decide
  rcases family_descends (prefixWord ++ tailWord_4083224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4083253 : List Nat := [1, 3, 3, 1, 1, 3, 2, 9]
def baseStart_4083253 : Nat := 118140960795 + 4083253 * 2 ^ 59
def prefixEnd_4083253 : Nat := 4983230072969 + 3 ^ 40 * 4083253 * 2
def baseEnd_4083253 : Nat := 77654497144933999539221

theorem tailTrace_4083253 : CollatzResearch.WordTrace tailWord_4083253 prefixEnd_4083253 77654497144933999539221 := by
  unfold tailWord_4083253
  simp only [CollatzResearch.WordTrace]
  refine ⟨148928471876079219937518413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99285647917386146625012275 148928471876079219937518413)
  ·
    refine ⟨55848176953529707476569405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148928471876079219937518413 55848176953529707476569405)
    ·
      refine ⟨20943066357573640303713527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55848176953529707476569405 20943066357573640303713527)
      ·
        refine ⟨31414599536360460455570291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20943066357573640303713527 31414599536360460455570291)
        ·
          refine ⟨47121899304540690683355437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31414599536360460455570291 47121899304540690683355437)
          ·
            refine ⟨17670712239202759006258289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47121899304540690683355437 17670712239202759006258289)
            ·
              refine ⟨13253034179402069254693717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17670712239202759006258289 13253034179402069254693717)
              ·
                refine ⟨77654497144933999539221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 13253034179402069254693717 77654497144933999539221)
                ·
                  rfl

theorem cell23_4083253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 9].length) (baseStart_4083253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4083253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4083253 prefixEnd_4083253 := by exact prefixLift 4083253
  have htrace : WordTrace (prefixWord ++ tailWord_4083253) baseStart_4083253 baseEnd_4083253 := by
    simpa [prefixWord, tailWord_4083253, baseEnd_4083253] using wordTrace_append hprefix tailTrace_4083253
  have hstable : (prefixWord ++ tailWord_4083253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4083253).length < 2 ^ (prefixWord ++ tailWord_4083253).sum := by decide
  have hdescent : baseEnd_4083253 < baseStart_4083253 := by decide
  rcases family_descends (prefixWord ++ tailWord_4083253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4083264 : List Nat := [2, 1, 1, 2, 2, 2, 1, 7, 1, 2, 2]
def baseStart_4083264 : Nat := 118140960795 + 4083264 * 2 ^ 59
def prefixEnd_4083264 : Nat := 4983230072969 + 3 ^ 40 * 4083264 * 2
def baseEnd_4083264 : Nat := 2096677071200417444521417

theorem tailTrace_4083264 : CollatzResearch.WordTrace tailWord_4083264 prefixEnd_4083264 2096677071200417444521417 := by
  unfold tailWord_4083264
  simp only [CollatzResearch.WordTrace]
  refine ⟨74464436539519684408084423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99285915386026245877445897 74464436539519684408084423)
  ·
    refine ⟨111696654809279526612126635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74464436539519684408084423 111696654809279526612126635)
    ·
      refine ⟨167544982213919289918189953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111696654809279526612126635 167544982213919289918189953)
      ·
        refine ⟨125658736660439467438642465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167544982213919289918189953 125658736660439467438642465)
        ·
          refine ⟨94244052495329600578981849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125658736660439467438642465 94244052495329600578981849)
          ·
            refine ⟨70683039371497200434236387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94244052495329600578981849 70683039371497200434236387)
            ·
              refine ⟨106024559057245800651354581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70683039371497200434236387 106024559057245800651354581)
              ·
                refine ⟨2484950602904198452766123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 106024559057245800651354581 2484950602904198452766123)
                ·
                  refine ⟨3727425904356297679149185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2484950602904198452766123 3727425904356297679149185)
                  ·
                    refine ⟨2795569428267223259361889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3727425904356297679149185 2795569428267223259361889)
                    ·
                      refine ⟨2096677071200417444521417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2795569428267223259361889 2096677071200417444521417)
                      ·
                        rfl

theorem cell23_4083264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 7, 1, 2, 2].length) (baseStart_4083264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4083264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4083264 prefixEnd_4083264 := by exact prefixLift 4083264
  have htrace : WordTrace (prefixWord ++ tailWord_4083264) baseStart_4083264 baseEnd_4083264 := by
    simpa [prefixWord, tailWord_4083264, baseEnd_4083264] using wordTrace_append hprefix tailTrace_4083264
  have hstable : (prefixWord ++ tailWord_4083264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4083264).length < 2 ^ (prefixWord ++ tailWord_4083264).sum := by decide
  have hdescent : baseEnd_4083264 < baseStart_4083264 := by decide
  rcases family_descends (prefixWord ++ tailWord_4083264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4083270 : List Nat := [6, 1, 1, 1, 14]
def baseStart_4083270 : Nat := 118140960795 + 4083270 * 2 ^ 59
def prefixEnd_4083270 : Nat := 4983230072969 + 3 ^ 40 * 4083270 * 2
def baseEnd_4083270 : Nat := 2876104461021048588541

theorem tailTrace_4083270 : CollatzResearch.WordTrace tailWord_4083270 prefixEnd_4083270 2876104461021048588541 := by
  unfold tailWord_4083270
  simp only [CollatzResearch.WordTrace]
  refine ⟨4654034122406800995027727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 99286061278011754560591509 4654034122406800995027727)
  ·
    refine ⟨6981051183610201492541591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4654034122406800995027727 6981051183610201492541591)
    ·
      refine ⟨10471576775415302238812387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6981051183610201492541591 10471576775415302238812387)
      ·
        refine ⟨15707365163122953358218581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10471576775415302238812387 15707365163122953358218581)
        ·
          refine ⟨2876104461021048588541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 15707365163122953358218581 2876104461021048588541)
          ·
            rfl

theorem cell23_4083270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 14].length) (baseStart_4083270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4083270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4083270 prefixEnd_4083270 := by exact prefixLift 4083270
  have htrace : WordTrace (prefixWord ++ tailWord_4083270) baseStart_4083270 baseEnd_4083270 := by
    simpa [prefixWord, tailWord_4083270, baseEnd_4083270] using wordTrace_append hprefix tailTrace_4083270
  have hstable : (prefixWord ++ tailWord_4083270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4083270).length < 2 ^ (prefixWord ++ tailWord_4083270).sum := by decide
  have hdescent : baseEnd_4083270 < baseStart_4083270 := by decide
  rcases family_descends (prefixWord ++ tailWord_4083270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4083297 : List Nat := [1, 2, 3, 1, 1, 3, 1, 5, 2, 1, 3]
def baseStart_4083297 : Nat := 118140960795 + 4083297 * 2 ^ 59
def prefixEnd_4083297 : Nat := 4983230072969 + 3 ^ 40 * 4083297 * 2
def baseEnd_4083297 : Nat := 2096694016062015815408765

theorem tailTrace_4083297 : CollatzResearch.WordTrace tailWord_4083297 prefixEnd_4083297 2096694016062015815408765 := by
  unfold tailWord_4083297
  simp only [CollatzResearch.WordTrace]
  refine ⟨148930076687919815452120145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99286717791946543634746763 148930076687919815452120145)
  ·
    refine ⟨111697557515939861589090109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148930076687919815452120145 111697557515939861589090109)
    ·
      refine ⟨41886584068477448095908791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111697557515939861589090109 41886584068477448095908791)
      ·
        refine ⟨62829876102716172143863187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41886584068477448095908791 62829876102716172143863187)
        ·
          refine ⟨94244814154074258215794781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62829876102716172143863187 94244814154074258215794781)
          ·
            refine ⟨35341805307777846830923043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94244814154074258215794781 35341805307777846830923043)
            ·
              refine ⟨53012707961666770246384565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35341805307777846830923043 53012707961666770246384565)
              ·
                refine ⟨4969941371406259710598553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53012707961666770246384565 4969941371406259710598553)
                ·
                  refine ⟨3727456028554694782948915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4969941371406259710598553 3727456028554694782948915)
                  ·
                    refine ⟨5591184042832042174423373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3727456028554694782948915 5591184042832042174423373)
                    ·
                      refine ⟨2096694016062015815408765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5591184042832042174423373 2096694016062015815408765)
                      ·
                        rfl

theorem cell23_4083297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 5, 2, 1, 3].length) (baseStart_4083297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4083297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4083297 prefixEnd_4083297 := by exact prefixLift 4083297
  have htrace : WordTrace (prefixWord ++ tailWord_4083297) baseStart_4083297 baseEnd_4083297 := by
    simpa [prefixWord, tailWord_4083297, baseEnd_4083297] using wordTrace_append hprefix tailTrace_4083297
  have hstable : (prefixWord ++ tailWord_4083297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4083297).length < 2 ^ (prefixWord ++ tailWord_4083297).sum := by decide
  have hdescent : baseEnd_4083297 < baseStart_4083297 := by decide
  rcases family_descends (prefixWord ++ tailWord_4083297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4083323 : List Nat := [1, 1, 1, 1, 1, 4, 4, 1, 1, 3, 5]
def baseStart_4083323 : Nat := 118140960795 + 4083323 * 2 ^ 59
def prefixEnd_4083323 : Nat := 4983230072969 + 3 ^ 40 * 4083323 * 2
def baseEnd_4083323 : Nat := 2096707366559032713683645

theorem tailTrace_4083323 : CollatzResearch.WordTrace tailWord_4083323 prefixEnd_4083323 2096707366559032713683645 := by
  unfold tailWord_4083323
  simp only [CollatzResearch.WordTrace]
  refine ⟨148931024985825621892566623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99287349990550414595044415 148931024985825621892566623)
  ·
    refine ⟨223396537478738432838849935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148931024985825621892566623 223396537478738432838849935)
    ·
      refine ⟨335094806218107649258274903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223396537478738432838849935 335094806218107649258274903)
      ·
        refine ⟨502642209327161473887412355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335094806218107649258274903 502642209327161473887412355)
        ·
          refine ⟨753963313990742210831118533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 502642209327161473887412355 753963313990742210831118533)
          ·
            refine ⟨141368121373264164530834725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 753963313990742210831118533 141368121373264164530834725)
            ·
              refine ⟨26506522757487030849531511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 141368121373264164530834725 26506522757487030849531511)
              ·
                refine ⟨39759784136230546274297267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26506522757487030849531511 39759784136230546274297267)
                ·
                  refine ⟨59639676204345819411445901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39759784136230546274297267 59639676204345819411445901)
                  ·
                    refine ⟨22364878576629682279292213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59639676204345819411445901 22364878576629682279292213)
                    ·
                      refine ⟨2096707366559032713683645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22364878576629682279292213 2096707366559032713683645)
                      ·
                        rfl

theorem cell23_4083323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 1, 1, 3, 5].length) (baseStart_4083323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4083323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4083323 prefixEnd_4083323 := by exact prefixLift 4083323
  have htrace : WordTrace (prefixWord ++ tailWord_4083323) baseStart_4083323 baseEnd_4083323 := by
    simpa [prefixWord, tailWord_4083323, baseEnd_4083323] using wordTrace_append hprefix tailTrace_4083323
  have hstable : (prefixWord ++ tailWord_4083323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4083323).length < 2 ^ (prefixWord ++ tailWord_4083323).sum := by decide
  have hdescent : baseEnd_4083323 < baseStart_4083323 := by decide
  rcases family_descends (prefixWord ++ tailWord_4083323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4083348 : List Nat := [2, 4, 2, 2, 2, 1, 3, 1, 2, 1, 3]
def baseStart_4083348 : Nat := 118140960795 + 4083348 * 2 ^ 59
def prefixEnd_4083348 : Nat := 4983230072969 + 3 ^ 40 * 4083348 * 2
def baseEnd_4083348 : Nat := 2096720203575395115871031

theorem tailTrace_4083348 : CollatzResearch.WordTrace tailWord_4083348 prefixEnd_4083348 2096720203575395115871031 := by
  unfold tailWord_4083348
  simp only [CollatzResearch.WordTrace]
  refine ⟨74465968405367525581113349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99287957873823367441484465 74465968405367525581113349)
  ·
    refine ⟨13962369076006411046458753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74465968405367525581113349 13962369076006411046458753)
    ·
      refine ⟨10471776807004808284844065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13962369076006411046458753 10471776807004808284844065)
      ·
        refine ⟨7853832605253606213633049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10471776807004808284844065 7853832605253606213633049)
        ·
          refine ⟨5890374453940204660224787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7853832605253606213633049 5890374453940204660224787)
          ·
            refine ⟨8835561680910306990337181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5890374453940204660224787 8835561680910306990337181)
            ·
              refine ⟨3313335630341365121376443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8835561680910306990337181 3313335630341365121376443)
              ·
                refine ⟨4970003445512047682064665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3313335630341365121376443 4970003445512047682064665)
                ·
                  refine ⟨3727502584134035761548499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4970003445512047682064665 3727502584134035761548499)
                  ·
                    refine ⟨5591253876201053642322749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3727502584134035761548499 5591253876201053642322749)
                    ·
                      refine ⟨2096720203575395115871031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5591253876201053642322749 2096720203575395115871031)
                      ·
                        rfl

theorem cell23_4083348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 3, 1, 2, 1, 3].length) (baseStart_4083348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4083348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4083348 prefixEnd_4083348 := by exact prefixLift 4083348
  have htrace : WordTrace (prefixWord ++ tailWord_4083348) baseStart_4083348 baseEnd_4083348 := by
    simpa [prefixWord, tailWord_4083348, baseEnd_4083348] using wordTrace_append hprefix tailTrace_4083348
  have hstable : (prefixWord ++ tailWord_4083348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4083348).length < 2 ^ (prefixWord ++ tailWord_4083348).sum := by decide
  have hdescent : baseEnd_4083348 < baseStart_4083348 := by decide
  rcases family_descends (prefixWord ++ tailWord_4083348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4083360 : List Nat := [2, 1, 1, 4, 3, 1, 2, 2, 7]
def baseStart_4083360 : Nat := 118140960795 + 4083360 * 2 ^ 59
def prefixEnd_4083360 : Nat := 4983230072969 + 3 ^ 40 * 4083360 * 2
def baseEnd_4083360 : Nat := 232969596149249896546775

theorem tailTrace_4083360 : CollatzResearch.WordTrace tailWord_4083360 prefixEnd_4083360 232969596149249896546775 := by
  unfold tailWord_4083360
  simp only [CollatzResearch.WordTrace]
  refine ⟨74466187243345788605831767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99288249657794384807775689 74466187243345788605831767)
  ·
    refine ⟨111699280865018682908747651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74466187243345788605831767 111699280865018682908747651)
    ·
      refine ⟨167548921297528024363121477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111699280865018682908747651 167548921297528024363121477)
      ·
        refine ⟨31415422743286504568085277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 167548921297528024363121477 31415422743286504568085277)
        ·
          refine ⟨11780783528732439213031979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31415422743286504568085277 11780783528732439213031979)
          ·
            refine ⟨17671175293098658819547969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11780783528732439213031979 17671175293098658819547969)
            ·
              refine ⟨13253381469823994114660977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17671175293098658819547969 13253381469823994114660977)
              ·
                refine ⟨9940036102367995585995733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13253381469823994114660977 9940036102367995585995733)
                ·
                  refine ⟨232969596149249896546775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9940036102367995585995733 232969596149249896546775)
                  ·
                    rfl

theorem cell23_4083360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 2, 7].length) (baseStart_4083360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4083360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4083360 prefixEnd_4083360 := by exact prefixLift 4083360
  have htrace : WordTrace (prefixWord ++ tailWord_4083360) baseStart_4083360 baseEnd_4083360 := by
    simpa [prefixWord, tailWord_4083360, baseEnd_4083360] using wordTrace_append hprefix tailTrace_4083360
  have hstable : (prefixWord ++ tailWord_4083360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4083360).length < 2 ^ (prefixWord ++ tailWord_4083360).sum := by decide
  have hdescent : baseEnd_4083360 < baseStart_4083360 := by decide
  rcases family_descends (prefixWord ++ tailWord_4083360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4083374 : List Nat := [4, 1, 4, 1, 2, 1, 1, 1, 2, 1, 5]
def baseStart_4083374 : Nat := 118140960795 + 4083374 * 2 ^ 59
def prefixEnd_4083374 : Nat := 4983230072969 + 3 ^ 40 * 4083374 * 2
def baseEnd_4083374 : Nat := 2096733554072412014145911

theorem tailTrace_4083374 : CollatzResearch.WordTrace tailWord_4083374 prefixEnd_4083374 2096733554072412014145911 := by
  unfold tailWord_4083374
  simp only [CollatzResearch.WordTrace]
  refine ⟨18616610638580107200334147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99288590072427238401782117 18616610638580107200334147)
  ·
    refine ⟨27924915957870160800501221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18616610638580107200334147 27924915957870160800501221)
    ·
      refine ⟨5235921742100655150093979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27924915957870160800501221 5235921742100655150093979)
      ·
        refine ⟨7853882613150982725140969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5235921742100655150093979 7853882613150982725140969)
        ·
          refine ⟨5890411959863237043855727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7853882613150982725140969 5890411959863237043855727)
          ·
            refine ⟨8835617939794855565783591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5890411959863237043855727 8835617939794855565783591)
            ·
              refine ⟨13253426909692283348675387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8835617939794855565783591 13253426909692283348675387)
              ·
                refine ⟨19880140364538425023013081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13253426909692283348675387 19880140364538425023013081)
                ·
                  refine ⟨14910105273403818767259811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19880140364538425023013081 14910105273403818767259811)
                  ·
                    refine ⟨22365157910105728150889717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14910105273403818767259811 22365157910105728150889717)
                    ·
                      refine ⟨2096733554072412014145911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22365157910105728150889717 2096733554072412014145911)
                      ·
                        rfl

theorem cell23_4083374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_4083374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4083374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4083374 prefixEnd_4083374 := by exact prefixLift 4083374
  have htrace : WordTrace (prefixWord ++ tailWord_4083374) baseStart_4083374 baseEnd_4083374 := by
    simpa [prefixWord, tailWord_4083374, baseEnd_4083374] using wordTrace_append hprefix tailTrace_4083374
  have hstable : (prefixWord ++ tailWord_4083374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4083374).length < 2 ^ (prefixWord ++ tailWord_4083374).sum := by decide
  have hdescent : baseEnd_4083374 < baseStart_4083374 := by decide
  rcases family_descends (prefixWord ++ tailWord_4083374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4083400 : List Nat := [2, 1, 3, 1, 2, 2, 3, 1, 1, 2, 5]
def baseStart_4083400 : Nat := 118140960795 + 4083400 * 2 ^ 59
def prefixEnd_4083400 : Nat := 4983230072969 + 3 ^ 40 * 4083400 * 2
def baseEnd_4083400 : Nat := 2096746904569428912420791

theorem tailTrace_4083400 : CollatzResearch.WordTrace tailWord_4083400 prefixEnd_4083400 2096746904569428912420791 := by
  unfold tailWord_4083400
  simp only [CollatzResearch.WordTrace]
  refine ⟨74466916703273332021559827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99289222271031109362079769 74466916703273332021559827)
  ·
    refine ⟨111700375054909998032339741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74466916703273332021559827 111700375054909998032339741)
    ·
      refine ⟨41887640645591249262127403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111700375054909998032339741 41887640645591249262127403)
      ·
        refine ⟨62831460968386873893191105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41887640645591249262127403 62831460968386873893191105)
        ·
          refine ⟨47123595726290155419893329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62831460968386873893191105 47123595726290155419893329)
          ·
            refine ⟨35342696794717616564919997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47123595726290155419893329 35342696794717616564919997)
            ·
              refine ⟨13253511298019106211844999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35342696794717616564919997 13253511298019106211844999)
              ·
                refine ⟨19880266947028659317767499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13253511298019106211844999 19880266947028659317767499)
                ·
                  refine ⟨29820400420542988976651249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19880266947028659317767499 29820400420542988976651249)
                  ·
                    refine ⟨22365300315407241732488437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29820400420542988976651249 22365300315407241732488437)
                    ·
                      refine ⟨2096746904569428912420791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22365300315407241732488437 2096746904569428912420791)
                      ·
                        rfl

theorem cell23_4083400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 1, 1, 2, 5].length) (baseStart_4083400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4083400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4083400 prefixEnd_4083400 := by exact prefixLift 4083400
  have htrace : WordTrace (prefixWord ++ tailWord_4083400) baseStart_4083400 baseEnd_4083400 := by
    simpa [prefixWord, tailWord_4083400, baseEnd_4083400] using wordTrace_append hprefix tailTrace_4083400
  have hstable : (prefixWord ++ tailWord_4083400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4083400).length < 2 ^ (prefixWord ++ tailWord_4083400).sum := by decide
  have hdescent : baseEnd_4083400 < baseStart_4083400 := by decide
  rcases family_descends (prefixWord ++ tailWord_4083400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4083405 : List Nat := [1, 6, 2, 1, 1, 1, 4, 1, 2, 2, 2]
def baseStart_4083405 : Nat := 118140960795 + 4083405 * 2 ^ 59
def prefixEnd_4083405 : Nat := 4983230072969 + 3 ^ 40 * 4083405 * 2
def baseEnd_4083405 : Nat := 2096749471972701392858269

theorem tailTrace_4083405 : CollatzResearch.WordTrace tailWord_4083405 prefixEnd_4083405 2096749471972701392858269 := by
  unfold tailWord_4083405
  simp only [CollatzResearch.WordTrace]
  refine ⟨148934015771528549897051669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99289343847685699931367779 148934015771528549897051669)
  ·
    refine ⟨6981281989290400776424297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 148934015771528549897051669 6981281989290400776424297)
    ·
      refine ⟨5235961491967800582318223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6981281989290400776424297 5235961491967800582318223)
      ·
        refine ⟨7853942237951700873477335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5235961491967800582318223 7853942237951700873477335)
        ·
          refine ⟨11780913356927551310216003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7853942237951700873477335 11780913356927551310216003)
          ·
            refine ⟨17671370035391326965324005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11780913356927551310216003 17671370035391326965324005)
            ·
              refine ⟨3313381881635873805998251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17671370035391326965324005 3313381881635873805998251)
              ·
                refine ⟨4970072822453810708997377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3313381881635873805998251 4970072822453810708997377)
                ·
                  refine ⟨3727554616840358031748033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4970072822453810708997377 3727554616840358031748033)
                  ·
                    refine ⟨2795665962630268523811025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3727554616840358031748033 2795665962630268523811025)
                    ·
                      refine ⟨2096749471972701392858269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2795665962630268523811025 2096749471972701392858269)
                      ·
                        rfl

theorem cell23_4083405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 4, 1, 2, 2, 2].length) (baseStart_4083405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4083405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4083405 prefixEnd_4083405 := by exact prefixLift 4083405
  have htrace : WordTrace (prefixWord ++ tailWord_4083405) baseStart_4083405 baseEnd_4083405 := by
    simpa [prefixWord, tailWord_4083405, baseEnd_4083405] using wordTrace_append hprefix tailTrace_4083405
  have hstable : (prefixWord ++ tailWord_4083405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4083405).length < 2 ^ (prefixWord ++ tailWord_4083405).sum := by decide
  have hdescent : baseEnd_4083405 < baseStart_4083405 := by decide
  rcases family_descends (prefixWord ++ tailWord_4083405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4083447 : List Nat := [1, 1, 3, 1, 1, 1, 6, 2, 2, 2, 3]
def baseStart_4083447 : Nat := 118140960795 + 4083447 * 2 ^ 59
def prefixEnd_4083447 : Nat := 4983230072969 + 3 ^ 40 * 4083447 * 2
def baseEnd_4083447 : Nat := 2096771038160190228533075

theorem tailTrace_4083447 : CollatzResearch.WordTrace tailWord_4083447 prefixEnd_4083447 2096771038160190228533075 := by
  unfold tailWord_4083447
  simp only [CollatzResearch.WordTrace]
  refine ⟨148935547637376391070080595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99290365091584260713387063 148935547637376391070080595)
  ·
    refine ⟨223403321456064586605120893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148935547637376391070080595 223403321456064586605120893)
    ·
      refine ⟨83776245546024219976920335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223403321456064586605120893 83776245546024219976920335)
      ·
        refine ⟨125664368319036329965380503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83776245546024219976920335 125664368319036329965380503)
        ·
          refine ⟨188496552478554494948070755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125664368319036329965380503 188496552478554494948070755)
          ·
            refine ⟨282744828717831742422106133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188496552478554494948070755 282744828717831742422106133)
            ·
              refine ⟨13253663846148362926036225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 282744828717831742422106133 13253663846148362926036225)
              ·
                refine ⟨9940247884611272194527169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13253663846148362926036225 9940247884611272194527169)
                ·
                  refine ⟨7455185913458454145895377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9940247884611272194527169 7455185913458454145895377)
                  ·
                    refine ⟨5591389435093840609421533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7455185913458454145895377 5591389435093840609421533)
                    ·
                      refine ⟨2096771038160190228533075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5591389435093840609421533 2096771038160190228533075)
                      ·
                        rfl

theorem cell23_4083447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 2, 2, 2, 3].length) (baseStart_4083447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4083447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4083447 prefixEnd_4083447 := by exact prefixLift 4083447
  have htrace : WordTrace (prefixWord ++ tailWord_4083447) baseStart_4083447 baseEnd_4083447 := by
    simpa [prefixWord, tailWord_4083447, baseEnd_4083447] using wordTrace_append hprefix tailTrace_4083447
  have hstable : (prefixWord ++ tailWord_4083447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4083447).length < 2 ^ (prefixWord ++ tailWord_4083447).sum := by decide
  have hdescent : baseEnd_4083447 < baseStart_4083447 := by decide
  rcases family_descends (prefixWord ++ tailWord_4083447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4083527 : List Nat := [1, 1, 4, 1, 2, 1, 5, 1, 1, 6]
def baseStart_4083527 : Nat := 118140960795 + 4083527 * 2 ^ 59
def prefixEnd_4083527 : Nat := 4983230072969 + 3 ^ 40 * 4083527 * 2
def baseEnd_4083527 : Nat := 698937372204183305177569

theorem tailTrace_4083527 : CollatzResearch.WordTrace tailWord_4083527 prefixEnd_4083527 698937372204183305177569 := by
  unfold tailWord_4083527
  simp only [CollatzResearch.WordTrace]
  refine ⟨148938465477086564732992835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99292310318057709821995223 148938465477086564732992835)
  ·
    refine ⟨223407698215629847099489253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148938465477086564732992835 223407698215629847099489253)
    ·
      refine ⟨41888943415430596331154235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 223407698215629847099489253 41888943415430596331154235)
      ·
        refine ⟨62833415123145894496731353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41888943415430596331154235 62833415123145894496731353)
        ·
          refine ⟨47125061342359420872548515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62833415123145894496731353 47125061342359420872548515)
          ·
            refine ⟨70687592013539131308822773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47125061342359420872548515 70687592013539131308822773)
            ·
              refine ⟨6626961751269293560202135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70687592013539131308822773 6626961751269293560202135)
              ·
                refine ⟨9940442626903940340303203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6626961751269293560202135 9940442626903940340303203)
                ·
                  refine ⟨14910663940355910510454805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9940442626903940340303203 14910663940355910510454805)
                  ·
                    refine ⟨698937372204183305177569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14910663940355910510454805 698937372204183305177569)
                    ·
                      rfl

theorem cell23_4083527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 5, 1, 1, 6].length) (baseStart_4083527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4083527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4083527 prefixEnd_4083527 := by exact prefixLift 4083527
  have htrace : WordTrace (prefixWord ++ tailWord_4083527) baseStart_4083527 baseEnd_4083527 := by
    simpa [prefixWord, tailWord_4083527, baseEnd_4083527] using wordTrace_append hprefix tailTrace_4083527
  have hstable : (prefixWord ++ tailWord_4083527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4083527).length < 2 ^ (prefixWord ++ tailWord_4083527).sum := by decide
  have hdescent : baseEnd_4083527 < baseStart_4083527 := by decide
  rcases family_descends (prefixWord ++ tailWord_4083527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4083554 : List Nat := [3, 3, 2, 1, 2, 1, 1, 3, 1, 1, 5]
def baseStart_4083554 : Nat := 118140960795 + 4083554 * 2 ^ 59
def prefixEnd_4083554 : Nat := 4983230072969 + 3 ^ 40 * 4083554 * 2
def baseEnd_4083554 : Nat := 2096825980590221309895083

theorem tailTrace_4083554 : CollatzResearch.WordTrace tailWord_4083554 prefixEnd_4083554 2096825980590221309895083 := by
  unfold tailWord_4083554
  simp only [CollatzResearch.WordTrace]
  refine ⟨37234862561997187086056429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99292966831992498896150477 37234862561997187086056429)
  ·
    refine ⟨13963073460748945157271161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37234862561997187086056429 13963073460748945157271161)
    ·
      refine ⟨10472305095561708867953371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13963073460748945157271161 10472305095561708867953371)
      ·
        refine ⟨15708457643342563301930057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10472305095561708867953371 15708457643342563301930057)
        ·
          refine ⟨11781343232506922476447543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15708457643342563301930057 11781343232506922476447543)
          ·
            refine ⟨17672014848760383714671315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11781343232506922476447543 17672014848760383714671315)
            ·
              refine ⟨26508022273140575572006973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17672014848760383714671315 26508022273140575572006973)
              ·
                refine ⟨9940508352427715839502615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26508022273140575572006973 9940508352427715839502615)
                ·
                  refine ⟨14910762528641573759253923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9940508352427715839502615 14910762528641573759253923)
                  ·
                    refine ⟨22366143792962360638880885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14910762528641573759253923 22366143792962360638880885)
                    ·
                      refine ⟨2096825980590221309895083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22366143792962360638880885 2096825980590221309895083)
                      ·
                        rfl

theorem cell23_4083554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_4083554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4083554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4083554 prefixEnd_4083554 := by exact prefixLift 4083554
  have htrace : WordTrace (prefixWord ++ tailWord_4083554) baseStart_4083554 baseEnd_4083554 := by
    simpa [prefixWord, tailWord_4083554, baseEnd_4083554] using wordTrace_append hprefix tailTrace_4083554
  have hstable : (prefixWord ++ tailWord_4083554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4083554).length < 2 ^ (prefixWord ++ tailWord_4083554).sum := by decide
  have hdescent : baseEnd_4083554 < baseStart_4083554 := by decide
  rcases family_descends (prefixWord ++ tailWord_4083554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4083562 : List Nat := [3, 1, 3, 4, 1, 1, 3, 2, 1, 1, 3]
def baseStart_4083562 : Nat := 118140960795 + 4083562 * 2 ^ 59
def prefixEnd_4083562 : Nat := 4983230072969 + 3 ^ 40 * 4083562 * 2
def baseEnd_4083562 : Nat := 2096830088435457278595047

theorem tailTrace_4083562 : CollatzResearch.WordTrace tailWord_4083562 prefixEnd_4083562 2096830088435457278595047 := by
  unfold tailWord_4083562
  simp only [CollatzResearch.WordTrace]
  refine ⟨37234935507989941427629235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99293161354639843807011293 37234935507989941427629235)
  ·
    refine ⟨55852403261984912141443853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37234935507989941427629235 55852403261984912141443853)
    ·
      refine ⟨20944651223244342053041445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55852403261984912141443853 20944651223244342053041445)
      ·
        refine ⟨3927122104358314134945271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20944651223244342053041445 3927122104358314134945271)
        ·
          refine ⟨5890683156537471202417907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3927122104358314134945271 5890683156537471202417907)
          ·
            refine ⟨8836024734806206803626861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5890683156537471202417907 8836024734806206803626861)
            ·
              refine ⟨3313509275552327551360073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8836024734806206803626861 3313509275552327551360073)
              ·
                refine ⟨2485131956664245663520055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3313509275552327551360073 2485131956664245663520055)
                ·
                  refine ⟨3727697934996368495280083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2485131956664245663520055 3727697934996368495280083)
                  ·
                    refine ⟨5591546902494552742920125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3727697934996368495280083 5591546902494552742920125)
                    ·
                      refine ⟨2096830088435457278595047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5591546902494552742920125 2096830088435457278595047)
                      ·
                        rfl

theorem cell23_4083562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 3, 2, 1, 1, 3].length) (baseStart_4083562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4083562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4083562 prefixEnd_4083562 := by exact prefixLift 4083562
  have htrace : WordTrace (prefixWord ++ tailWord_4083562) baseStart_4083562 baseEnd_4083562 := by
    simpa [prefixWord, tailWord_4083562, baseEnd_4083562] using wordTrace_append hprefix tailTrace_4083562
  have hstable : (prefixWord ++ tailWord_4083562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4083562).length < 2 ^ (prefixWord ++ tailWord_4083562).sum := by decide
  have hdescent : baseEnd_4083562 < baseStart_4083562 := by decide
  rcases family_descends (prefixWord ++ tailWord_4083562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4083585 : List Nat := [1, 2, 4, 4, 2, 1, 1, 2, 1, 1, 4]
def baseStart_4083585 : Nat := 118140960795 + 4083585 * 2 ^ 59
def prefixEnd_4083585 : Nat := 4983230072969 + 3 ^ 40 * 4083585 * 2
def baseEnd_4083585 : Nat := 2096841898490510688607441

theorem tailTrace_4083585 : CollatzResearch.WordTrace tailWord_4083585 prefixEnd_4083585 2096841898490510688607441 := by
  unfold tailWord_4083585
  simp only [CollatzResearch.WordTrace]
  refine ⟨148940580910876440638604209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99293720607250960425736139 148940580910876440638604209)
  ·
    refine ⟨111705435683157330478953157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148940580910876440638604209 111705435683157330478953157)
    ·
      refine ⟨20944769190591999464803717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111705435683157330478953157 20944769190591999464803717)
      ·
        refine ⟨3927144223235999899650697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20944769190591999464803717 3927144223235999899650697)
        ·
          refine ⟨2945358167426999924738023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3927144223235999899650697 2945358167426999924738023)
          ·
            refine ⟨4418037251140499887107035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2945358167426999924738023 4418037251140499887107035)
            ·
              refine ⟨6627055876710749830660553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4418037251140499887107035 6627055876710749830660553)
              ·
                refine ⟨4970291907533062372995415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6627055876710749830660553 4970291907533062372995415)
                ·
                  refine ⟨7455437861299593559493123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4970291907533062372995415 7455437861299593559493123)
                  ·
                    refine ⟨11183156791949390339239685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7455437861299593559493123 11183156791949390339239685)
                    ·
                      refine ⟨2096841898490510688607441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11183156791949390339239685 2096841898490510688607441)
                      ·
                        rfl

theorem cell23_4083585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_4083585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4083585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4083585 prefixEnd_4083585 := by exact prefixLift 4083585
  have htrace : WordTrace (prefixWord ++ tailWord_4083585) baseStart_4083585 baseEnd_4083585 := by
    simpa [prefixWord, tailWord_4083585, baseEnd_4083585] using wordTrace_append hprefix tailTrace_4083585
  have hstable : (prefixWord ++ tailWord_4083585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4083585).length < 2 ^ (prefixWord ++ tailWord_4083585).sum := by decide
  have hdescent : baseEnd_4083585 < baseStart_4083585 := by decide
  rcases family_descends (prefixWord ++ tailWord_4083585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4083641 : List Nat := [1, 2, 1, 4, 2, 1, 4, 1, 1, 4, 2]
def baseStart_4083641 : Nat := 118140960795 + 4083641 * 2 ^ 59
def prefixEnd_4083641 : Nat := 4983230072969 + 3 ^ 40 * 4083641 * 2
def baseEnd_4083641 : Nat := 2096870653407162469507183

theorem tailTrace_4083641 : CollatzResearch.WordTrace tailWord_4083641 prefixEnd_4083641 2096870653407162469507183 := by
  unfold tailWord_4083641
  simp only [CollatzResearch.WordTrace]
  refine ⟨148942623398673562202642777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99295082265782374801761851 148942623398673562202642777)
  ·
    refine ⟨111706967549005171651982083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148942623398673562202642777 111706967549005171651982083)
    ·
      refine ⟨167560451323507757477973125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111706967549005171651982083 167560451323507757477973125)
      ·
        refine ⟨31417584623157704527119961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 167560451323507757477973125 31417584623157704527119961)
        ·
          refine ⟨23563188467368278395339971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31417584623157704527119961 23563188467368278395339971)
          ·
            refine ⟨35344782701052417593009957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23563188467368278395339971 35344782701052417593009957)
            ·
              refine ⟨6627146756447328298689367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35344782701052417593009957 6627146756447328298689367)
              ·
                refine ⟨9940720134670992448034051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6627146756447328298689367 9940720134670992448034051)
                ·
                  refine ⟨14911080202006488672051077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9940720134670992448034051 14911080202006488672051077)
                  ·
                    refine ⟨2795827537876216626009577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14911080202006488672051077 2795827537876216626009577)
                    ·
                      refine ⟨2096870653407162469507183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2795827537876216626009577 2096870653407162469507183)
                      ·
                        rfl

theorem cell23_4083641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 4, 1, 1, 4, 2].length) (baseStart_4083641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4083641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4083641 prefixEnd_4083641 := by exact prefixLift 4083641
  have htrace : WordTrace (prefixWord ++ tailWord_4083641) baseStart_4083641 baseEnd_4083641 := by
    simpa [prefixWord, tailWord_4083641, baseEnd_4083641] using wordTrace_append hprefix tailTrace_4083641
  have hstable : (prefixWord ++ tailWord_4083641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4083641).length < 2 ^ (prefixWord ++ tailWord_4083641).sum := by decide
  have hdescent : baseEnd_4083641 < baseStart_4083641 := by decide
  rcases family_descends (prefixWord ++ tailWord_4083641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4083647 : List Nat := [1, 1, 2, 2, 2, 1, 5, 2, 7]
def baseStart_4083647 : Nat := 118140960795 + 4083647 * 2 ^ 59
def prefixEnd_4083647 : Nat := 4983230072969 + 3 ^ 40 * 4083647 * 2
def baseEnd_4083647 : Nat := 232985970476787716225795

theorem tailTrace_4083647 : CollatzResearch.WordTrace tailWord_4083647 prefixEnd_4083647 232985970476787716225795 := by
  unfold tailWord_4083647
  simp only [CollatzResearch.WordTrace]
  refine ⟨148942842236651825227361195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99295228157767883484907463 148942842236651825227361195)
  ·
    refine ⟨223414263354977737841041793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148942842236651825227361195 223414263354977737841041793)
    ·
      refine ⟨167560697516233303380781345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223414263354977737841041793 167560697516233303380781345)
      ·
        refine ⟨125670523137174977535586009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167560697516233303380781345 125670523137174977535586009)
        ·
          refine ⟨94252892352881233151689507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125670523137174977535586009 94252892352881233151689507)
          ·
            refine ⟨141379338529321849727534261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94252892352881233151689507 141379338529321849727534261)
            ·
              refine ⟨13254312987123923411956337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 141379338529321849727534261 13254312987123923411956337)
              ·
                refine ⟨9940734740342942558967253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13254312987123923411956337 9940734740342942558967253)
                ·
                  refine ⟨232985970476787716225795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9940734740342942558967253 232985970476787716225795)
                  ·
                    rfl

theorem cell23_4083647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 2, 7].length) (baseStart_4083647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4083647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4083647 prefixEnd_4083647 := by exact prefixLift 4083647
  have htrace : WordTrace (prefixWord ++ tailWord_4083647) baseStart_4083647 baseEnd_4083647 := by
    simpa [prefixWord, tailWord_4083647, baseEnd_4083647] using wordTrace_append hprefix tailTrace_4083647
  have hstable : (prefixWord ++ tailWord_4083647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4083647).length < 2 ^ (prefixWord ++ tailWord_4083647).sum := by decide
  have hdescent : baseEnd_4083647 < baseStart_4083647 := by decide
  rcases family_descends (prefixWord ++ tailWord_4083647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4083664 : List Nat := [2, 1, 1, 1, 1, 2, 5, 5, 5]
def baseStart_4083664 : Nat := 118140960795 + 4083664 * 2 ^ 59
def prefixEnd_4083664 : Nat := 4983230072969 + 3 ^ 40 * 4083664 * 2
def baseEnd_4083664 : Nat := 232986940384690653279953

theorem tailTrace_4083664 : CollatzResearch.WordTrace tailWord_4083664 prefixEnd_4083664 232986940384690653279953 := by
  unfold tailWord_4083664
  simp only [CollatzResearch.WordTrace]
  refine ⟨74471731138795118565365023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99295641518393491420486697 74471731138795118565365023)
  ·
    refine ⟨111707596708192677848047535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74471731138795118565365023 111707596708192677848047535)
    ·
      refine ⟨167561395062289016772071303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111707596708192677848047535 167561395062289016772071303)
      ·
        refine ⟨251342092593433525158106955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167561395062289016772071303 251342092593433525158106955)
        ·
          refine ⟨377013138890150287737160433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251342092593433525158106955 377013138890150287737160433)
          ·
            refine ⟨282759854167612715802870325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 377013138890150287737160433 282759854167612715802870325)
            ·
              refine ⟨26508736328213692106519093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 282759854167612715802870325 26508736328213692106519093)
              ·
                refine ⟨2485194030770033634986165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26508736328213692106519093 2485194030770033634986165)
                ·
                  refine ⟨232986940384690653279953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2485194030770033634986165 232986940384690653279953)
                  ·
                    rfl

theorem cell23_4083664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 5, 5].length) (baseStart_4083664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4083664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4083664 prefixEnd_4083664 := by exact prefixLift 4083664
  have htrace : WordTrace (prefixWord ++ tailWord_4083664) baseStart_4083664 baseEnd_4083664 := by
    simpa [prefixWord, tailWord_4083664, baseEnd_4083664] using wordTrace_append hprefix tailTrace_4083664
  have hstable : (prefixWord ++ tailWord_4083664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4083664).length < 2 ^ (prefixWord ++ tailWord_4083664).sum := by decide
  have hdescent : baseEnd_4083664 < baseStart_4083664 := by decide
  rcases family_descends (prefixWord ++ tailWord_4083664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4083694 : List Nat := [4, 1, 2, 1, 3, 1, 1, 2, 1, 7]
def baseStart_4083694 : Nat := 118140960795 + 4083694 * 2 ^ 59
def prefixEnd_4083694 : Nat := 4983230072969 + 3 ^ 40 * 4083694 * 2
def baseEnd_4083694 : Nat := 698965955960616920714813

theorem tailTrace_4083694 : CollatzResearch.WordTrace tailWord_4083694 prefixEnd_4083694 698965955960616920714813 := by
  unfold tailWord_4083694
  simp only [CollatzResearch.WordTrace]
  refine ⟨18618069558435194031790267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99296370978321034836214757 18618069558435194031790267)
  ·
    refine ⟨27927104337652791047685401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18618069558435194031790267 27927104337652791047685401)
    ·
      refine ⟨20945328253239593285764051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27927104337652791047685401 20945328253239593285764051)
      ·
        refine ⟨31417992379859389928646077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20945328253239593285764051 31417992379859389928646077)
        ·
          refine ⟨11781747142447271223242279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31417992379859389928646077 11781747142447271223242279)
          ·
            refine ⟨17672620713670906834863419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11781747142447271223242279 17672620713670906834863419)
            ·
              refine ⟨26508931070506360252295129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17672620713670906834863419 26508931070506360252295129)
              ·
                refine ⟨19881698302879770189221347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26508931070506360252295129 19881698302879770189221347)
                ·
                  refine ⟨29822547454319655283832021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19881698302879770189221347 29822547454319655283832021)
                  ·
                    refine ⟨698965955960616920714813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29822547454319655283832021 698965955960616920714813)
                    ·
                      rfl

theorem cell23_4083694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 2, 1, 7].length) (baseStart_4083694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4083694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4083694 prefixEnd_4083694 := by exact prefixLift 4083694
  have htrace : WordTrace (prefixWord ++ tailWord_4083694) baseStart_4083694 baseEnd_4083694 := by
    simpa [prefixWord, tailWord_4083694, baseEnd_4083694] using wordTrace_append hprefix tailTrace_4083694
  have hstable : (prefixWord ++ tailWord_4083694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4083694).length < 2 ^ (prefixWord ++ tailWord_4083694).sum := by decide
  have hdescent : baseEnd_4083694 < baseStart_4083694 := by decide
  rcases family_descends (prefixWord ++ tailWord_4083694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4083732 : List Nat := [2, 4, 3, 2, 1, 1, 3, 2, 5]
def baseStart_4083732 : Nat := 118140960795 + 4083732 * 2 ^ 59
def prefixEnd_4083732 : Nat := 4983230072969 + 3 ^ 40 * 4083732 * 2
def baseEnd_4083732 : Nat := 232990820016302401496585

theorem tailTrace_4083732 : CollatzResearch.WordTrace tailWord_4083732 prefixEnd_4083732 232990820016302401496585 := by
  unfold tailWord_4083732
  simp only [CollatzResearch.WordTrace]
  refine ⟨74472971220671942372102725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99297294960895923162803633 74472971220671942372102725)
  ·
    refine ⟨13963682103875989194769261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74472971220671942372102725 13963682103875989194769261)
    ·
      refine ⟨5236380788953495948038473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13963682103875989194769261 5236380788953495948038473)
      ·
        refine ⟨3927285591715121961028855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5236380788953495948038473 3927285591715121961028855)
        ·
          refine ⟨5890928387572682941543283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3927285591715121961028855 5890928387572682941543283)
          ·
            refine ⟨8836392581359024412314925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5890928387572682941543283 8836392581359024412314925)
            ·
              refine ⟨3313647218009634154618097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8836392581359024412314925 3313647218009634154618097)
              ·
                refine ⟨2485235413507225615963573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3313647218009634154618097 2485235413507225615963573)
                ·
                  refine ⟨232990820016302401496585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2485235413507225615963573 232990820016302401496585)
                  ·
                    rfl

theorem cell23_4083732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 3, 2, 5].length) (baseStart_4083732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4083732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4083732 prefixEnd_4083732 := by exact prefixLift 4083732
  have htrace : WordTrace (prefixWord ++ tailWord_4083732) baseStart_4083732 baseEnd_4083732 := by
    simpa [prefixWord, tailWord_4083732, baseEnd_4083732] using wordTrace_append hprefix tailTrace_4083732
  have hstable : (prefixWord ++ tailWord_4083732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4083732).length < 2 ^ (prefixWord ++ tailWord_4083732).sum := by decide
  have hdescent : baseEnd_4083732 < baseStart_4083732 := by decide
  rcases family_descends (prefixWord ++ tailWord_4083732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4083768 : List Nat := [2, 1, 2, 1, 6, 1, 2, 1, 2, 2, 3]
def baseStart_4083768 : Nat := 118140960795 + 4083768 * 2 ^ 59
def prefixEnd_4083768 : Nat := 4983230072969 + 3 ^ 40 * 4083768 * 2
def baseEnd_4083768 : Nat := 2096935865450283472619099

theorem tailTrace_4083768 : CollatzResearch.WordTrace tailWord_4083768 prefixEnd_4083768 2096935865450283472619099 := by
  unfold tailWord_4083768
  simp only [CollatzResearch.WordTrace]
  refine ⟨74473627734606731446257979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99298170312808975261677305 74473627734606731446257979)
  ·
    refine ⟨111710441601910097169386969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74473627734606731446257979 111710441601910097169386969)
    ·
      refine ⟨83782831201432572877040227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111710441601910097169386969 83782831201432572877040227)
      ·
        refine ⟨125674246802148859315560341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83782831201432572877040227 125674246802148859315560341)
        ·
          refine ⟨5890980318850727780416891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 125674246802148859315560341 5890980318850727780416891)
          ·
            refine ⟨8836470478276091670625337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5890980318850727780416891 8836470478276091670625337)
            ·
              refine ⟨6627352858707068752969003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8836470478276091670625337 6627352858707068752969003)
              ·
                refine ⟨9941029288060603129453505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6627352858707068752969003 9941029288060603129453505)
                ·
                  refine ⟨7455771966045452347090129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9941029288060603129453505 7455771966045452347090129)
                  ·
                    refine ⟨5591828974534089260317597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7455771966045452347090129 5591828974534089260317597)
                    ·
                      refine ⟨2096935865450283472619099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5591828974534089260317597 2096935865450283472619099)
                      ·
                        rfl

theorem cell23_4083768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 2, 1, 2, 2, 3].length) (baseStart_4083768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4083768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4083768 prefixEnd_4083768 := by exact prefixLift 4083768
  have htrace : WordTrace (prefixWord ++ tailWord_4083768) baseStart_4083768 baseEnd_4083768 := by
    simpa [prefixWord, tailWord_4083768, baseEnd_4083768] using wordTrace_append hprefix tailTrace_4083768
  have hstable : (prefixWord ++ tailWord_4083768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4083768).length < 2 ^ (prefixWord ++ tailWord_4083768).sum := by decide
  have hdescent : baseEnd_4083768 < baseStart_4083768 := by decide
  rcases family_descends (prefixWord ++ tailWord_4083768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4083821 : List Nat := [1, 5, 1, 1, 2, 1, 1, 3, 3, 1, 4]
def baseStart_4083821 : Nat := 118140960795 + 4083821 * 2 ^ 59
def prefixEnd_4083821 : Nat := 4983230072969 + 3 ^ 40 * 4083821 * 2
def baseEnd_4083821 : Nat := 2096963079924971765256355

theorem tailTrace_4083821 : CollatzResearch.WordTrace tailWord_4083821 prefixEnd_4083821 2096963079924971765256355 := by
  unfold tailWord_4083821
  simp only [CollatzResearch.WordTrace]
  refine ⟨148949188538021452944195317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99299459025347635296130211 148949188538021452944195317)
  ·
    refine ⟨13963986425439511213518311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 148949188538021452944195317 13963986425439511213518311)
    ·
      refine ⟨20945979638159266820277467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13963986425439511213518311 20945979638159266820277467)
      ·
        refine ⟨31418969457238900230416201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20945979638159266820277467 31418969457238900230416201)
        ·
          refine ⟨23564227092929175172812151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31418969457238900230416201 23564227092929175172812151)
          ·
            refine ⟨35346340639393762759218227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23564227092929175172812151 35346340639393762759218227)
            ·
              refine ⟨53019510959090644138827341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35346340639393762759218227 53019510959090644138827341)
              ·
                refine ⟨19882316609658991552060253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53019510959090644138827341 19882316609658991552060253)
                ·
                  refine ⟨7455868728622121832022595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19882316609658991552060253 7455868728622121832022595)
                  ·
                    refine ⟨11183803092933182748033893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7455868728622121832022595 11183803092933182748033893)
                    ·
                      refine ⟨2096963079924971765256355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11183803092933182748033893 2096963079924971765256355)
                      ·
                        rfl

theorem cell23_4083821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 3, 3, 1, 4].length) (baseStart_4083821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4083821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4083821 prefixEnd_4083821 := by exact prefixLift 4083821
  have htrace : WordTrace (prefixWord ++ tailWord_4083821) baseStart_4083821 baseEnd_4083821 := by
    simpa [prefixWord, tailWord_4083821, baseEnd_4083821] using wordTrace_append hprefix tailTrace_4083821
  have hstable : (prefixWord ++ tailWord_4083821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4083821).length < 2 ^ (prefixWord ++ tailWord_4083821).sum := by decide
  have hdescent : baseEnd_4083821 < baseStart_4083821 := by decide
  rcases family_descends (prefixWord ++ tailWord_4083821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4083844 : List Nat := [2, 3, 2, 1, 2, 1, 12]
def baseStart_4083844 : Nat := 118140960795 + 4083844 * 2 ^ 59
def prefixEnd_4083844 : Nat := 4983230072969 + 3 ^ 40 * 4083844 * 2
def baseEnd_4083844 : Nat := 25888578888642286114429

theorem tailTrace_4083844 : CollatzResearch.WordTrace tailWord_4083844 prefixEnd_4083844 25888578888642286114429 := by
  unfold tailWord_4083844
  simp only [CollatzResearch.WordTrace]
  refine ⟨74475013708469063936141293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99300018277958751914855057 74475013708469063936141293)
  ·
    refine ⟨27928130140675898976052985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74475013708469063936141293 27928130140675898976052985)
    ·
      refine ⟨20946097605506924232039739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27928130140675898976052985 20946097605506924232039739)
      ·
        refine ⟨31419146408260386348059609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20946097605506924232039739 31419146408260386348059609)
        ·
          refine ⟨23564359806195289761044707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31419146408260386348059609 23564359806195289761044707)
          ·
            refine ⟨35346539709292934641567061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23564359806195289761044707 35346539709292934641567061)
            ·
              refine ⟨25888578888642286114429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 35346539709292934641567061 25888578888642286114429)
              ·
                rfl

theorem cell23_4083844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 12].length) (baseStart_4083844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4083844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4083844 prefixEnd_4083844 := by exact prefixLift 4083844
  have htrace : WordTrace (prefixWord ++ tailWord_4083844) baseStart_4083844 baseEnd_4083844 := by
    simpa [prefixWord, tailWord_4083844, baseEnd_4083844] using wordTrace_append hprefix tailTrace_4083844
  have hstable : (prefixWord ++ tailWord_4083844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4083844).length < 2 ^ (prefixWord ++ tailWord_4083844).sum := by decide
  have hdescent : baseEnd_4083844 < baseStart_4083844 := by decide
  rcases family_descends (prefixWord ++ tailWord_4083844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4083848 : List Nat := [2, 1, 3, 4, 1, 2, 1, 1, 4, 4]
def baseStart_4083848 : Nat := 118140960795 + 4083848 * 2 ^ 59
def prefixEnd_4083848 : Nat := 4983230072969 + 3 ^ 40 * 4083848 * 2
def baseEnd_4083848 : Nat := 698992314634214386539577

theorem tailTrace_4083848 : CollatzResearch.WordTrace tailWord_4083848 prefixEnd_4083848 698992314634214386539577 := by
  unfold tailWord_4083848
  simp only [CollatzResearch.WordTrace]
  refine ⟨74475086654461818277714099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99300115539282424370285465 74475086654461818277714099)
  ·
    refine ⟨111712629981692727416571149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74475086654461818277714099 111712629981692727416571149)
    ·
      refine ⟨41892236243134772781214181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111712629981692727416571149 41892236243134772781214181)
      ·
        refine ⟨7854794295587769896477659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41892236243134772781214181 7854794295587769896477659)
        ·
          refine ⟨11782191443381654844716489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7854794295587769896477659 11782191443381654844716489)
          ·
            refine ⟨8836643582536241133537367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11782191443381654844716489 8836643582536241133537367)
            ·
              refine ⟨13254965373804361700306051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8836643582536241133537367 13254965373804361700306051)
              ·
                refine ⟨19882448060706542550459077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13254965373804361700306051 19882448060706542550459077)
                ·
                  refine ⟨3727959011382476728211077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19882448060706542550459077 3727959011382476728211077)
                  ·
                    refine ⟨698992314634214386539577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3727959011382476728211077 698992314634214386539577)
                    ·
                      rfl

theorem cell23_4083848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 1, 4, 4].length) (baseStart_4083848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4083848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4083848 prefixEnd_4083848 := by exact prefixLift 4083848
  have htrace : WordTrace (prefixWord ++ tailWord_4083848) baseStart_4083848 baseEnd_4083848 := by
    simpa [prefixWord, tailWord_4083848, baseEnd_4083848] using wordTrace_append hprefix tailTrace_4083848
  have hstable : (prefixWord ++ tailWord_4083848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4083848).length < 2 ^ (prefixWord ++ tailWord_4083848).sum := by decide
  have hdescent : baseEnd_4083848 < baseStart_4083848 := by decide
  rcases family_descends (prefixWord ++ tailWord_4083848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4083906 : List Nat := [3, 5, 1, 1, 1, 3, 1, 1, 3, 2, 2]
def baseStart_4083906 : Nat := 118140960795 + 4083906 * 2 ^ 59
def prefixEnd_4083906 : Nat := 4983230072969 + 3 ^ 40 * 4083906 * 2
def baseEnd_4083906 : Nat := 2097006725780603932693465

theorem tailTrace_4083906 : CollatzResearch.WordTrace tailWord_4083906 prefixEnd_4083906 2097006725780603932693465 := by
  unfold tailWord_4083906
  simp only [CollatzResearch.WordTrace]
  refine ⟨37238072185678378115259893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99301525828475674974026381 37238072185678378115259893)
  ·
    refine ⟨3491069267407347948305615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37238072185678378115259893 3491069267407347948305615)
    ·
      refine ⟨5236603901111021922458423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3491069267407347948305615 5236603901111021922458423)
      ·
        refine ⟨7854905851666532883687635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5236603901111021922458423 7854905851666532883687635)
        ·
          refine ⟨11782358777499799325531453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7854905851666532883687635 11782358777499799325531453)
          ·
            refine ⟨4418384541562424747074295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11782358777499799325531453 4418384541562424747074295)
            ·
              refine ⟨6627576812343637120611443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4418384541562424747074295 6627576812343637120611443)
              ·
                refine ⟨9941365218515455680917165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6627576812343637120611443 9941365218515455680917165)
                ·
                  refine ⟨3728011956943295880343937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9941365218515455680917165 3728011956943295880343937)
                  ·
                    refine ⟨2796008967707471910257953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3728011956943295880343937 2796008967707471910257953)
                    ·
                      refine ⟨2097006725780603932693465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2796008967707471910257953 2097006725780603932693465)
                      ·
                        rfl

theorem cell23_4083906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 1, 1, 3, 2, 2].length) (baseStart_4083906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4083906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4083906 prefixEnd_4083906 := by exact prefixLift 4083906
  have htrace : WordTrace (prefixWord ++ tailWord_4083906) baseStart_4083906 baseEnd_4083906 := by
    simpa [prefixWord, tailWord_4083906, baseEnd_4083906] using wordTrace_append hprefix tailTrace_4083906
  have hstable : (prefixWord ++ tailWord_4083906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4083906).length < 2 ^ (prefixWord ++ tailWord_4083906).sum := by decide
  have hdescent : baseEnd_4083906 < baseStart_4083906 := by decide
  rcases family_descends (prefixWord ++ tailWord_4083906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4083922 : List Nat := [3, 2, 2, 2, 1, 2, 4, 1, 2, 1, 3]
def baseStart_4083922 : Nat := 118140960795 + 4083922 * 2 ^ 59
def prefixEnd_4083922 : Nat := 4983230072969 + 3 ^ 40 * 4083922 * 2
def baseEnd_4083922 : Nat := 2097014941471075870093391

theorem tailTrace_4083922 : CollatzResearch.WordTrace tailWord_4083922 prefixEnd_4083922 2097014941471075870093391 := by
  unfold tailWord_4083922
  simp only [CollatzResearch.WordTrace]
  refine ⟨37238218077663886798405505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99301914873770364795748013 37238218077663886798405505)
  ·
    refine ⟨27928663558247915098804129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37238218077663886798405505 27928663558247915098804129)
    ·
      refine ⟨20946497668685936324103097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27928663558247915098804129 20946497668685936324103097)
      ·
        refine ⟨15709873251514452243077323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20946497668685936324103097 15709873251514452243077323)
        ·
          refine ⟨23564809877271678364615985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15709873251514452243077323 23564809877271678364615985)
          ·
            refine ⟨17673607407953758773461989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23564809877271678364615985 17673607407953758773461989)
            ·
              refine ⟨3313801388991329770024123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17673607407953758773461989 3313801388991329770024123)
              ·
                refine ⟨4970702083486994655036185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3313801388991329770024123 4970702083486994655036185)
                ·
                  refine ⟨3728026562615245991277139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4970702083486994655036185 3728026562615245991277139)
                  ·
                    refine ⟨5592039843922868986915709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3728026562615245991277139 5592039843922868986915709)
                    ·
                      refine ⟨2097014941471075870093391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5592039843922868986915709 2097014941471075870093391)
                      ·
                        rfl

theorem cell23_4083922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 4, 1, 2, 1, 3].length) (baseStart_4083922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4083922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4083922 prefixEnd_4083922 := by exact prefixLift 4083922
  have htrace : WordTrace (prefixWord ++ tailWord_4083922) baseStart_4083922 baseEnd_4083922 := by
    simpa [prefixWord, tailWord_4083922, baseEnd_4083922] using wordTrace_append hprefix tailTrace_4083922
  have hstable : (prefixWord ++ tailWord_4083922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4083922).length < 2 ^ (prefixWord ++ tailWord_4083922).sum := by decide
  have hdescent : baseEnd_4083922 < baseStart_4083922 := by decide
  rcases family_descends (prefixWord ++ tailWord_4083922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4083949 : List Nat := [1, 5, 1, 2, 3, 1, 3, 1, 1, 3, 2]
def baseStart_4083949 : Nat := 118140960795 + 4083949 * 2 ^ 59
def prefixEnd_4083949 : Nat := 4983230072969 + 3 ^ 40 * 4083949 * 2
def baseEnd_4083949 : Nat := 2097028805448747264455767

theorem tailTrace_4083949 : CollatzResearch.WordTrace tailWord_4083949 prefixEnd_4083949 2097028805448747264455767 := by
  unfold tailWord_4083949
  simp only [CollatzResearch.WordTrace]
  refine ⟨148953857081557730804854901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99302571387705153869903267 148953857081557730804854901)
  ·
    refine ⟨13964424101396037262955147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 148953857081557730804854901 13964424101396037262955147)
    ·
      refine ⟨20946636152094055894432721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13964424101396037262955147 20946636152094055894432721)
      ·
        refine ⟨15709977114070541920824541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20946636152094055894432721 15709977114070541920824541)
        ·
          refine ⟨5891241417776453220309203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15709977114070541920824541 5891241417776453220309203)
          ·
            refine ⟨8836862126664679830463805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5891241417776453220309203 8836862126664679830463805)
            ·
              refine ⟨3313823297499254936423927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8836862126664679830463805 3313823297499254936423927)
              ·
                refine ⟨4970734946248882404635891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3313823297499254936423927 4970734946248882404635891)
                ·
                  refine ⟨7456102419373323606953837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4970734946248882404635891 7456102419373323606953837)
                  ·
                    refine ⟨2796038407264996352607689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7456102419373323606953837 2796038407264996352607689)
                    ·
                      refine ⟨2097028805448747264455767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2796038407264996352607689 2097028805448747264455767)
                      ·
                        rfl

theorem cell23_4083949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 3, 1, 1, 3, 2].length) (baseStart_4083949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4083949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4083949 prefixEnd_4083949 := by exact prefixLift 4083949
  have htrace : WordTrace (prefixWord ++ tailWord_4083949) baseStart_4083949 baseEnd_4083949 := by
    simpa [prefixWord, tailWord_4083949, baseEnd_4083949] using wordTrace_append hprefix tailTrace_4083949
  have hstable : (prefixWord ++ tailWord_4083949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4083949).length < 2 ^ (prefixWord ++ tailWord_4083949).sum := by decide
  have hdescent : baseEnd_4083949 < baseStart_4083949 := by decide
  rcases family_descends (prefixWord ++ tailWord_4083949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4083962 : List Nat := [3, 1, 1, 1, 1, 6, 2, 2, 2, 2, 2]
def baseStart_4083962 : Nat := 118140960795 + 4083962 * 2 ^ 59
def prefixEnd_4083962 : Nat := 4983230072969 + 3 ^ 40 * 4083962 * 2
def baseEnd_4083962 : Nat := 2097035480697255713593207

theorem tailTrace_4083962 : CollatzResearch.WordTrace tailWord_4083962 prefixEnd_4083962 2097035480697255713593207 := by
  unfold tailWord_4083962
  simp only [CollatzResearch.WordTrace]
  refine ⟨37238582807627658506269535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99302887487007089350052093 37238582807627658506269535)
  ·
    refine ⟨55857874211441487759404303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37238582807627658506269535 55857874211441487759404303)
    ·
      refine ⟨83786811317162231639106455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55857874211441487759404303 83786811317162231639106455)
      ·
        refine ⟨125680216975743347458659683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83786811317162231639106455 125680216975743347458659683)
        ·
          refine ⟨188520325463615021187989525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125680216975743347458659683 188520325463615021187989525)
          ·
            refine ⟨8836890256106954118187009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 188520325463615021187989525 8836890256106954118187009)
            ·
              refine ⟨6627667692080215588640257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8836890256106954118187009 6627667692080215588640257)
              ·
                refine ⟨4970750769060161691480193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6627667692080215588640257 4970750769060161691480193)
                ·
                  refine ⟨3728063076795121268610145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4970750769060161691480193 3728063076795121268610145)
                  ·
                    refine ⟨2796047307596340951457609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3728063076795121268610145 2796047307596340951457609)
                    ·
                      refine ⟨2097035480697255713593207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2796047307596340951457609 2097035480697255713593207)
                      ·
                        rfl

theorem cell23_4083962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 2, 2, 2, 2, 2].length) (baseStart_4083962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4083962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4083962 prefixEnd_4083962 := by exact prefixLift 4083962
  have htrace : WordTrace (prefixWord ++ tailWord_4083962) baseStart_4083962 baseEnd_4083962 := by
    simpa [prefixWord, tailWord_4083962, baseEnd_4083962] using wordTrace_append hprefix tailTrace_4083962
  have hstable : (prefixWord ++ tailWord_4083962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4083962).length < 2 ^ (prefixWord ++ tailWord_4083962).sum := by decide
  have hdescent : baseEnd_4083962 < baseStart_4083962 := by decide
  rcases family_descends (prefixWord ++ tailWord_4083962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4083975 : List Nat := [1, 1, 4, 5, 1, 1, 1, 1, 2, 2, 4]
def baseStart_4083975 : Nat := 118140960795 + 4083975 * 2 ^ 59
def prefixEnd_4083975 : Nat := 4983230072969 + 3 ^ 40 * 4083975 * 2
def baseEnd_4083975 : Nat := 2097042155945764162730647

theorem tailTrace_4083975 : CollatzResearch.WordTrace tailWord_4083975 prefixEnd_4083975 2097042155945764162730647 := by
  unfold tailWord_4083975
  simp only [CollatzResearch.WordTrace]
  refine ⟨148954805379463537245301379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99303203586309024830200919 148954805379463537245301379)
  ·
    refine ⟨223432208069195305867952069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148954805379463537245301379 223432208069195305867952069)
    ·
      refine ⟨41893539012974119850241013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 223432208069195305867952069 41893539012974119850241013)
      ·
        refine ⟨3927519282466323735960095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41893539012974119850241013 3927519282466323735960095)
        ·
          refine ⟨5891278923699485603940143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3927519282466323735960095 5891278923699485603940143)
          ·
            refine ⟨8836918385549228405910215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5891278923699485603940143 8836918385549228405910215)
            ·
              refine ⟨13255377578323842608865323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8836918385549228405910215 13255377578323842608865323)
              ·
                refine ⟨19883066367485763913297985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13255377578323842608865323 19883066367485763913297985)
                ·
                  refine ⟨14912299775614322934973489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19883066367485763913297985 14912299775614322934973489)
                  ·
                    refine ⟨11184224831710742201230117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14912299775614322934973489 11184224831710742201230117)
                    ·
                      refine ⟨2097042155945764162730647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11184224831710742201230117 2097042155945764162730647)
                      ·
                        rfl

theorem cell23_4083975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_4083975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4083975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4083975 prefixEnd_4083975 := by exact prefixLift 4083975
  have htrace : WordTrace (prefixWord ++ tailWord_4083975) baseStart_4083975 baseEnd_4083975 := by
    simpa [prefixWord, tailWord_4083975, baseEnd_4083975] using wordTrace_append hprefix tailTrace_4083975
  have hstable : (prefixWord ++ tailWord_4083975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4083975).length < 2 ^ (prefixWord ++ tailWord_4083975).sum := by decide
  have hdescent : baseEnd_4083975 < baseStart_4083975 := by decide
  rcases family_descends (prefixWord ++ tailWord_4083975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4084013 : List Nat := [1, 5, 3, 1, 3, 1, 1, 2, 2, 2, 2]
def baseStart_4084013 : Nat := 118140960795 + 4084013 * 2 ^ 59
def prefixEnd_4084013 : Nat := 4983230072969 + 3 ^ 40 * 4084013 * 2
def baseEnd_4084013 : Nat := 2097061668210635014055473

theorem tailTrace_4084013 : CollatzResearch.WordTrace tailWord_4084013 prefixEnd_4084013 2097061668210635014055473 := by
  unfold tailWord_4084013
  simp only [CollatzResearch.WordTrace]
  refine ⟨148956191353325869735184693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99304127568883913156789795 148956191353325869735184693)
  ·
    refine ⟨13964642939374300287673565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 148956191353325869735184693 13964642939374300287673565)
    ·
      refine ⟨5236741102265362607877587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13964642939374300287673565 5236741102265362607877587)
      ·
        refine ⟨7855111653398043911816381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5236741102265362607877587 7855111653398043911816381)
        ·
          refine ⟨2945666870024266466931143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7855111653398043911816381 2945666870024266466931143)
          ·
            refine ⟨4418500305036399700396715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2945666870024266466931143 4418500305036399700396715)
            ·
              refine ⟨6627750457554599550595073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4418500305036399700396715 6627750457554599550595073)
              ·
                refine ⟨4970812843165949662946305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6627750457554599550595073 4970812843165949662946305)
                ·
                  refine ⟨3728109632374462247209729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4970812843165949662946305 3728109632374462247209729)
                  ·
                    refine ⟨2796082224280846685407297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3728109632374462247209729 2796082224280846685407297)
                    ·
                      refine ⟨2097061668210635014055473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2796082224280846685407297 2097061668210635014055473)
                      ·
                        rfl

theorem cell23_4084013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 1, 2, 2, 2, 2].length) (baseStart_4084013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4084013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4084013 prefixEnd_4084013 := by exact prefixLift 4084013
  have htrace : WordTrace (prefixWord ++ tailWord_4084013) baseStart_4084013 baseEnd_4084013 := by
    simpa [prefixWord, tailWord_4084013, baseEnd_4084013] using wordTrace_append hprefix tailTrace_4084013
  have hstable : (prefixWord ++ tailWord_4084013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4084013).length < 2 ^ (prefixWord ++ tailWord_4084013).sum := by decide
  have hdescent : baseEnd_4084013 < baseStart_4084013 := by decide
  rcases family_descends (prefixWord ++ tailWord_4084013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4084031 : List Nat := [1, 1, 2, 2, 4, 1, 1, 2, 2, 1, 6]
def baseStart_4084031 : Nat := 118140960795 + 4084031 * 2 ^ 59
def prefixEnd_4084031 : Nat := 4983230072969 + 3 ^ 40 * 4084031 * 2
def baseEnd_4084031 : Nat := 2097070910862415943630389

theorem tailTrace_4084031 : CollatzResearch.WordTrace tailWord_4084031 prefixEnd_4084031 2097070910862415943630389 := by
  unfold tailWord_4084031
  simp only [CollatzResearch.WordTrace]
  refine ⟨148956847867260658809339947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99304565244840439206226631 148956847867260658809339947)
  ·
    refine ⟨223435271800890988214009921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148956847867260658809339947 223435271800890988214009921)
    ·
      refine ⟨167576453850668241160507441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223435271800890988214009921 167576453850668241160507441)
      ·
        refine ⟨125682340388001180870380581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167576453850668241160507441 125682340388001180870380581)
        ·
          refine ⟨23565438822750221413196359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125682340388001180870380581 23565438822750221413196359)
          ·
            refine ⟨35348158234125332119794539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23565438822750221413196359 35348158234125332119794539)
            ·
              refine ⟨53022237351187998179691809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35348158234125332119794539 53022237351187998179691809)
              ·
                refine ⟨39766678013390998634768857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53022237351187998179691809 39766678013390998634768857)
                ·
                  refine ⟨29825008510043248976076643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39766678013390998634768857 29825008510043248976076643)
                  ·
                    refine ⟨44737512765064873464114965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29825008510043248976076643 44737512765064873464114965)
                    ·
                      refine ⟨2097070910862415943630389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44737512765064873464114965 2097070910862415943630389)
                      ·
                        rfl

theorem cell23_4084031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 2, 2, 1, 6].length) (baseStart_4084031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4084031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4084031 prefixEnd_4084031 := by exact prefixLift 4084031
  have htrace : WordTrace (prefixWord ++ tailWord_4084031) baseStart_4084031 baseEnd_4084031 := by
    simpa [prefixWord, tailWord_4084031, baseEnd_4084031] using wordTrace_append hprefix tailTrace_4084031
  have hstable : (prefixWord ++ tailWord_4084031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4084031).length < 2 ^ (prefixWord ++ tailWord_4084031).sum := by decide
  have hdescent : baseEnd_4084031 < baseStart_4084031 := by decide
  rcases family_descends (prefixWord ++ tailWord_4084031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4084081 : List Nat := [1, 2, 2, 2, 1, 2, 1, 2, 2, 1, 7]
def baseStart_4084081 : Nat := 118140960795 + 4084081 * 2 ^ 59
def prefixEnd_4084081 : Nat := 4983230072969 + 3 ^ 40 * 4084081 * 2
def baseEnd_4084081 : Nat := 2097096584895140748005159

theorem tailTrace_4084081 : CollatzResearch.WordTrace tailWord_4084081 prefixEnd_4084081 2097096584895140748005159 := by
  unfold tailWord_4084081
  simp only [CollatzResearch.WordTrace]
  refine ⟨148958671517079517348660097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99305781011386344899106731 148958671517079517348660097)
  ·
    refine ⟨111719003637809638011495073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148958671517079517348660097 111719003637809638011495073)
    ·
      refine ⟨83789252728357228508621305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111719003637809638011495073 83789252728357228508621305)
      ·
        refine ⟨62841939546267921381465979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83789252728357228508621305 62841939546267921381465979)
        ·
          refine ⟨94262909319401882072198969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62841939546267921381465979 94262909319401882072198969)
          ·
            refine ⟨70697181989551411554149227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94262909319401882072198969 70697181989551411554149227)
            ·
              refine ⟨106045772984327117331223841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70697181989551411554149227 106045772984327117331223841)
              ·
                refine ⟨79534329738245337998417881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106045772984327117331223841 79534329738245337998417881)
                ·
                  refine ⟨59650747303684003498813411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79534329738245337998417881 59650747303684003498813411)
                  ·
                    refine ⟨89476120955526005248220117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59650747303684003498813411 89476120955526005248220117)
                    ·
                      refine ⟨2097096584895140748005159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 89476120955526005248220117 2097096584895140748005159)
                      ·
                        rfl

theorem cell23_4084081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 2, 2, 1, 7].length) (baseStart_4084081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4084081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4084081 prefixEnd_4084081 := by exact prefixLift 4084081
  have htrace : WordTrace (prefixWord ++ tailWord_4084081) baseStart_4084081 baseEnd_4084081 := by
    simpa [prefixWord, tailWord_4084081, baseEnd_4084081] using wordTrace_append hprefix tailTrace_4084081
  have hstable : (prefixWord ++ tailWord_4084081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4084081).length < 2 ^ (prefixWord ++ tailWord_4084081).sum := by decide
  have hdescent : baseEnd_4084081 < baseStart_4084081 := by decide
  rcases family_descends (prefixWord ++ tailWord_4084081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4084105 : List Nat := [1, 2, 1, 1, 6, 1, 3, 2, 1, 5]
def baseStart_4084105 : Nat := 118140960795 + 4084105 * 2 ^ 59
def prefixEnd_4084105 : Nat := 4983230072969 + 3 ^ 40 * 4084105 * 2
def baseEnd_4084105 : Nat := 699036302810282884701683

theorem tailTrace_4084105 : CollatzResearch.WordTrace tailWord_4084105 prefixEnd_4084105 699036302810282884701683 := by
  unfold tailWord_4084105
  simp only [CollatzResearch.WordTrace]
  refine ⟨148959546868992569447533769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99306364579328379631689179 148959546868992569447533769)
  ·
    refine ⟨111719660151744427085650327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148959546868992569447533769 111719660151744427085650327)
    ·
      refine ⟨167579490227616640628475491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111719660151744427085650327 167579490227616640628475491)
      ·
        refine ⟨251369235341424960942713237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167579490227616640628475491 251369235341424960942713237)
        ·
          refine ⟨11782932906629295044189683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 251369235341424960942713237 11782932906629295044189683)
          ·
            refine ⟨17674399359943942566284525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11782932906629295044189683 17674399359943942566284525)
            ·
              refine ⟨6627899759978978462356697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17674399359943942566284525 6627899759978978462356697)
              ·
                refine ⟨4970924819984233846767523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6627899759978978462356697 4970924819984233846767523)
                ·
                  refine ⟨7456387229976350770151285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4970924819984233846767523 7456387229976350770151285)
                  ·
                    refine ⟨699036302810282884701683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7456387229976350770151285 699036302810282884701683)
                    ·
                      rfl

theorem cell23_4084105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 3, 2, 1, 5].length) (baseStart_4084105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4084105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4084105 prefixEnd_4084105 := by exact prefixLift 4084105
  have htrace : WordTrace (prefixWord ++ tailWord_4084105) baseStart_4084105 baseEnd_4084105 := by
    simpa [prefixWord, tailWord_4084105, baseEnd_4084105] using wordTrace_append hprefix tailTrace_4084105
  have hstable : (prefixWord ++ tailWord_4084105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4084105).length < 2 ^ (prefixWord ++ tailWord_4084105).sum := by decide
  have hdescent : baseEnd_4084105 < baseStart_4084105 := by decide
  rcases family_descends (prefixWord ++ tailWord_4084105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4084122 : List Nat := [3, 1, 1, 4, 1, 3, 3, 1, 1, 5]
def baseStart_4084122 : Nat := 118140960795 + 4084122 * 2 ^ 59
def prefixEnd_4084122 : Nat := 4983230072969 + 3 ^ 40 * 4084122 * 2
def baseEnd_4084122 : Nat := 699039212533991695864157

theorem tailTrace_4084122 : CollatzResearch.WordTrace tailWord_4084122 prefixEnd_4084122 699039212533991695864157 := by
  unfold tailWord_4084122
  simp only [CollatzResearch.WordTrace]
  refine ⟨37240041727482745337725655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99306777939953987567268413 37240041727482745337725655)
  ·
    refine ⟨55860062591224118006588483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37240041727482745337725655 55860062591224118006588483)
    ·
      refine ⟨83790093886836177009882725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55860062591224118006588483 83790093886836177009882725)
      ·
        refine ⟨15710642603781783189353011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83790093886836177009882725 15710642603781783189353011)
        ·
          refine ⟨23565963905672674784029517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15710642603781783189353011 23565963905672674784029517)
          ·
            refine ⟨8837236464627253044011069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23565963905672674784029517 8837236464627253044011069)
            ·
              refine ⟨3313963674235219891504151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8837236464627253044011069 3313963674235219891504151)
              ·
                refine ⟨4970945511352829837256227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3313963674235219891504151 4970945511352829837256227)
                ·
                  refine ⟨7456418267029244755884341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4970945511352829837256227 7456418267029244755884341)
                  ·
                    refine ⟨699039212533991695864157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7456418267029244755884341 699039212533991695864157)
                    ·
                      rfl

theorem cell23_4084122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 3, 1, 1, 5].length) (baseStart_4084122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4084122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4084122 prefixEnd_4084122 := by exact prefixLift 4084122
  have htrace : WordTrace (prefixWord ++ tailWord_4084122) baseStart_4084122 baseEnd_4084122 := by
    simpa [prefixWord, tailWord_4084122, baseEnd_4084122] using wordTrace_append hprefix tailTrace_4084122
  have hstable : (prefixWord ++ tailWord_4084122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4084122).length < 2 ^ (prefixWord ++ tailWord_4084122).sum := by decide
  have hdescent : baseEnd_4084122 < baseStart_4084122 := by decide
  rcases family_descends (prefixWord ++ tailWord_4084122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4084131 : List Nat := [1, 1, 1, 4, 1, 15]
def baseStart_4084131 : Nat := 118140960795 + 4084131 * 2 ^ 59
def prefixEnd_4084131 : Nat := 4983230072969 + 3 ^ 40 * 4084131 * 2
def baseEnd_4084131 : Nat := 8630132752789570174403

theorem tailTrace_4084131 : CollatzResearch.WordTrace tailWord_4084131 prefixEnd_4084131 8630132752789570174403 := by
  unfold tailWord_4084131
  simp only [CollatzResearch.WordTrace]
  refine ⟨148960495166898375887980247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99306996777932250591986831 148960495166898375887980247)
  ·
    refine ⟨223440742750347563831970371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148960495166898375887980247 223440742750347563831970371)
    ·
      refine ⟨335161114125521345747955557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223440742750347563831970371 335161114125521345747955557)
      ·
        refine ⟨62842708898535252327741667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 335161114125521345747955557 62842708898535252327741667)
        ·
          refine ⟨94264063347802878491612501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62842708898535252327741667 94264063347802878491612501)
          ·
            refine ⟨8630132752789570174403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 15 94264063347802878491612501 8630132752789570174403)
            ·
              rfl

theorem cell23_4084131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 15].length) (baseStart_4084131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4084131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4084131 prefixEnd_4084131 := by exact prefixLift 4084131
  have htrace : WordTrace (prefixWord ++ tailWord_4084131) baseStart_4084131 baseEnd_4084131 := by
    simpa [prefixWord, tailWord_4084131, baseEnd_4084131] using wordTrace_append hprefix tailTrace_4084131
  have hstable : (prefixWord ++ tailWord_4084131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4084131).length < 2 ^ (prefixWord ++ tailWord_4084131).sum := by decide
  have hdescent : baseEnd_4084131 < baseStart_4084131 := by decide
  rcases family_descends (prefixWord ++ tailWord_4084131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4084136 : List Nat := [2, 1, 6, 1, 1, 2, 1, 4, 1, 1, 3]
def baseStart_4084136 : Nat := 118140960795 + 4084136 * 2 ^ 59
def prefixEnd_4084136 : Nat := 4983230072969 + 3 ^ 40 * 4084136 * 2
def baseEnd_4084136 : Nat := 2097124826331138032817407

theorem tailTrace_4084136 : CollatzResearch.WordTrace tailWord_4084136 prefixEnd_4084136 2097124826331138032817407 := by
  unfold tailWord_4084136
  simp only [CollatzResearch.WordTrace]
  refine ⟨74480338765940130870956131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99307118354586841161274841 74480338765940130870956131)
  ·
    refine ⟨111720508148910196306434197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74480338765940130870956131 111720508148910196306434197)
    ·
      refine ⟨5236898819480165451864103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 111720508148910196306434197 5236898819480165451864103)
      ·
        refine ⟨7855348229220248177796155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5236898819480165451864103 7855348229220248177796155)
        ·
          refine ⟨11783022343830372266694233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7855348229220248177796155 11783022343830372266694233)
          ·
            refine ⟨8837266757872779200020675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11783022343830372266694233 8837266757872779200020675)
            ·
              refine ⟨13255900136809168800031013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8837266757872779200020675 13255900136809168800031013)
              ·
                refine ⟨2485481275651719150005815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13255900136809168800031013 2485481275651719150005815)
                ·
                  refine ⟨3728221913477578725008723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2485481275651719150005815 3728221913477578725008723)
                  ·
                    refine ⟨5592332870216368087513085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3728221913477578725008723 5592332870216368087513085)
                    ·
                      refine ⟨2097124826331138032817407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5592332870216368087513085 2097124826331138032817407)
                      ·
                        rfl

theorem cell23_4084136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 4, 1, 1, 3].length) (baseStart_4084136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4084136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4084136 prefixEnd_4084136 := by exact prefixLift 4084136
  have htrace : WordTrace (prefixWord ++ tailWord_4084136) baseStart_4084136 baseEnd_4084136 := by
    simpa [prefixWord, tailWord_4084136, baseEnd_4084136] using wordTrace_append hprefix tailTrace_4084136
  have hstable : (prefixWord ++ tailWord_4084136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4084136).length < 2 ^ (prefixWord ++ tailWord_4084136).sum := by decide
  have hdescent : baseEnd_4084136 < baseStart_4084136 := by decide
  rcases family_descends (prefixWord ++ tailWord_4084136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4084145 : List Nat := [1, 2, 2, 4, 1, 2, 1, 2, 3, 2, 3]
def baseStart_4084145 : Nat := 118140960795 + 4084145 * 2 ^ 59
def prefixEnd_4084145 : Nat := 4983230072969 + 3 ^ 40 * 4084145 * 2
def baseEnd_4084145 : Nat := 2097129447657028497604865

theorem tailTrace_4084145 : CollatzResearch.WordTrace tailWord_4084145 prefixEnd_4084145 2097129447657028497604865 := by
  unfold tailWord_4084145
  simp only [CollatzResearch.WordTrace]
  refine ⟨148961005788847656278989889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99307337192565104185993259 148961005788847656278989889)
  ·
    refine ⟨111720754341635742209242417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148961005788847656278989889 111720754341635742209242417)
    ·
      refine ⟨83790565756226806656931813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111720754341635742209242417 83790565756226806656931813)
      ·
        refine ⟨15710731079292526248174715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83790565756226806656931813 15710731079292526248174715)
        ·
          refine ⟨23566096618938789372262073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15710731079292526248174715 23566096618938789372262073)
          ·
            refine ⟨17674572464204092029196555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23566096618938789372262073 17674572464204092029196555)
            ·
              refine ⟨26511858696306138043794833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17674572464204092029196555 26511858696306138043794833)
              ·
                refine ⟨19883894022229603532846125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26511858696306138043794833 19883894022229603532846125)
                ·
                  refine ⟨7456460258336101324817297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19883894022229603532846125 7456460258336101324817297)
                  ·
                    refine ⟨5592345193752075993612973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7456460258336101324817297 5592345193752075993612973)
                    ·
                      refine ⟨2097129447657028497604865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5592345193752075993612973 2097129447657028497604865)
                      ·
                        rfl

theorem cell23_4084145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 2, 3, 2, 3].length) (baseStart_4084145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4084145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4084145 prefixEnd_4084145 := by exact prefixLift 4084145
  have htrace : WordTrace (prefixWord ++ tailWord_4084145) baseStart_4084145 baseEnd_4084145 := by
    simpa [prefixWord, tailWord_4084145, baseEnd_4084145] using wordTrace_append hprefix tailTrace_4084145
  have hstable : (prefixWord ++ tailWord_4084145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4084145).length < 2 ^ (prefixWord ++ tailWord_4084145).sum := by decide
  have hdescent : baseEnd_4084145 < baseStart_4084145 := by decide
  rcases family_descends (prefixWord ++ tailWord_4084145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4084175 : List Nat := [1, 1, 2, 1, 1, 4, 1, 4, 4, 1, 3]
def baseStart_4084175 : Nat := 118140960795 + 4084175 * 2 ^ 59
def prefixEnd_4084175 : Nat := 4983230072969 + 3 ^ 40 * 4084175 * 2
def baseEnd_4084175 : Nat := 2097144852076663380229727

theorem tailTrace_4084175 : CollatzResearch.WordTrace tailWord_4084175 prefixEnd_4084175 2097144852076663380229727 := by
  unfold tailWord_4084175
  simp only [CollatzResearch.WordTrace]
  refine ⟨148962099978738971402581979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99308066652492647601721319 148962099978738971402581979)
  ·
    refine ⟨223443149968108457103872969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148962099978738971402581979 223443149968108457103872969)
    ·
      refine ⟨167582362476081342827904727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223443149968108457103872969 167582362476081342827904727)
      ·
        refine ⟨251373543714122014241857091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167582362476081342827904727 251373543714122014241857091)
        ·
          refine ⟨377060315571183021362785637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251373543714122014241857091 377060315571183021362785637)
          ·
            refine ⟨70698809169596816505522307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 377060315571183021362785637 70698809169596816505522307)
            ·
              refine ⟨106048213754395224758283461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70698809169596816505522307 106048213754395224758283461)
              ·
                refine ⟨19884040078949104642178149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106048213754395224758283461 19884040078949104642178149)
                ·
                  refine ⟨3728257514802957120408403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19884040078949104642178149 3728257514802957120408403)
                  ·
                    refine ⟨5592386272204435680612605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3728257514802957120408403 5592386272204435680612605)
                    ·
                      refine ⟨2097144852076663380229727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5592386272204435680612605 2097144852076663380229727)
                      ·
                        rfl

theorem cell23_4084175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 4, 4, 1, 3].length) (baseStart_4084175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4084175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4084175 prefixEnd_4084175 := by exact prefixLift 4084175
  have htrace : WordTrace (prefixWord ++ tailWord_4084175) baseStart_4084175 baseEnd_4084175 := by
    simpa [prefixWord, tailWord_4084175, baseEnd_4084175] using wordTrace_append hprefix tailTrace_4084175
  have hstable : (prefixWord ++ tailWord_4084175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4084175).length < 2 ^ (prefixWord ++ tailWord_4084175).sum := by decide
  have hdescent : baseEnd_4084175 < baseStart_4084175 := by decide
  rcases family_descends (prefixWord ++ tailWord_4084175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4084208 : List Nat := [2, 1, 1, 1, 3, 3, 1, 3, 2, 6]
def baseStart_4084208 : Nat := 118140960795 + 4084208 * 2 ^ 59
def prefixEnd_4084208 : Nat := 4983230072969 + 3 ^ 40 * 4084208 * 2
def baseEnd_4084208 : Nat := 699053932312753917039025

theorem tailTrace_4084208 : CollatzResearch.WordTrace tailWord_4084208 prefixEnd_4084208 699053932312753917039025 := by
  unfold tailWord_4084208
  simp only [CollatzResearch.WordTrace]
  refine ⟨74481651793809709019266639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99308869058412945359022185 74481651793809709019266639)
  ·
    refine ⟨111722477690714563528899959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74481651793809709019266639 111722477690714563528899959)
    ·
      refine ⟨167583716536071845293349939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111722477690714563528899959 167583716536071845293349939)
      ·
        refine ⟨251375574804107767940024909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167583716536071845293349939 251375574804107767940024909)
        ·
          refine ⟨94265840551540412977509341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 251375574804107767940024909 94265840551540412977509341)
          ·
            refine ⟨35349690206827654866566003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94265840551540412977509341 35349690206827654866566003)
            ·
              refine ⟨53024535310241482299849005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35349690206827654866566003 53024535310241482299849005)
              ·
                refine ⟨19884200741340555862443377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53024535310241482299849005 19884200741340555862443377)
                ·
                  refine ⟨14913150556005416896832533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19884200741340555862443377 14913150556005416896832533)
                  ·
                    refine ⟨699053932312753917039025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14913150556005416896832533 699053932312753917039025)
                    ·
                      rfl

theorem cell23_4084208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 3, 2, 6].length) (baseStart_4084208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4084208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4084208 prefixEnd_4084208 := by exact prefixLift 4084208
  have htrace : WordTrace (prefixWord ++ tailWord_4084208) baseStart_4084208 baseEnd_4084208 := by
    simpa [prefixWord, tailWord_4084208, baseEnd_4084208] using wordTrace_append hprefix tailTrace_4084208
  have hstable : (prefixWord ++ tailWord_4084208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4084208).length < 2 ^ (prefixWord ++ tailWord_4084208).sum := by decide
  have hdescent : baseEnd_4084208 < baseStart_4084208 := by decide
  rcases family_descends (prefixWord ++ tailWord_4084208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4084209 : List Nat := [1, 2, 2, 2, 3, 1, 5, 1, 2, 1, 3]
def baseStart_4084209 : Nat := 118140960795 + 4084209 * 2 ^ 59
def prefixEnd_4084209 : Nat := 4983230072969 + 3 ^ 40 * 4084209 * 2
def baseEnd_4084209 : Nat := 2097162310418916247204571

theorem tailTrace_4084209 : CollatzResearch.WordTrace tailWord_4084209 prefixEnd_4084209 2097162310418916247204571 := by
  unfold tailWord_4084209
  simp only [CollatzResearch.WordTrace]
  refine ⟨148963340060615795209319681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99308893373743863472879787 148963340060615795209319681)
  ·
    refine ⟨111722505045461846406989761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148963340060615795209319681 111722505045461846406989761)
    ·
      refine ⟨83791878784096384805242321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111722505045461846406989761 83791878784096384805242321)
      ·
        refine ⟨62843909088072288603931741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83791878784096384805242321 62843909088072288603931741)
        ·
          refine ⟨23566465908027108226474403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62843909088072288603931741 23566465908027108226474403)
          ·
            refine ⟨35349698862040662339711605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23566465908027108226474403 35349698862040662339711605)
            ·
              refine ⟨3314034268316312094347963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35349698862040662339711605 3314034268316312094347963)
              ·
                refine ⟨4971051402474468141521945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3314034268316312094347963 4971051402474468141521945)
                ·
                  refine ⟨3728288551855851106141459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4971051402474468141521945 3728288551855851106141459)
                  ·
                    refine ⟨5592432827783776659212189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3728288551855851106141459 5592432827783776659212189)
                    ·
                      refine ⟨2097162310418916247204571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5592432827783776659212189 2097162310418916247204571)
                      ·
                        rfl

theorem cell23_4084209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 5, 1, 2, 1, 3].length) (baseStart_4084209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4084209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4084209 prefixEnd_4084209 := by exact prefixLift 4084209
  have htrace : WordTrace (prefixWord ++ tailWord_4084209) baseStart_4084209 baseEnd_4084209 := by
    simpa [prefixWord, tailWord_4084209, baseEnd_4084209] using wordTrace_append hprefix tailTrace_4084209
  have hstable : (prefixWord ++ tailWord_4084209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4084209).length < 2 ^ (prefixWord ++ tailWord_4084209).sum := by decide
  have hdescent : baseEnd_4084209 < baseStart_4084209 := by decide
  rcases family_descends (prefixWord ++ tailWord_4084209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4084235 : List Nat := [1, 1, 1, 1, 7, 2, 1, 1, 2, 1, 5]
def baseStart_4084235 : Nat := 118140960795 + 4084235 * 2 ^ 59
def prefixEnd_4084235 : Nat := 4983230072969 + 3 ^ 40 * 4084235 * 2
def baseEnd_4084235 : Nat := 2097175660915933145479451

theorem tailTrace_4084235 : CollatzResearch.WordTrace tailWord_4084235 prefixEnd_4084235 2097175660915933145479451 := by
  unfold tailWord_4084235
  simp only [CollatzResearch.WordTrace]
  refine ⟨148964288358521601649766159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99309525572347734433177439 148964288358521601649766159)
  ·
    refine ⟨223446432537782402474649239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148964288358521601649766159 223446432537782402474649239)
    ·
      refine ⟨335169648806673603711973859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223446432537782402474649239 335169648806673603711973859)
      ·
        refine ⟨502754473210010405567960789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335169648806673603711973859 502754473210010405567960789)
        ·
          refine ⟨11783307965859618880499081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 502754473210010405567960789 11783307965859618880499081)
          ·
            refine ⟨8837480974394714160374311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11783307965859618880499081 8837480974394714160374311)
            ·
              refine ⟨13256221461592071240561467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8837480974394714160374311 13256221461592071240561467)
              ·
                refine ⟨19884332192388106860842201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13256221461592071240561467 19884332192388106860842201)
                ·
                  refine ⟨14913249144291080145631651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19884332192388106860842201 14913249144291080145631651)
                  ·
                    refine ⟨22369873716436620218447477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14913249144291080145631651 22369873716436620218447477)
                    ·
                      refine ⟨2097175660915933145479451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22369873716436620218447477 2097175660915933145479451)
                      ·
                        rfl

theorem cell23_4084235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 1, 2, 1, 5].length) (baseStart_4084235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4084235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4084235 prefixEnd_4084235 := by exact prefixLift 4084235
  have htrace : WordTrace (prefixWord ++ tailWord_4084235) baseStart_4084235 baseEnd_4084235 := by
    simpa [prefixWord, tailWord_4084235, baseEnd_4084235] using wordTrace_append hprefix tailTrace_4084235
  have hstable : (prefixWord ++ tailWord_4084235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4084235).length < 2 ^ (prefixWord ++ tailWord_4084235).sum := by decide
  have hdescent : baseEnd_4084235 < baseStart_4084235 := by decide
  rcases family_descends (prefixWord ++ tailWord_4084235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4084260 : List Nat := [2, 3, 1, 5, 2, 1, 2, 1, 2, 1, 3]
def baseStart_4084260 : Nat := 118140960795 + 4084260 * 2 ^ 59
def prefixEnd_4084260 : Nat := 4983230072969 + 3 ^ 40 * 4084260 * 2
def baseEnd_4084260 : Nat := 2097188497932295547666837

theorem tailTrace_4084260 : CollatzResearch.WordTrace tailWord_4084260 prefixEnd_4084260 2097188497932295547666837 := by
  unfold tailWord_4084260
  simp only [CollatzResearch.WordTrace]
  refine ⟨74482600091715515459713117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99310133455620687279617489 74482600091715515459713117)
  ·
    refine ⟨27930975034393318297392419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74482600091715515459713117 27930975034393318297392419)
    ·
      refine ⟨41896462551589977446088629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27930975034393318297392419 41896462551589977446088629)
      ·
        refine ⟨3927793364211560385570809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41896462551589977446088629 3927793364211560385570809)
        ·
          refine ⟨2945845023158670289178107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3927793364211560385570809 2945845023158670289178107)
          ·
            refine ⟨4418767534738005433767161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2945845023158670289178107 4418767534738005433767161)
            ·
              refine ⟨3314075651053504075325371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4418767534738005433767161 3314075651053504075325371)
              ·
                refine ⟨4971113476580256112988057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3314075651053504075325371 4971113476580256112988057)
                ·
                  refine ⟨3728335107435192084741043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4971113476580256112988057 3728335107435192084741043)
                  ·
                    refine ⟨5592502661152788127111565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3728335107435192084741043 5592502661152788127111565)
                    ·
                      refine ⟨2097188497932295547666837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5592502661152788127111565 2097188497932295547666837)
                      ·
                        rfl

theorem cell23_4084260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_4084260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4084260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4084260 prefixEnd_4084260 := by exact prefixLift 4084260
  have htrace : WordTrace (prefixWord ++ tailWord_4084260) baseStart_4084260 baseEnd_4084260 := by
    simpa [prefixWord, tailWord_4084260, baseEnd_4084260] using wordTrace_append hprefix tailTrace_4084260
  have hstable : (prefixWord ++ tailWord_4084260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4084260).length < 2 ^ (prefixWord ++ tailWord_4084260).sum := by decide
  have hdescent : baseEnd_4084260 < baseStart_4084260 := by decide
  rcases family_descends (prefixWord ++ tailWord_4084260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4084266 : List Nat := [3, 1, 4, 1, 1, 3, 1, 3, 2, 2, 2]
def baseStart_4084266 : Nat := 118140960795 + 4084266 * 2 ^ 59
def prefixEnd_4084266 : Nat := 4983230072969 + 3 ^ 40 * 4084266 * 2
def baseEnd_4084266 : Nat := 2097191578816222524191809

theorem tailTrace_4084266 : CollatzResearch.WordTrace tailWord_4084266 prefixEnd_4084266 2097191578816222524191809 := by
  unfold tailWord_4084266
  simp only [CollatzResearch.WordTrace]
  refine ⟨37241354755352323486036163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99310279347606195962763101 37241354755352323486036163)
  ·
    refine ⟨55862032133028485229054245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37241354755352323486036163 55862032133028485229054245)
    ·
      refine ⟨10474131024942840980447671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55862032133028485229054245 10474131024942840980447671)
      ·
        refine ⟨15711196537414261470671507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10474131024942840980447671 15711196537414261470671507)
        ·
          refine ⟨23566794806121392206007261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15711196537414261470671507 23566794806121392206007261)
          ·
            refine ⟨8837548052295522077252723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23566794806121392206007261 8837548052295522077252723)
            ·
              refine ⟨13256322078443283115879085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8837548052295522077252723 13256322078443283115879085)
              ·
                refine ⟨4971120779416231168454657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13256322078443283115879085 4971120779416231168454657)
                ·
                  refine ⟨3728340584562173376340993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4971120779416231168454657 3728340584562173376340993)
                  ·
                    refine ⟨2796255438421630032255745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3728340584562173376340993 2796255438421630032255745)
                    ·
                      refine ⟨2097191578816222524191809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2796255438421630032255745 2097191578816222524191809)
                      ·
                        rfl

theorem cell23_4084266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 3, 2, 2, 2].length) (baseStart_4084266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4084266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4084266 prefixEnd_4084266 := by exact prefixLift 4084266
  have htrace : WordTrace (prefixWord ++ tailWord_4084266) baseStart_4084266 baseEnd_4084266 := by
    simpa [prefixWord, tailWord_4084266, baseEnd_4084266] using wordTrace_append hprefix tailTrace_4084266
  have hstable : (prefixWord ++ tailWord_4084266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4084266).length < 2 ^ (prefixWord ++ tailWord_4084266).sum := by decide
  have hdescent : baseEnd_4084266 < baseStart_4084266 := by decide
  rcases family_descends (prefixWord ++ tailWord_4084266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4084268 : List Nat := [2, 2, 1, 1, 1, 2, 1, 3, 3, 7]
def baseStart_4084268 : Nat := 118140960795 + 4084268 * 2 ^ 59
def prefixEnd_4084268 : Nat := 4983230072969 + 3 ^ 40 * 4084268 * 2
def baseEnd_4084268 : Nat := 699064201925843838788933

theorem tailTrace_4084268 : CollatzResearch.WordTrace tailWord_4084268 prefixEnd_4084268 699064201925843838788933 := by
  unfold tailWord_4084268
  simp only [CollatzResearch.WordTrace]
  refine ⟨74482745983701024142858729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99310327978268032190478305 74482745983701024142858729)
  ·
    refine ⟨55862059487775768107144047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74482745983701024142858729 55862059487775768107144047)
    ·
      refine ⟨83793089231663652160716071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55862059487775768107144047 83793089231663652160716071)
      ·
        refine ⟨125689633847495478241074107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83793089231663652160716071 125689633847495478241074107)
        ·
          refine ⟨188534450771243217361611161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125689633847495478241074107 188534450771243217361611161)
          ·
            refine ⟨141400838078432413021208371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188534450771243217361611161 141400838078432413021208371)
            ·
              refine ⟨212101257117648619531812557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141400838078432413021208371 212101257117648619531812557)
              ·
                refine ⟨79537971419118232324429709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 212101257117648619531812557 79537971419118232324429709)
                ·
                  refine ⟨29826739282169337121661141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79537971419118232324429709 29826739282169337121661141)
                  ·
                    refine ⟨699064201925843838788933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29826739282169337121661141 699064201925843838788933)
                    ·
                      rfl

theorem cell23_4084268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 7].length) (baseStart_4084268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4084268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4084268 prefixEnd_4084268 := by exact prefixLift 4084268
  have htrace : WordTrace (prefixWord ++ tailWord_4084268) baseStart_4084268 baseEnd_4084268 := by
    simpa [prefixWord, tailWord_4084268, baseEnd_4084268] using wordTrace_append hprefix tailTrace_4084268
  have hstable : (prefixWord ++ tailWord_4084268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4084268).length < 2 ^ (prefixWord ++ tailWord_4084268).sum := by decide
  have hdescent : baseEnd_4084268 < baseStart_4084268 := by decide
  rcases family_descends (prefixWord ++ tailWord_4084268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4084295 : List Nat := [1, 1, 4, 1, 4, 1, 1, 2, 1, 2, 5]
def baseStart_4084295 : Nat := 118140960795 + 4084295 * 2 ^ 59
def prefixEnd_4084295 : Nat := 4983230072969 + 3 ^ 40 * 4084295 * 2
def baseEnd_4084295 : Nat := 2097206469755202910729175

theorem tailTrace_4084295 : CollatzResearch.WordTrace tailWord_4084295 prefixEnd_4084295 2097206469755202910729175 := by
  unfold tailWord_4084295
  simp only [CollatzResearch.WordTrace]
  refine ⟨148966476738304231896950339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99310984492202821264633559 148966476738304231896950339)
  ·
    refine ⟨223449715107456347845425509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148966476738304231896950339 223449715107456347845425509)
    ·
      refine ⟨41896821582648065221017283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 223449715107456347845425509 41896821582648065221017283)
      ·
        refine ⟨62845232373972097831525925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41896821582648065221017283 62845232373972097831525925)
        ·
          refine ⟨11783481070119768343411111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62845232373972097831525925 11783481070119768343411111)
          ·
            refine ⟨17675221605179652515116667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11783481070119768343411111 17675221605179652515116667)
            ·
              refine ⟨26512832407769478772675001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17675221605179652515116667 26512832407769478772675001)
              ·
                refine ⟨19884624305827109079506251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26512832407769478772675001 19884624305827109079506251)
                ·
                  refine ⟨29826936458740663619259377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19884624305827109079506251 29826936458740663619259377)
                  ·
                    refine ⟨22370202344055497714444533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29826936458740663619259377 22370202344055497714444533)
                    ·
                      refine ⟨2097206469755202910729175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22370202344055497714444533 2097206469755202910729175)
                      ·
                        rfl

theorem cell23_4084295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 2, 1, 2, 5].length) (baseStart_4084295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4084295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4084295 prefixEnd_4084295 := by exact prefixLift 4084295
  have htrace : WordTrace (prefixWord ++ tailWord_4084295) baseStart_4084295 baseEnd_4084295 := by
    simpa [prefixWord, tailWord_4084295, baseEnd_4084295] using wordTrace_append hprefix tailTrace_4084295
  have hstable : (prefixWord ++ tailWord_4084295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4084295).length < 2 ^ (prefixWord ++ tailWord_4084295).sum := by decide
  have hdescent : baseEnd_4084295 < baseStart_4084295 := by decide
  rcases family_descends (prefixWord ++ tailWord_4084295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4084362 : List Nat := [3, 1, 2, 3, 3, 1, 1, 1, 8]
def baseStart_4084362 : Nat := 118140960795 + 4084362 * 2 ^ 59
def prefixEnd_4084362 : Nat := 4983230072969 + 3 ^ 40 * 4084362 * 2
def baseEnd_4084362 : Nat := 233026763662117127621263

theorem tailTrace_4084362 : CollatzResearch.WordTrace tailWord_4084362 prefixEnd_4084362 233026763662117127621263 := by
  unfold tailWord_4084362
  simp only [CollatzResearch.WordTrace]
  refine ⟨37242230107265375584909835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99312613619374334893092893 37242230107265375584909835)
  ·
    refine ⟨55863345160898063377364753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37242230107265375584909835 55863345160898063377364753)
    ·
      refine ⟨41897508870673547533023565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55863345160898063377364753 41897508870673547533023565)
      ·
        refine ⟨15711565826502580324883837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41897508870673547533023565 15711565826502580324883837)
        ·
          refine ⟨5891837184938467621831439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15711565826502580324883837 5891837184938467621831439)
          ·
            refine ⟨8837755777407701432747159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5891837184938467621831439 8837755777407701432747159)
            ·
              refine ⟨13256633666111552149120739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8837755777407701432747159 13256633666111552149120739)
              ·
                refine ⟨19884950499167328223681109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13256633666111552149120739 19884950499167328223681109)
                ·
                  refine ⟨233026763662117127621263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19884950499167328223681109 233026763662117127621263)
                  ·
                    rfl

theorem cell23_4084362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 1, 8].length) (baseStart_4084362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4084362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4084362 prefixEnd_4084362 := by exact prefixLift 4084362
  have htrace : WordTrace (prefixWord ++ tailWord_4084362) baseStart_4084362 baseEnd_4084362 := by
    simpa [prefixWord, tailWord_4084362, baseEnd_4084362] using wordTrace_append hprefix tailTrace_4084362
  have hstable : (prefixWord ++ tailWord_4084362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4084362).length < 2 ^ (prefixWord ++ tailWord_4084362).sum := by decide
  have hdescent : baseEnd_4084362 < baseStart_4084362 := by decide
  rcases family_descends (prefixWord ++ tailWord_4084362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4084382 : List Nat := [4, 3, 1, 1, 1, 1, 1, 2, 1, 2, 6]
def baseStart_4084382 : Nat := 118140960795 + 4084382 * 2 ^ 59
def prefixEnd_4084382 : Nat := 4983230072969 + 3 ^ 40 * 4084382 * 2
def baseEnd_4084382 : Nat := 2097251142572144070341275

theorem tailTrace_4084382 : CollatzResearch.WordTrace tailWord_4084382 prefixEnd_4084382 2097251142572144070341275 := by
  unfold tailWord_4084382
  simp only [CollatzResearch.WordTrace]
  refine ⟨18621206236123630719420925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99313099925992697170244933 18621206236123630719420925)
  ·
    refine ⟨6982952338546361519782847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18621206236123630719420925 6982952338546361519782847)
    ·
      refine ⟨10474428507819542279674271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6982952338546361519782847 10474428507819542279674271)
      ·
        refine ⟨15711642761729313419511407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10474428507819542279674271 15711642761729313419511407)
        ·
          refine ⟨23567464142593970129267111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15711642761729313419511407 23567464142593970129267111)
          ·
            refine ⟨35351196213890955193900667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23567464142593970129267111 35351196213890955193900667)
            ·
              refine ⟨53026794320836432790851001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35351196213890955193900667 53026794320836432790851001)
              ·
                refine ⟨39770095740627324593138251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53026794320836432790851001 39770095740627324593138251)
                ·
                  refine ⟨59655143610940986889707377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39770095740627324593138251 59655143610940986889707377)
                  ·
                    refine ⟨44741357708205740167280533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59655143610940986889707377 44741357708205740167280533)
                    ·
                      refine ⟨2097251142572144070341275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44741357708205740167280533 2097251142572144070341275)
                      ·
                        rfl

theorem cell23_4084382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_4084382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4084382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4084382 prefixEnd_4084382 := by exact prefixLift 4084382
  have htrace : WordTrace (prefixWord ++ tailWord_4084382) baseStart_4084382 baseEnd_4084382 := by
    simpa [prefixWord, tailWord_4084382, baseEnd_4084382] using wordTrace_append hprefix tailTrace_4084382
  have hstable : (prefixWord ++ tailWord_4084382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4084382).length < 2 ^ (prefixWord ++ tailWord_4084382).sum := by decide
  have hdescent : baseEnd_4084382 < baseStart_4084382 := by decide
  rcases family_descends (prefixWord ++ tailWord_4084382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4084439 : List Nat := [1, 1, 3, 2, 1, 5, 1, 3, 2, 4]
def baseStart_4084439 : Nat := 118140960795 + 4084439 * 2 ^ 59
def prefixEnd_4084439 : Nat := 4983230072969 + 3 ^ 40 * 4084439 * 2
def baseEnd_4084439 : Nat := 699093470323150115776171

theorem tailTrace_4084439 : CollatzResearch.WordTrace tailWord_4084439 prefixEnd_4084439 699093470323150115776171 := by
  unfold tailWord_4084439
  simp only [CollatzResearch.WordTrace]
  refine ⟨148971728849782544490192371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99314485899855029660128247 148971728849782544490192371)
  ·
    refine ⟨223457593274673816735288557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148971728849782544490192371 223457593274673816735288557)
    ·
      refine ⟨83796597478002681275733209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223457593274673816735288557 83796597478002681275733209)
      ·
        refine ⟨62847448108502010956799907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83796597478002681275733209 62847448108502010956799907)
        ·
          refine ⟨94271172162753016435199861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62847448108502010956799907 94271172162753016435199861)
          ·
            refine ⟨8837922390258095290799987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 94271172162753016435199861 8837922390258095290799987)
            ·
              refine ⟨13256883585387142936199981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8837922390258095290799987 13256883585387142936199981)
              ·
                refine ⟨4971331344520178601074993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13256883585387142936199981 4971331344520178601074993)
                ·
                  refine ⟨3728498508390133950806245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4971331344520178601074993 3728498508390133950806245)
                  ·
                    refine ⟨699093470323150115776171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3728498508390133950806245 699093470323150115776171)
                    ·
                      rfl

theorem cell23_4084439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 3, 2, 4].length) (baseStart_4084439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4084439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4084439 prefixEnd_4084439 := by exact prefixLift 4084439
  have htrace : WordTrace (prefixWord ++ tailWord_4084439) baseStart_4084439 baseEnd_4084439 := by
    simpa [prefixWord, tailWord_4084439, baseEnd_4084439] using wordTrace_append hprefix tailTrace_4084439
  have hstable : (prefixWord ++ tailWord_4084439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4084439).length < 2 ^ (prefixWord ++ tailWord_4084439).sum := by decide
  have hdescent : baseEnd_4084439 < baseStart_4084439 := by decide
  rcases family_descends (prefixWord ++ tailWord_4084439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4084442 : List Nat := [3, 1, 1, 2, 2, 2, 2, 3, 1, 2, 4]
def baseStart_4084442 : Nat := 118140960795 + 4084442 * 2 ^ 59
def prefixEnd_4084442 : Nat := 4983230072969 + 3 ^ 40 * 4084442 * 2
def baseEnd_4084442 : Nat := 2097281951411413835590999

theorem tailTrace_4084442 : CollatzResearch.WordTrace tailWord_4084442 prefixEnd_4084442 2097281951411413835590999 := by
  unfold tailWord_4084442
  simp only [CollatzResearch.WordTrace]
  refine ⟨37242959567192919000637895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99314558845847784001701053 37242959567192919000637895)
  ·
    refine ⟨55864439350789378500956843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37242959567192919000637895 55864439350789378500956843)
    ·
      refine ⟨83796659026184067751435265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55864439350789378500956843 83796659026184067751435265)
      ·
        refine ⟨62847494269638050813576449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83796659026184067751435265 62847494269638050813576449)
        ·
          refine ⟨47135620702228538110182337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62847494269638050813576449 47135620702228538110182337)
          ·
            refine ⟨35351715526671403582636753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47135620702228538110182337 35351715526671403582636753)
            ·
              refine ⟨26513786645003552686977565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35351715526671403582636753 26513786645003552686977565)
              ·
                refine ⟨9942669991876332257616587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26513786645003552686977565 9942669991876332257616587)
                ·
                  refine ⟨14914004987814498386424881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9942669991876332257616587 14914004987814498386424881)
                  ·
                    refine ⟨11185503740860873789818661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14914004987814498386424881 11185503740860873789818661)
                    ·
                      refine ⟨2097281951411413835590999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11185503740860873789818661 2097281951411413835590999)
                      ·
                        rfl

theorem cell23_4084442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 3, 1, 2, 4].length) (baseStart_4084442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4084442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4084442 prefixEnd_4084442 := by exact prefixLift 4084442
  have htrace : WordTrace (prefixWord ++ tailWord_4084442) baseStart_4084442 baseEnd_4084442 := by
    simpa [prefixWord, tailWord_4084442, baseEnd_4084442] using wordTrace_append hprefix tailTrace_4084442
  have hstable : (prefixWord ++ tailWord_4084442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4084442).length < 2 ^ (prefixWord ++ tailWord_4084442).sum := by decide
  have hdescent : baseEnd_4084442 < baseStart_4084442 := by decide
  rcases family_descends (prefixWord ++ tailWord_4084442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4084449 : List Nat := [1, 2, 3, 1, 4, 2, 1, 1, 3, 2, 3]
def baseStart_4084449 : Nat := 118140960795 + 4084449 * 2 ^ 59
def prefixEnd_4084449 : Nat := 4983230072969 + 3 ^ 40 * 4084449 * 2
def baseEnd_4084449 : Nat := 2097285545775995308203467

theorem tailTrace_4084449 : CollatzResearch.WordTrace tailWord_4084449 prefixEnd_4084449 2097285545775995308203467 := by
  unfold tailWord_4084449
  simp only [CollatzResearch.WordTrace]
  refine ⟨148972093579746316198056401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99314729053164210798704267 148972093579746316198056401)
  ·
    refine ⟨111729070184809737148542301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148972093579746316198056401 111729070184809737148542301)
    ·
      refine ⟨41898401319303651430703363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111729070184809737148542301 41898401319303651430703363)
      ·
        refine ⟨62847601978955477146055045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41898401319303651430703363 62847601978955477146055045)
        ·
          refine ⟨11783925371054151964885321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62847601978955477146055045 11783925371054151964885321)
          ·
            refine ⟨8837944028290613973663991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11783925371054151964885321 8837944028290613973663991)
            ·
              refine ⟨13256916042435920960495987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8837944028290613973663991 13256916042435920960495987)
              ·
                refine ⟨19885374063653881440743981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13256916042435920960495987 19885374063653881440743981)
                ·
                  refine ⟨7457015273870205540278993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19885374063653881440743981 7457015273870205540278993)
                  ·
                    refine ⟨5592761455402654155209245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7457015273870205540278993 5592761455402654155209245)
                    ·
                      refine ⟨2097285545775995308203467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5592761455402654155209245 2097285545775995308203467)
                      ·
                        rfl

theorem cell23_4084449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 1, 3, 2, 3].length) (baseStart_4084449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4084449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4084449 prefixEnd_4084449 := by exact prefixLift 4084449
  have htrace : WordTrace (prefixWord ++ tailWord_4084449) baseStart_4084449 baseEnd_4084449 := by
    simpa [prefixWord, tailWord_4084449, baseEnd_4084449] using wordTrace_append hprefix tailTrace_4084449
  have hstable : (prefixWord ++ tailWord_4084449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4084449).length < 2 ^ (prefixWord ++ tailWord_4084449).sum := by decide
  have hdescent : baseEnd_4084449 < baseStart_4084449 := by decide
  rcases family_descends (prefixWord ++ tailWord_4084449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4084469 : List Nat := [1, 3, 6, 1, 12]
def baseStart_4084469 : Nat := 118140960795 + 4084469 * 2 ^ 59
def prefixEnd_4084469 : Nat := 4983230072969 + 3 ^ 40 * 4084469 * 2
def baseEnd_4084469 : Nat := 2876948992303271920375

theorem tailTrace_4084469 : CollatzResearch.WordTrace tailWord_4084469 prefixEnd_4084469 2876948992303271920375 := by
  unfold tailWord_4084469
  simp only [CollatzResearch.WordTrace]
  refine ⟨148972823039673859613784461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99315215359782573075856307 148972823039673859613784461)
  ·
    refine ⟨55864808639877697355169173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148972823039673859613784461 55864808639877697355169173)
    ·
      refine ⟨2618662904994267063523555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 55864808639877697355169173 2618662904994267063523555)
      ·
        refine ⟨3927994357491400595285333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2618662904994267063523555 3927994357491400595285333)
        ·
          refine ⟨2876948992303271920375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 3927994357491400595285333 2876948992303271920375)
          ·
            rfl

theorem cell23_4084469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 12].length) (baseStart_4084469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4084469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4084469 prefixEnd_4084469 := by exact prefixLift 4084469
  have htrace : WordTrace (prefixWord ++ tailWord_4084469) baseStart_4084469 baseEnd_4084469 := by
    simpa [prefixWord, tailWord_4084469, baseEnd_4084469] using wordTrace_append hprefix tailTrace_4084469
  have hstable : (prefixWord ++ tailWord_4084469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4084469).length < 2 ^ (prefixWord ++ tailWord_4084469).sum := by decide
  have hdescent : baseEnd_4084469 < baseStart_4084469 := by decide
  rcases family_descends (prefixWord ++ tailWord_4084469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4084475 : List Nat := [1, 1, 1, 1, 1, 3, 1, 2, 3, 4, 5]
def baseStart_4084475 : Nat := 118140960795 + 4084475 * 2 ^ 59
def prefixEnd_4084475 : Nat := 4983230072969 + 3 ^ 40 * 4084475 * 2
def baseEnd_4084475 : Nat := 2097298896273012206478347

theorem tailTrace_4084475 : CollatzResearch.WordTrace tailWord_4084475 prefixEnd_4084475 2097298896273012206478347 := by
  unfold tailWord_4084475
  simp only [CollatzResearch.WordTrace]
  refine ⟨148973041877652122638502879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99315361251768081759001919 148973041877652122638502879)
  ·
    refine ⟨223459562816478183957754319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148973041877652122638502879 223459562816478183957754319)
    ·
      refine ⟨335189344224717275936631479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223459562816478183957754319 335189344224717275936631479)
      ·
        refine ⟨502784016337075913904947219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335189344224717275936631479 502784016337075913904947219)
        ·
          refine ⟨754176024505613870857420829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 502784016337075913904947219 754176024505613870857420829)
          ·
            refine ⟨282816009189605201571532811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 754176024505613870857420829 282816009189605201571532811)
            ·
              refine ⟨424224013784407802357299217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 282816009189605201571532811 424224013784407802357299217)
              ·
                refine ⟨318168010338305851767974413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 424224013784407802357299217 318168010338305851767974413)
                ·
                  refine ⟨119313003876864694412990405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 318168010338305851767974413 119313003876864694412990405)
                  ·
                    refine ⟨22371188226912130202435701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 119313003876864694412990405 22371188226912130202435701)
                    ·
                      refine ⟨2097298896273012206478347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22371188226912130202435701 2097298896273012206478347)
                      ·
                        rfl

theorem cell23_4084475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 3, 4, 5].length) (baseStart_4084475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4084475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4084475 prefixEnd_4084475 := by exact prefixLift 4084475
  have htrace : WordTrace (prefixWord ++ tailWord_4084475) baseStart_4084475 baseEnd_4084475 := by
    simpa [prefixWord, tailWord_4084475, baseEnd_4084475] using wordTrace_append hprefix tailTrace_4084475
  have hstable : (prefixWord ++ tailWord_4084475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4084475).length < 2 ^ (prefixWord ++ tailWord_4084475).sum := by decide
  have hdescent : baseEnd_4084475 < baseStart_4084475 := by decide
  rcases family_descends (prefixWord ++ tailWord_4084475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4084489 : List Nat := [1, 2, 1, 1, 3, 2, 3, 2, 3, 3, 2]
def baseStart_4084489 : Nat := 118140960795 + 4084489 * 2 ^ 59
def prefixEnd_4084489 : Nat := 4983230072969 + 3 ^ 40 * 4084489 * 2
def baseEnd_4084489 : Nat := 2097306085002175151703283

theorem tailTrace_4084489 : CollatzResearch.WordTrace tailWord_4084489 prefixEnd_4084489 2097306085002175151703283 := by
  unfold tailWord_4084489
  simp only [CollatzResearch.WordTrace]
  refine ⟨148973552499601403029512521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99315701666400935353008347 148973552499601403029512521)
  ·
    refine ⟨111730164374701052272134391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148973552499601403029512521 111730164374701052272134391)
    ·
      refine ⟨167595246562051578408201587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111730164374701052272134391 167595246562051578408201587)
      ·
        refine ⟨251392869843077367612302381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167595246562051578408201587 251392869843077367612302381)
        ·
          refine ⟨94272326191154012854613393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 251392869843077367612302381 94272326191154012854613393)
          ·
            refine ⟨70704244643365509640960045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94272326191154012854613393 70704244643365509640960045)
            ·
              refine ⟨26514091741262066115360017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70704244643365509640960045 26514091741262066115360017)
              ·
                refine ⟨19885568805946549586520013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26514091741262066115360017 19885568805946549586520013)
                ·
                  refine ⟨7457088302229956094945005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19885568805946549586520013 7457088302229956094945005)
                  ·
                    refine ⟨2796408113336233535604377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7457088302229956094945005 2796408113336233535604377)
                    ·
                      refine ⟨2097306085002175151703283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2796408113336233535604377 2097306085002175151703283)
                      ·
                        rfl

theorem cell23_4084489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 2, 3, 3, 2].length) (baseStart_4084489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4084489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4084489 prefixEnd_4084489 := by exact prefixLift 4084489
  have htrace : WordTrace (prefixWord ++ tailWord_4084489) baseStart_4084489 baseEnd_4084489 := by
    simpa [prefixWord, tailWord_4084489, baseEnd_4084489] using wordTrace_append hprefix tailTrace_4084489
  have hstable : (prefixWord ++ tailWord_4084489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4084489).length < 2 ^ (prefixWord ++ tailWord_4084489).sum := by decide
  have hdescent : baseEnd_4084489 < baseStart_4084489 := by decide
  rcases family_descends (prefixWord ++ tailWord_4084489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4084506 : List Nat := [3, 1, 1, 3, 2, 1, 2, 4, 1, 3, 2]
def baseStart_4084506 : Nat := 118140960795 + 4084506 * 2 ^ 59
def prefixEnd_4084506 : Nat := 4983230072969 + 3 ^ 40 * 4084506 * 2
def baseEnd_4084506 : Nat := 2097314814173301585190705

theorem tailTrace_4084506 : CollatzResearch.WordTrace tailWord_4084506 prefixEnd_4084506 2097314814173301585190705 := by
  unfold tailWord_4084506
  simp only [CollatzResearch.WordTrace]
  refine ⟨37243543135134953733220343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99316115027026543288587581 37243543135134953733220343)
  ·
    refine ⟨55865314702702430599830515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37243543135134953733220343 55865314702702430599830515)
    ·
      refine ⟨83797972054053645899745773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55865314702702430599830515 83797972054053645899745773)
      ·
        refine ⟨31424239520270117212404665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83797972054053645899745773 31424239520270117212404665)
        ·
          refine ⟨23568179640202587909303499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31424239520270117212404665 23568179640202587909303499)
          ·
            refine ⟨35352269460303881863955249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23568179640202587909303499 35352269460303881863955249)
            ·
              refine ⟨26514202095227911397966437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35352269460303881863955249 26514202095227911397966437)
              ·
                refine ⟨4971412892855233387118707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26514202095227911397966437 4971412892855233387118707)
                ·
                  refine ⟨7457119339282850080678061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4971412892855233387118707 7457119339282850080678061)
                  ·
                    refine ⟨2796419752231068780254273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7457119339282850080678061 2796419752231068780254273)
                    ·
                      refine ⟨2097314814173301585190705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2796419752231068780254273 2097314814173301585190705)
                      ·
                        rfl

theorem cell23_4084506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 4, 1, 3, 2].length) (baseStart_4084506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4084506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4084506 prefixEnd_4084506 := by exact prefixLift 4084506
  have htrace : WordTrace (prefixWord ++ tailWord_4084506) baseStart_4084506 baseEnd_4084506 := by
    simpa [prefixWord, tailWord_4084506, baseEnd_4084506] using wordTrace_append hprefix tailTrace_4084506
  have hstable : (prefixWord ++ tailWord_4084506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4084506).length < 2 ^ (prefixWord ++ tailWord_4084506).sum := by decide
  have hdescent : baseEnd_4084506 < baseStart_4084506 := by decide
  rcases family_descends (prefixWord ++ tailWord_4084506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4084536 : List Nat := [2, 1, 2, 1, 3, 2, 3, 1, 4, 2, 2]
def baseStart_4084536 : Nat := 118140960795 + 4084536 * 2 ^ 59
def prefixEnd_4084536 : Nat := 4983230072969 + 3 ^ 40 * 4084536 * 2
def baseEnd_4084536 : Nat := 2097330218592936467815567

theorem tailTrace_4084536 : CollatzResearch.WordTrace tailWord_4084536 prefixEnd_4084536 2097330218592936467815567 := by
  unfold tailWord_4084536
  simp only [CollatzResearch.WordTrace]
  refine ⟨74487633365215565028236731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99316844486954086704315641 74487633365215565028236731)
  ·
    refine ⟨111731450047823347542355097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74487633365215565028236731 111731450047823347542355097)
    ·
      refine ⟨83798587535867510656766323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111731450047823347542355097 83798587535867510656766323)
      ·
        refine ⟨125697881303801265985149485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83798587535867510656766323 125697881303801265985149485)
        ·
          refine ⟨47136705488925474744431057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125697881303801265985149485 47136705488925474744431057)
          ·
            refine ⟨35352529116694106058323293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47136705488925474744431057 35352529116694106058323293)
            ·
              refine ⟨13257198418760289771871235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35352529116694106058323293 13257198418760289771871235)
              ·
                refine ⟨19885797628140434657806853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13257198418760289771871235 19885797628140434657806853)
                ·
                  refine ⟨3728587055276331498338785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19885797628140434657806853 3728587055276331498338785)
                  ·
                    refine ⟨2796440291457248623754089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3728587055276331498338785 2796440291457248623754089)
                    ·
                      refine ⟨2097330218592936467815567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2796440291457248623754089 2097330218592936467815567)
                      ·
                        rfl

theorem cell23_4084536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 1, 4, 2, 2].length) (baseStart_4084536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4084536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4084536 prefixEnd_4084536 := by exact prefixLift 4084536
  have htrace : WordTrace (prefixWord ++ tailWord_4084536) baseStart_4084536 baseEnd_4084536 := by
    simpa [prefixWord, tailWord_4084536, baseEnd_4084536] using wordTrace_append hprefix tailTrace_4084536
  have hstable : (prefixWord ++ tailWord_4084536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4084536).length < 2 ^ (prefixWord ++ tailWord_4084536).sum := by decide
  have hdescent : baseEnd_4084536 < baseStart_4084536 := by decide
  rcases family_descends (prefixWord ++ tailWord_4084536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4084619 : List Nat := [1, 1, 1, 1, 4, 2, 2, 4, 3, 4]
def baseStart_4084619 : Nat := 118140960795 + 4084619 * 2 ^ 59
def prefixEnd_4084619 : Nat := 4983230072969 + 3 ^ 40 * 4084619 * 2
def baseEnd_4084619 : Nat := 699124279162419881025895

theorem tailTrace_4084619 : CollatzResearch.WordTrace tailWord_4084619 prefixEnd_4084619 699124279162419881025895 := by
  unfold tailWord_4084619
  simp only [CollatzResearch.WordTrace]
  refine ⟨148978293989130435231744911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99318862659420290154496607 148978293989130435231744911)
  ·
    refine ⟨223467440983695652847617367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148978293989130435231744911 223467440983695652847617367)
    ·
      refine ⟨335201161475543479271426051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223467440983695652847617367 335201161475543479271426051)
      ·
        refine ⟨502801742213315218907139077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335201161475543479271426051 502801742213315218907139077)
        ·
          refine ⟨94275326664996603545088577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 502801742213315218907139077 94275326664996603545088577)
          ·
            refine ⟨70706494998747452658816433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94275326664996603545088577 70706494998747452658816433)
            ·
              refine ⟨53029871249060589494112325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70706494998747452658816433 53029871249060589494112325)
              ·
                refine ⟨9943100859198860530146061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53029871249060589494112325 9943100859198860530146061)
                ·
                  refine ⟨3728662822199572698804773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9943100859198860530146061 3728662822199572698804773)
                  ·
                    refine ⟨699124279162419881025895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3728662822199572698804773 699124279162419881025895)
                    ·
                      rfl

theorem cell23_4084619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 4, 3, 4].length) (baseStart_4084619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4084619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4084619 prefixEnd_4084619 := by exact prefixLift 4084619
  have htrace : WordTrace (prefixWord ++ tailWord_4084619) baseStart_4084619 baseEnd_4084619 := by
    simpa [prefixWord, tailWord_4084619, baseEnd_4084619] using wordTrace_append hprefix tailTrace_4084619
  have hstable : (prefixWord ++ tailWord_4084619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4084619).length < 2 ^ (prefixWord ++ tailWord_4084619).sum := by decide
  have hdescent : baseEnd_4084619 < baseStart_4084619 := by decide
  rcases family_descends (prefixWord ++ tailWord_4084619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4084649 : List Nat := [1, 2, 1, 1, 1, 1, 8, 2, 6]
def baseStart_4084649 : Nat := 118140960795 + 4084649 * 2 ^ 59
def prefixEnd_4084649 : Nat := 4983230072969 + 3 ^ 40 * 4084649 * 2
def baseEnd_4084649 : Nat := 233043137989654947300283

theorem tailTrace_4084649 : CollatzResearch.WordTrace tailWord_4084649 prefixEnd_4084649 233043137989654947300283 := by
  unfold tailWord_4084649
  simp only [CollatzResearch.WordTrace]
  refine ⟨148979388179021750355337001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99319592119347833570224667 148979388179021750355337001)
  ·
    refine ⟨111734541134266312766502751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148979388179021750355337001 111734541134266312766502751)
    ·
      refine ⟨167601811701399469149754127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111734541134266312766502751 167601811701399469149754127)
      ·
        refine ⟨251402717552099203724631191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167601811701399469149754127 251402717552099203724631191)
        ·
          refine ⟨377104076328148805586946787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251402717552099203724631191 377104076328148805586946787)
          ·
            refine ⟨565656114492223208380420181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 377104076328148805586946787 565656114492223208380420181)
            ·
              refine ⟨6628782591705740723208049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 565656114492223208380420181 6628782591705740723208049)
              ·
                refine ⟨4971586943779305542406037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6628782591705740723208049 4971586943779305542406037)
                ·
                  refine ⟨233043137989654947300283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4971586943779305542406037 233043137989654947300283)
                  ·
                    rfl

theorem cell23_4084649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 8, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 8, 2, 6].length) (baseStart_4084649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4084649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4084649 prefixEnd_4084649 := by exact prefixLift 4084649
  have htrace : WordTrace (prefixWord ++ tailWord_4084649) baseStart_4084649 baseEnd_4084649 := by
    simpa [prefixWord, tailWord_4084649, baseEnd_4084649] using wordTrace_append hprefix tailTrace_4084649
  have hstable : (prefixWord ++ tailWord_4084649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4084649).length < 2 ^ (prefixWord ++ tailWord_4084649).sum := by decide
  have hdescent : baseEnd_4084649 < baseStart_4084649 := by decide
  rcases family_descends (prefixWord ++ tailWord_4084649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4084652 : List Nat := [2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 8]
def baseStart_4084652 : Nat := 118140960795 + 4084652 * 2 ^ 59
def prefixEnd_4084652 : Nat := 4983230072969 + 3 ^ 40 * 4084652 * 2
def baseEnd_4084652 : Nat := 2097389782348858013965033

theorem tailTrace_4084652 : CollatzResearch.WordTrace tailWord_4084652 prefixEnd_4084652 2097389782348858013965033 := by
  unfold tailWord_4084652
  simp only [CollatzResearch.WordTrace]
  refine ⟨74489748799005440933848105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99319665065340587911797473 74489748799005440933848105)
  ·
    refine ⟨55867311599254080700386079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74489748799005440933848105 55867311599254080700386079)
    ·
      refine ⟨83800967398881121050579119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55867311599254080700386079 83800967398881121050579119)
      ·
        refine ⟨125701451098321681575868679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83800967398881121050579119 125701451098321681575868679)
        ·
          refine ⟨188552176647482522363803019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125701451098321681575868679 188552176647482522363803019)
          ·
            refine ⟨282828264971223783545704529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188552176647482522363803019 282828264971223783545704529)
            ·
              refine ⟨212121198728417837659278397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 282828264971223783545704529 212121198728417837659278397)
              ·
                refine ⟨79545449523156689122229399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 212121198728417837659278397 79545449523156689122229399)
                ·
                  refine ⟨119318174284735033683344099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79545449523156689122229399 119318174284735033683344099)
                  ·
                    refine ⟨178977261427102550525016149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 119318174284735033683344099 178977261427102550525016149)
                    ·
                      refine ⟨2097389782348858013965033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 178977261427102550525016149 2097389782348858013965033)
                      ·
                        rfl

theorem cell23_4084652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 8].length) (baseStart_4084652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4084652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4084652 prefixEnd_4084652 := by exact prefixLift 4084652
  have htrace : WordTrace (prefixWord ++ tailWord_4084652) baseStart_4084652 baseEnd_4084652 := by
    simpa [prefixWord, tailWord_4084652, baseEnd_4084652] using wordTrace_append hprefix tailTrace_4084652
  have hstable : (prefixWord ++ tailWord_4084652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4084652).length < 2 ^ (prefixWord ++ tailWord_4084652).sum := by decide
  have hdescent : baseEnd_4084652 < baseStart_4084652 := by decide
  rcases family_descends (prefixWord ++ tailWord_4084652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4084660 : List Nat := [2, 5, 2, 1, 1, 2, 1, 1, 2, 4, 2]
def baseStart_4084660 : Nat := 118140960795 + 4084660 * 2 ^ 59
def prefixEnd_4084660 : Nat := 4983230072969 + 3 ^ 40 * 4084660 * 2
def baseEnd_4084660 : Nat := 2097393890194093982664997

theorem tailTrace_4084660 : CollatzResearch.WordTrace tailWord_4084660 prefixEnd_4084660 2097393890194093982664997 := by
  unfold tailWord_4084660
  simp only [CollatzResearch.WordTrace]
  refine ⟨74489894690990949616993717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99319859587987932822658289 74489894690990949616993717)
  ·
    refine ⟨6983427627280401526593161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 74489894690990949616993717 6983427627280401526593161)
    ·
      refine ⟨5237570720460301144944871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6983427627280401526593161 5237570720460301144944871)
      ·
        refine ⟨7856356080690451717417307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5237570720460301144944871 7856356080690451717417307)
        ·
          refine ⟨11784534121035677576125961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7856356080690451717417307 11784534121035677576125961)
          ·
            refine ⟨8838400590776758182094471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11784534121035677576125961 8838400590776758182094471)
            ·
              refine ⟨13257600886165137273141707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8838400590776758182094471 13257600886165137273141707)
              ·
                refine ⟨19886401329247705909712561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13257600886165137273141707 19886401329247705909712561)
                ·
                  refine ⟨14914800996935779432284421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19886401329247705909712561 14914800996935779432284421)
                  ·
                    refine ⟨2796525186925458643553329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14914800996935779432284421 2796525186925458643553329)
                    ·
                      refine ⟨2097393890194093982664997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2796525186925458643553329 2097393890194093982664997)
                      ·
                        rfl

theorem cell23_4084660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 1, 2, 4, 2].length) (baseStart_4084660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4084660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4084660 prefixEnd_4084660 := by exact prefixLift 4084660
  have htrace : WordTrace (prefixWord ++ tailWord_4084660) baseStart_4084660 baseEnd_4084660 := by
    simpa [prefixWord, tailWord_4084660, baseEnd_4084660] using wordTrace_append hprefix tailTrace_4084660
  have hstable : (prefixWord ++ tailWord_4084660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4084660).length < 2 ^ (prefixWord ++ tailWord_4084660).sum := by decide
  have hdescent : baseEnd_4084660 < baseStart_4084660 := by decide
  rcases family_descends (prefixWord ++ tailWord_4084660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4084679 : List Nat := [1, 1, 4, 1, 1, 2, 4, 1, 3, 5]
def baseStart_4084679 : Nat := 118140960795 + 4084679 * 2 ^ 59
def prefixEnd_4084679 : Nat := 4983230072969 + 3 ^ 40 * 4084679 * 2
def baseEnd_4084679 : Nat := 699134548775509802775803

theorem tailTrace_4084679 : CollatzResearch.WordTrace tailWord_4084679 prefixEnd_4084679 699134548775509802775803 := by
  unfold tailWord_4084679
  simp only [CollatzResearch.WordTrace]
  refine ⟨148980482368913065478929091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99320321579275376985952727 148980482368913065478929091)
  ·
    refine ⟨223470723553369598218393637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148980482368913065478929091 223470723553369598218393637)
    ·
      refine ⟨41900760666256799665948807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 223470723553369598218393637 41900760666256799665948807)
      ·
        refine ⟨62851140999385199498923211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41900760666256799665948807 62851140999385199498923211)
        ·
          refine ⟨94276711499077799248384817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62851140999385199498923211 94276711499077799248384817)
          ·
            refine ⟨70707533624308349436288613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94276711499077799248384817 70707533624308349436288613)
            ·
              refine ⟨13257662554557815519304115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70707533624308349436288613 13257662554557815519304115)
              ·
                refine ⟨19886493831836723278956173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13257662554557815519304115 19886493831836723278956173)
                ·
                  refine ⟨7457435186938771229608565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19886493831836723278956173 7457435186938771229608565)
                  ·
                    refine ⟨699134548775509802775803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7457435186938771229608565 699134548775509802775803)
                    ·
                      rfl

theorem cell23_4084679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 1, 3, 5].length) (baseStart_4084679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4084679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4084679 prefixEnd_4084679 := by exact prefixLift 4084679
  have htrace : WordTrace (prefixWord ++ tailWord_4084679) baseStart_4084679 baseEnd_4084679 := by
    simpa [prefixWord, tailWord_4084679, baseEnd_4084679] using wordTrace_append hprefix tailTrace_4084679
  have hstable : (prefixWord ++ tailWord_4084679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4084679).length < 2 ^ (prefixWord ++ tailWord_4084679).sum := by decide
  have hdescent : baseEnd_4084679 < baseStart_4084679 := by decide
  rcases family_descends (prefixWord ++ tailWord_4084679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4084680 : List Nat := [2, 1, 3, 1, 6, 1, 1, 1, 2, 2, 3]
def baseStart_4084680 : Nat := 118140960795 + 4084680 * 2 ^ 59
def prefixEnd_4084680 : Nat := 4983230072969 + 3 ^ 40 * 4084680 * 2
def baseEnd_4084680 : Nat := 2097404159807183904414905

theorem tailTrace_4084680 : CollatzResearch.WordTrace tailWord_4084680 prefixEnd_4084680 2097404159807183904414905 := by
  unfold tailWord_4084680
  simp only [CollatzResearch.WordTrace]
  refine ⟨74490259420954721324857747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99320345894606295099810329 74490259420954721324857747)
  ·
    refine ⟨111735389131432081987286621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74490259420954721324857747 111735389131432081987286621)
    ·
      refine ⟨41900770924287030745232483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111735389131432081987286621 41900770924287030745232483)
      ·
        refine ⟨62851156386430546117848725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41900770924287030745232483 62851156386430546117848725)
        ·
          refine ⟨2946147955613931849274159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 62851156386430546117848725 2946147955613931849274159)
          ·
            refine ⟨4419221933420897773911239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2946147955613931849274159 4419221933420897773911239)
            ·
              refine ⟨6628832900131346660866859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4419221933420897773911239 6628832900131346660866859)
              ·
                refine ⟨9943249350197019991300289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6628832900131346660866859 9943249350197019991300289)
                ·
                  refine ⟨7457437012647764993475217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9943249350197019991300289 7457437012647764993475217)
                  ·
                    refine ⟨5593077759485823745106413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7457437012647764993475217 5593077759485823745106413)
                    ·
                      refine ⟨2097404159807183904414905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5593077759485823745106413 2097404159807183904414905)
                      ·
                        rfl

theorem cell23_4084680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 1, 1, 2, 2, 3].length) (baseStart_4084680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4084680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4084680 prefixEnd_4084680 := by exact prefixLift 4084680
  have htrace : WordTrace (prefixWord ++ tailWord_4084680) baseStart_4084680 baseEnd_4084680 := by
    simpa [prefixWord, tailWord_4084680, baseEnd_4084680] using wordTrace_append hprefix tailTrace_4084680
  have hstable : (prefixWord ++ tailWord_4084680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4084680).length < 2 ^ (prefixWord ++ tailWord_4084680).sum := by decide
  have hdescent : baseEnd_4084680 < baseStart_4084680 := by decide
  rcases family_descends (prefixWord ++ tailWord_4084680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4084696 : List Nat := [2, 1, 2, 2, 2, 4, 1, 3, 1, 5]
def baseStart_4084696 : Nat := 118140960795 + 4084696 * 2 ^ 59
def prefixEnd_4084696 : Nat := 4983230072969 + 3 ^ 40 * 4084696 * 2
def baseEnd_4084696 : Nat := 699137458499218613938277

theorem tailTrace_4084696 : CollatzResearch.WordTrace tailWord_4084696 prefixEnd_4084696 699137458499218613938277 := by
  unfold tailWord_4084696
  simp only [CollatzResearch.WordTrace]
  refine ⟨74490551204925738691148971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99320734939900984921531961 74490551204925738691148971)
  ·
    refine ⟨111735826807388608036723457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74490551204925738691148971 111735826807388608036723457)
    ·
      refine ⟨83801870105541456027542593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111735826807388608036723457 83801870105541456027542593)
      ·
        refine ⟨62851402579156092020656945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83801870105541456027542593 62851402579156092020656945)
        ·
          refine ⟨47138551934367069015492709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62851402579156092020656945 47138551934367069015492709)
          ·
            refine ⟨8838478487693825440404883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47138551934367069015492709 8838478487693825440404883)
            ·
              refine ⟨13257717731540738160607325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8838478487693825440404883 13257717731540738160607325)
              ·
                refine ⟨4971644149327776810227747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13257717731540738160607325 4971644149327776810227747)
                ·
                  refine ⟨7457466223991665215341621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4971644149327776810227747 7457466223991665215341621)
                  ·
                    refine ⟨699137458499218613938277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7457466223991665215341621 699137458499218613938277)
                    ·
                      rfl

theorem cell23_4084696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 3, 1, 5].length) (baseStart_4084696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4084696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4084696 prefixEnd_4084696 := by exact prefixLift 4084696
  have htrace : WordTrace (prefixWord ++ tailWord_4084696) baseStart_4084696 baseEnd_4084696 := by
    simpa [prefixWord, tailWord_4084696, baseEnd_4084696] using wordTrace_append hprefix tailTrace_4084696
  have hstable : (prefixWord ++ tailWord_4084696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4084696).length < 2 ^ (prefixWord ++ tailWord_4084696).sum := by decide
  have hdescent : baseEnd_4084696 < baseStart_4084696 := by decide
  rcases family_descends (prefixWord ++ tailWord_4084696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4084719 : List Nat := [1, 1, 2, 1, 4, 3, 1, 1, 3, 1, 5]
def baseStart_4084719 : Nat := 118140960795 + 4084719 * 2 ^ 59
def prefixEnd_4084719 : Nat := 4983230072969 + 3 ^ 40 * 4084719 * 2
def baseEnd_4084719 : Nat := 2097424185552709251827225

theorem tailTrace_4084719 : CollatzResearch.WordTrace tailWord_4084719 prefixEnd_4084719 2097424185552709251827225 := by
  unfold tailWord_4084719
  simp only [CollatzResearch.WordTrace]
  refine ⟨148981941288768152310385211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99321294192512101540256807 148981941288768152310385211)
  ·
    refine ⟨223472911933152228465577817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148981941288768152310385211 223472911933152228465577817)
    ·
      refine ⟨167604683949864171349183363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223472911933152228465577817 167604683949864171349183363)
      ·
        refine ⟨251407025924796257023775045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167604683949864171349183363 251407025924796257023775045)
        ·
          refine ⟨47138817360899298191957821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 251407025924796257023775045 47138817360899298191957821)
          ·
            refine ⟨17677056510337236821984183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47138817360899298191957821 17677056510337236821984183)
            ·
              refine ⟨26515584765505855232976275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17677056510337236821984183 26515584765505855232976275)
              ·
                refine ⟨39773377148258782849464413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26515584765505855232976275 39773377148258782849464413)
                ·
                  refine ⟨14915016430597043568549155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39773377148258782849464413 14915016430597043568549155)
                  ·
                    refine ⟨22372524645895565352823733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14915016430597043568549155 22372524645895565352823733)
                    ·
                      refine ⟨2097424185552709251827225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22372524645895565352823733 2097424185552709251827225)
                      ·
                        rfl

theorem cell23_4084719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 1, 3, 1, 5].length) (baseStart_4084719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4084719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4084719 prefixEnd_4084719 := by exact prefixLift 4084719
  have htrace : WordTrace (prefixWord ++ tailWord_4084719) baseStart_4084719 baseEnd_4084719 := by
    simpa [prefixWord, tailWord_4084719, baseEnd_4084719] using wordTrace_append hprefix tailTrace_4084719
  have hstable : (prefixWord ++ tailWord_4084719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4084719).length < 2 ^ (prefixWord ++ tailWord_4084719).sum := by decide
  have hdescent : baseEnd_4084719 < baseStart_4084719 := by decide
  rcases family_descends (prefixWord ++ tailWord_4084719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4084729 : List Nat := [1, 2, 1, 3, 1, 3, 3, 1, 1, 1, 6]
def baseStart_4084729 : Nat := 118140960795 + 4084729 * 2 ^ 59
def prefixEnd_4084729 : Nat := 4983230072969 + 3 ^ 40 * 4084729 * 2
def baseEnd_4084729 : Nat := 2097429320359254212702179

theorem tailTrace_4084729 : CollatzResearch.WordTrace tailWord_4084729 prefixEnd_4084729 2097429320359254212702179 := by
  unfold tailWord_4084729
  simp only [CollatzResearch.WordTrace]
  refine ⟨148982306018731924018249241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99321537345821282678832827 148982306018731924018249241)
  ·
    refine ⟨111736729514048943013686931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148982306018731924018249241 111736729514048943013686931)
    ·
      refine ⟨167605094271073414520530397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111736729514048943013686931 167605094271073414520530397)
      ·
        refine ⟨62851910351652530445198899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167605094271073414520530397 62851910351652530445198899)
        ·
          refine ⟨94277865527478795667798349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62851910351652530445198899 94277865527478795667798349)
          ·
            refine ⟨35354199572804548375424381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94277865527478795667798349 35354199572804548375424381)
            ·
              refine ⟨13257824839801705640784143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35354199572804548375424381 13257824839801705640784143)
              ·
                refine ⟨19886737259702558461176215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13257824839801705640784143 19886737259702558461176215)
                ·
                  refine ⟨29830105889553837691764323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19886737259702558461176215 29830105889553837691764323)
                  ·
                    refine ⟨44745158834330756537646485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29830105889553837691764323 44745158834330756537646485)
                    ·
                      refine ⟨2097429320359254212702179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44745158834330756537646485 2097429320359254212702179)
                      ·
                        rfl

theorem cell23_4084729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 1, 1, 1, 6].length) (baseStart_4084729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4084729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4084729 prefixEnd_4084729 := by exact prefixLift 4084729
  have htrace : WordTrace (prefixWord ++ tailWord_4084729) baseStart_4084729 baseEnd_4084729 := by
    simpa [prefixWord, tailWord_4084729, baseEnd_4084729] using wordTrace_append hprefix tailTrace_4084729
  have hstable : (prefixWord ++ tailWord_4084729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4084729).length < 2 ^ (prefixWord ++ tailWord_4084729).sum := by decide
  have hdescent : baseEnd_4084729 < baseStart_4084729 := by decide
  rcases family_descends (prefixWord ++ tailWord_4084729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4084754 : List Nat := [3, 2, 5, 1, 1, 1, 1, 2, 2, 3, 2]
def baseStart_4084754 : Nat := 118140960795 + 4084754 * 2 ^ 59
def prefixEnd_4084754 : Nat := 4983230072969 + 3 ^ 40 * 4084754 * 2
def baseEnd_4084754 : Nat := 2097442157375616614889565

theorem tailTrace_4084754 : CollatzResearch.WordTrace tailWord_4084754 prefixEnd_4084754 2097442157375616614889565 := by
  unfold tailWord_4084754
  simp only [CollatzResearch.WordTrace]
  refine ⟨37245804460910338321977329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99322145229094235525272877 37245804460910338321977329)
  ·
    refine ⟨27934353345682753741482997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37245804460910338321977329 27934353345682753741482997)
    ·
      refine ⟨2618845626157758163264031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27934353345682753741482997 2618845626157758163264031)
      ·
        refine ⟨3928268439236637244896047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2618845626157758163264031 3928268439236637244896047)
        ·
          refine ⟨5892402658854955867344071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3928268439236637244896047 5892402658854955867344071)
          ·
            refine ⟨8838603988282433801016107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5892402658854955867344071 8838603988282433801016107)
            ·
              refine ⟨13257905982423650701524161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8838603988282433801016107 13257905982423650701524161)
              ·
                refine ⟨9943429486817738026143121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13257905982423650701524161 9943429486817738026143121)
                ·
                  refine ⟨7457572115113303519607341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9943429486817738026143121 7457572115113303519607341)
                  ·
                    refine ⟨2796589543167488819852753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7457572115113303519607341 2796589543167488819852753)
                    ·
                      refine ⟨2097442157375616614889565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2796589543167488819852753 2097442157375616614889565)
                      ·
                        rfl

theorem cell23_4084754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_4084754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4084754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4084754 prefixEnd_4084754 := by exact prefixLift 4084754
  have htrace : WordTrace (prefixWord ++ tailWord_4084754) baseStart_4084754 baseEnd_4084754 := by
    simpa [prefixWord, tailWord_4084754, baseEnd_4084754] using wordTrace_append hprefix tailTrace_4084754
  have hstable : (prefixWord ++ tailWord_4084754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4084754).length < 2 ^ (prefixWord ++ tailWord_4084754).sum := by decide
  have hdescent : baseEnd_4084754 < baseStart_4084754 := by decide
  rcases family_descends (prefixWord ++ tailWord_4084754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4084789 : List Nat := [1, 3, 3, 1, 1, 1, 1, 1, 1, 2, 8]
def baseStart_4084789 : Nat := 118140960795 + 4084789 * 2 ^ 59
def prefixEnd_4084789 : Nat := 4983230072969 + 3 ^ 40 * 4084789 * 2
def baseEnd_4084789 : Nat := 2097460129198523977951903

theorem tailTrace_4084789 : CollatzResearch.WordTrace tailWord_4084789 prefixEnd_4084789 2097460129198523977951903 := by
  unfold tailWord_4084789
  simp only [CollatzResearch.WordTrace]
  refine ⟨148984494398514554265433421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99322996265676369510288947 148984494398514554265433421)
  ·
    refine ⟨55869185399442957849537533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148984494398514554265433421 55869185399442957849537533)
    ·
      refine ⟨20950944524791109193576575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55869185399442957849537533 20950944524791109193576575)
      ·
        refine ⟨31426416787186663790364863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20950944524791109193576575 31426416787186663790364863)
        ·
          refine ⟨47139625180779995685547295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31426416787186663790364863 47139625180779995685547295)
          ·
            refine ⟨70709437771169993528320943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47139625180779995685547295 70709437771169993528320943)
            ·
              refine ⟨106064156656754990292481415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70709437771169993528320943 106064156656754990292481415)
              ·
                refine ⟨159096234985132485438722123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106064156656754990292481415 159096234985132485438722123)
                ·
                  refine ⟨238644352477698728158083185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 159096234985132485438722123 238644352477698728158083185)
                  ·
                    refine ⟨178983264358274046118562389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 238644352477698728158083185 178983264358274046118562389)
                    ·
                      refine ⟨2097460129198523977951903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 178983264358274046118562389 2097460129198523977951903)
                      ·
                        rfl

theorem cell23_4084789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 2, 8].length) (baseStart_4084789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4084789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4084789 prefixEnd_4084789 := by exact prefixLift 4084789
  have htrace : WordTrace (prefixWord ++ tailWord_4084789) baseStart_4084789 baseEnd_4084789 := by
    simpa [prefixWord, tailWord_4084789, baseEnd_4084789] using wordTrace_append hprefix tailTrace_4084789
  have hstable : (prefixWord ++ tailWord_4084789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4084789).length < 2 ^ (prefixWord ++ tailWord_4084789).sum := by decide
  have hdescent : baseEnd_4084789 < baseStart_4084789 := by decide
  rcases family_descends (prefixWord ++ tailWord_4084789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4084799 : List Nat := [1, 1, 2, 2, 3, 1, 1, 2, 4, 6]
def baseStart_4084799 : Nat := 118140960795 + 4084799 * 2 ^ 59
def prefixEnd_4084799 : Nat := 4983230072969 + 3 ^ 40 * 4084799 * 2
def baseEnd_4084799 : Nat := 699155088001689646275619

theorem tailTrace_4084799 : CollatzResearch.WordTrace tailWord_4084799 prefixEnd_4084799 699155088001689646275619 := by
  unfold tailWord_4084799
  simp only [CollatzResearch.WordTrace]
  refine ⟨148984859128478325973297451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99323239418985550648864967 148984859128478325973297451)
  ·
    refine ⟨223477288692717488959946177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148984859128478325973297451 223477288692717488959946177)
    ·
      refine ⟨167607966519538116719959633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223477288692717488959946177 167607966519538116719959633)
      ·
        refine ⟨125705974889653587539969725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167607966519538116719959633 125705974889653587539969725)
        ·
          refine ⟨47139740583620095327488647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125705974889653587539969725 47139740583620095327488647)
          ·
            refine ⟨70709610875430142991232971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47139740583620095327488647 70709610875430142991232971)
            ·
              refine ⟨106064416313145214486849457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70709610875430142991232971 106064416313145214486849457)
              ·
                refine ⟨79548312234858910865137093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106064416313145214486849457 79548312234858910865137093)
                ·
                  refine ⟨14915308544036045787213205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79548312234858910865137093 14915308544036045787213205)
                  ·
                    refine ⟨699155088001689646275619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14915308544036045787213205 699155088001689646275619)
                    ·
                      rfl

theorem cell23_4084799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 2, 4, 6].length) (baseStart_4084799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4084799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4084799 prefixEnd_4084799 := by exact prefixLift 4084799
  have htrace : WordTrace (prefixWord ++ tailWord_4084799) baseStart_4084799 baseEnd_4084799 := by
    simpa [prefixWord, tailWord_4084799, baseEnd_4084799] using wordTrace_append hprefix tailTrace_4084799
  have hstable : (prefixWord ++ tailWord_4084799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4084799).length < 2 ^ (prefixWord ++ tailWord_4084799).sum := by decide
  have hdescent : baseEnd_4084799 < baseStart_4084799 := by decide
  rcases family_descends (prefixWord ++ tailWord_4084799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4084809 : List Nat := [1, 2, 1, 1, 2, 2, 2, 3, 1, 3, 5]
def baseStart_4084809 : Nat := 118140960795 + 4084809 * 2 ^ 59
def prefixEnd_4084809 : Nat := 4983230072969 + 3 ^ 40 * 4084809 * 2
def baseEnd_4084809 : Nat := 2097470398811613899701811

theorem tailTrace_4084809 : CollatzResearch.WordTrace tailWord_4084809 prefixEnd_4084809 2097470398811613899701811 := by
  unfold tailWord_4084809
  simp only [CollatzResearch.WordTrace]
  refine ⟨148985223858442097681161481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99323482572294731787440987 148985223858442097681161481)
  ·
    refine ⟨111738917893831573260871111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148985223858442097681161481 111738917893831573260871111)
    ·
      refine ⟨167608376840747359891306667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111738917893831573260871111 167608376840747359891306667)
      ·
        refine ⟨251412565261121039836960001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167608376840747359891306667 251412565261121039836960001)
        ·
          refine ⟨188559423945840779877720001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 251412565261121039836960001 188559423945840779877720001)
          ·
            refine ⟨141419567959380584908290001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188559423945840779877720001 141419567959380584908290001)
            ·
              refine ⟨106064675969535438681217501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141419567959380584908290001 106064675969535438681217501)
              ·
                refine ⟨39774253488575789505456563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 106064675969535438681217501 39774253488575789505456563)
                ·
                  refine ⟨59661380232863684258184845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39774253488575789505456563 59661380232863684258184845)
                  ·
                    refine ⟨22373017587323881596819317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59661380232863684258184845 22373017587323881596819317)
                    ·
                      refine ⟨2097470398811613899701811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22373017587323881596819317 2097470398811613899701811)
                      ·
                        rfl

theorem cell23_4084809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 3, 1, 3, 5].length) (baseStart_4084809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4084809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4084809 prefixEnd_4084809 := by exact prefixLift 4084809
  have htrace : WordTrace (prefixWord ++ tailWord_4084809) baseStart_4084809 baseEnd_4084809 := by
    simpa [prefixWord, tailWord_4084809, baseEnd_4084809] using wordTrace_append hprefix tailTrace_4084809
  have hstable : (prefixWord ++ tailWord_4084809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4084809).length < 2 ^ (prefixWord ++ tailWord_4084809).sum := by decide
  have hdescent : baseEnd_4084809 < baseStart_4084809 := by decide
  rcases family_descends (prefixWord ++ tailWord_4084809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4084846 : List Nat := [4, 1, 2, 2, 1, 2, 1, 1, 9]
def baseStart_4084846 : Nat := 118140960795 + 4084846 * 2 ^ 59
def prefixEnd_4084846 : Nat := 4983230072969 + 3 ^ 40 * 4084846 * 2
def baseEnd_4084846 : Nat := 233054377510647806104349

theorem tailTrace_4084846 : CollatzResearch.WordTrace tailWord_4084846 prefixEnd_4084846 233054377510647806104349 := by
  unfold tailWord_4084846
  simp only [CollatzResearch.WordTrace]
  refine ⟨18623321669913506625032299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99324382239538702000172261 18623321669913506625032299)
  ·
    refine ⟨27934982504870259937548449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18623321669913506625032299 27934982504870259937548449)
    ·
      refine ⟨20951236878652694953161337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27934982504870259937548449 20951236878652694953161337)
      ·
        refine ⟨15713427658989521214871003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20951236878652694953161337 15713427658989521214871003)
        ·
          refine ⟨23570141488484281822306505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15713427658989521214871003 23570141488484281822306505)
          ·
            refine ⟨17677606116363211366729879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23570141488484281822306505 17677606116363211366729879)
            ·
              refine ⟨26516409174544817050094819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17677606116363211366729879 26516409174544817050094819)
              ·
                refine ⟨39774613761817225575142229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26516409174544817050094819 39774613761817225575142229)
                ·
                  refine ⟨233054377510647806104349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 39774613761817225575142229 233054377510647806104349)
                  ·
                    rfl

theorem cell23_4084846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 1, 9].length) (baseStart_4084846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4084846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4084846 prefixEnd_4084846 := by exact prefixLift 4084846
  have htrace : WordTrace (prefixWord ++ tailWord_4084846) baseStart_4084846 baseEnd_4084846 := by
    simpa [prefixWord, tailWord_4084846, baseEnd_4084846] using wordTrace_append hprefix tailTrace_4084846
  have hstable : (prefixWord ++ tailWord_4084846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4084846).length < 2 ^ (prefixWord ++ tailWord_4084846).sum := by decide
  have hdescent : baseEnd_4084846 < baseStart_4084846 := by decide
  rcases family_descends (prefixWord ++ tailWord_4084846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4084876 : List Nat := [2, 2, 1, 2, 1, 1, 1, 6, 2, 5]
def baseStart_4084876 : Nat := 118140960795 + 4084876 * 2 ^ 59
def prefixEnd_4084876 : Nat := 4983230072969 + 3 ^ 40 * 4084876 * 2
def baseEnd_4084876 : Nat := 699168267338488379188001

theorem tailTrace_4084876 : CollatzResearch.WordTrace tailWord_4084876 prefixEnd_4084876 699168267338488379188001 := by
  unfold tailWord_4084876
  simp only [CollatzResearch.WordTrace]
  refine ⟨74493833774599684061925241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99325111699466245415900321 74493833774599684061925241)
  ·
    refine ⟨55870375330949763046443931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74493833774599684061925241 55870375330949763046443931)
    ·
      refine ⟨83805562996424644569665897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55870375330949763046443931 83805562996424644569665897)
      ·
        refine ⟨62854172247318483427249423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83805562996424644569665897 62854172247318483427249423)
        ·
          refine ⟨94281258370977725140874135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62854172247318483427249423 94281258370977725140874135)
          ·
            refine ⟨141421887556466587711311203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94281258370977725140874135 141421887556466587711311203)
            ·
              refine ⟨212132831334699881566966805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141421887556466587711311203 212132831334699881566966805)
              ·
                refine ⟨9943726468814056948451569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 212132831334699881566966805 9943726468814056948451569)
                ·
                  refine ⟨7457794851610542711338677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9943726468814056948451569 7457794851610542711338677)
                  ·
                    refine ⟨699168267338488379188001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7457794851610542711338677 699168267338488379188001)
                    ·
                      rfl

theorem cell23_4084876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 6, 2, 5].length) (baseStart_4084876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4084876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4084876 prefixEnd_4084876 := by exact prefixLift 4084876
  have htrace : WordTrace (prefixWord ++ tailWord_4084876) baseStart_4084876 baseEnd_4084876 := by
    simpa [prefixWord, tailWord_4084876, baseEnd_4084876] using wordTrace_append hprefix tailTrace_4084876
  have hstable : (prefixWord ++ tailWord_4084876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4084876).length < 2 ^ (prefixWord ++ tailWord_4084876).sum := by decide
  have hdescent : baseEnd_4084876 < baseStart_4084876 := by decide
  rcases family_descends (prefixWord ++ tailWord_4084876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4084896 : List Nat := [2, 1, 1, 4, 2, 1, 1, 1, 3, 3, 4]
def baseStart_4084896 : Nat := 118140960795 + 4084896 * 2 ^ 59
def prefixEnd_4084896 : Nat := 4983230072969 + 3 ^ 40 * 4084896 * 2
def baseEnd_4084896 : Nat := 2097515071628555059313911

theorem tailTrace_4084896 : CollatzResearch.WordTrace tailWord_4084896 prefixEnd_4084896 2097515071628555059313911 := by
  unfold tailWord_4084896
  simp only [CollatzResearch.WordTrace]
  refine ⟨74494198504563455769789271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99325598006084607693052361 74494198504563455769789271)
  ·
    refine ⟨111741297756845183654683907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74494198504563455769789271 111741297756845183654683907)
    ·
      refine ⟨167611946635267775482025861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111741297756845183654683907 167611946635267775482025861)
      ·
        refine ⟨31427239994112707902879849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 167611946635267775482025861 31427239994112707902879849)
        ·
          refine ⟨23570429995584530927159887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31427239994112707902879849 23570429995584530927159887)
          ·
            refine ⟨35355644993376796390739831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23570429995584530927159887 35355644993376796390739831)
            ·
              refine ⟨53033467490065194586109747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35355644993376796390739831 53033467490065194586109747)
              ·
                refine ⟨79550201235097791879164621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53033467490065194586109747 79550201235097791879164621)
                ·
                  refine ⟨29831325463161671954686733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79550201235097791879164621 29831325463161671954686733)
                  ·
                    refine ⟨11186747048685626983007525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29831325463161671954686733 11186747048685626983007525)
                    ·
                      refine ⟨2097515071628555059313911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11186747048685626983007525 2097515071628555059313911)
                      ·
                        rfl

theorem cell23_4084896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 1, 3, 3, 4].length) (baseStart_4084896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4084896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4084896 prefixEnd_4084896 := by exact prefixLift 4084896
  have htrace : WordTrace (prefixWord ++ tailWord_4084896) baseStart_4084896 baseEnd_4084896 := by
    simpa [prefixWord, tailWord_4084896, baseEnd_4084896] using wordTrace_append hprefix tailTrace_4084896
  have hstable : (prefixWord ++ tailWord_4084896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4084896).length < 2 ^ (prefixWord ++ tailWord_4084896).sum := by decide
  have hdescent : baseEnd_4084896 < baseStart_4084896 := by decide
  rcases family_descends (prefixWord ++ tailWord_4084896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4084913 : List Nat := [1, 2, 2, 5, 1, 1, 2, 1, 1, 3, 4]
def baseStart_4084913 : Nat := 118140960795 + 4084913 * 2 ^ 59
def prefixEnd_4084913 : Nat := 4983230072969 + 3 ^ 40 * 4084913 * 2
def baseEnd_4084913 : Nat := 2097523800799681492801333

theorem tailTrace_4084913 : CollatzResearch.WordTrace tailWord_4084913 prefixEnd_4084913 2097523800799681492801333 := by
  unfold tailWord_4084913
  simp only [CollatzResearch.WordTrace]
  refine ⟨148989017050065323442947393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99326011366710215628631595 148989017050065323442947393)
  ·
    refine ⟨111741762787548992582210545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148989017050065323442947393 111741762787548992582210545)
    ·
      refine ⟨83806322090661744436657909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111741762787548992582210545 83806322090661744436657909)
      ·
        refine ⟨7856842695999538540936679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 83806322090661744436657909 7856842695999538540936679)
        ·
          refine ⟨11785264043999307811405019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7856842695999538540936679 11785264043999307811405019)
          ·
            refine ⟨17677896065998961717107529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11785264043999307811405019 17677896065998961717107529)
            ·
              refine ⟨13258422049499221287830647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17677896065998961717107529 13258422049499221287830647)
              ·
                refine ⟨19887633074248831931745971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13258422049499221287830647 19887633074248831931745971)
                ·
                  refine ⟨29831449611373247897618957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19887633074248831931745971 29831449611373247897618957)
                  ·
                    refine ⟨11186793604264967961607109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29831449611373247897618957 11186793604264967961607109)
                    ·
                      refine ⟨2097523800799681492801333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11186793604264967961607109 2097523800799681492801333)
                      ·
                        rfl

theorem cell23_4084913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_4084913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4084913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4084913 prefixEnd_4084913 := by exact prefixLift 4084913
  have htrace : WordTrace (prefixWord ++ tailWord_4084913) baseStart_4084913 baseEnd_4084913 := by
    simpa [prefixWord, tailWord_4084913, baseEnd_4084913] using wordTrace_append hprefix tailTrace_4084913
  have hstable : (prefixWord ++ tailWord_4084913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4084913).length < 2 ^ (prefixWord ++ tailWord_4084913).sum := by decide
  have hdescent : baseEnd_4084913 < baseStart_4084913 := by decide
  rcases family_descends (prefixWord ++ tailWord_4084913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4084936 : List Nat := [2, 1, 3, 1, 2, 1, 4, 1, 8]
def baseStart_4084936 : Nat := 118140960795 + 4084936 * 2 ^ 59
def prefixEnd_4084936 : Nat := 4983230072969 + 3 ^ 40 * 4084936 * 2
def baseEnd_4084936 : Nat := 233059512317192766979303

theorem tailTrace_4084936 : CollatzResearch.WordTrace tailWord_4084936 prefixEnd_4084936 233059512317192766979303 := by
  unfold tailWord_4084936
  simp only [CollatzResearch.WordTrace]
  refine ⟨74494927964490999185517331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99326570619321332247356441 74494927964490999185517331)
  ·
    refine ⟨111742391946736498778275997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74494927964490999185517331 111742391946736498778275997)
    ·
      refine ⟨41903396980026187041853499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111742391946736498778275997 41903396980026187041853499)
      ·
        refine ⟨62855095470039280562780249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41903396980026187041853499 62855095470039280562780249)
        ·
          refine ⟨47141321602529460422085187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62855095470039280562780249 47141321602529460422085187)
          ·
            refine ⟨70711982403794190633127781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47141321602529460422085187 70711982403794190633127781)
            ·
              refine ⟨13258496700711410743711459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70711982403794190633127781 13258496700711410743711459)
              ·
                refine ⟨19887745051067116115567189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13258496700711410743711459 19887745051067116115567189)
                ·
                  refine ⟨233059512317192766979303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19887745051067116115567189 233059512317192766979303)
                  ·
                    rfl

theorem cell23_4084936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 1, 8].length) (baseStart_4084936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4084936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4084936 prefixEnd_4084936 := by exact prefixLift 4084936
  have htrace : WordTrace (prefixWord ++ tailWord_4084936) baseStart_4084936 baseEnd_4084936 := by
    simpa [prefixWord, tailWord_4084936, baseEnd_4084936] using wordTrace_append hprefix tailTrace_4084936
  have hstable : (prefixWord ++ tailWord_4084936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4084936).length < 2 ^ (prefixWord ++ tailWord_4084936).sum := by decide
  have hdescent : baseEnd_4084936 < baseStart_4084936 := by decide
  rcases family_descends (prefixWord ++ tailWord_4084936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4084967 : List Nat := [1, 1, 5, 3, 2, 1, 2, 1, 2, 2, 3]
def baseStart_4084967 : Nat := 118140960795 + 4084967 * 2 ^ 59
def prefixEnd_4084967 : Nat := 4983230072969 + 3 ^ 40 * 4084967 * 2
def baseEnd_4084967 : Nat := 2097551528755024281526085

theorem tailTrace_4084967 : CollatzResearch.WordTrace tailWord_4084967 prefixEnd_4084967 2097551528755024281526085 := by
  unfold tailWord_4084967
  simp only [CollatzResearch.WordTrace]
  refine ⟨148990986591869690665413155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99327324394579793776942103 148990986591869690665413155)
  ·
    refine ⟨223486479887804535998119733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148990986591869690665413155 223486479887804535998119733)
    ·
      refine ⟨20951857489481675249823725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 223486479887804535998119733 20951857489481675249823725)
      ·
        refine ⟨7856946558555628218683897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20951857489481675249823725 7856946558555628218683897)
        ·
          refine ⟨5892709918916721164012923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7856946558555628218683897 5892709918916721164012923)
          ·
            refine ⟨8839064878375081746019385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5892709918916721164012923 8839064878375081746019385)
            ·
              refine ⟨6629298658781311309514539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8839064878375081746019385 6629298658781311309514539)
              ·
                refine ⟨9943947988171966964271809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6629298658781311309514539 9943947988171966964271809)
                ·
                  refine ⟨7457960991128975223203857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9943947988171966964271809 7457960991128975223203857)
                  ·
                    refine ⟨5593470743346731417402893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7457960991128975223203857 5593470743346731417402893)
                    ·
                      refine ⟨2097551528755024281526085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5593470743346731417402893 2097551528755024281526085)
                      ·
                        rfl

theorem cell23_4084967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_4084967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4084967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4084967 prefixEnd_4084967 := by exact prefixLift 4084967
  have htrace : WordTrace (prefixWord ++ tailWord_4084967) baseStart_4084967 baseEnd_4084967 := by
    simpa [prefixWord, tailWord_4084967, baseEnd_4084967] using wordTrace_append hprefix tailTrace_4084967
  have hstable : (prefixWord ++ tailWord_4084967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4084967).length < 2 ^ (prefixWord ++ tailWord_4084967).sum := by decide
  have hdescent : baseEnd_4084967 < baseStart_4084967 := by decide
  rcases family_descends (prefixWord ++ tailWord_4084967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4084997 : List Nat := [1, 3, 1, 1, 2, 1, 5, 4, 1, 1, 3]
def baseStart_4084997 : Nat := 118140960795 + 4084997 * 2 ^ 59
def prefixEnd_4084997 : Nat := 4983230072969 + 3 ^ 40 * 4084997 * 2
def baseEnd_4084997 : Nat := 2097566933174659164150947

theorem tailTrace_4084997 : CollatzResearch.WordTrace tailWord_4084997 prefixEnd_4084997 2097566933174659164150947 := by
  unfold tailWord_4084997
  simp only [CollatzResearch.WordTrace]
  refine ⟨148992080781761005789005245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99328053854507337192670163 148992080781761005789005245)
  ·
    refine ⟨55872030293160377170876967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148992080781761005789005245 55872030293160377170876967)
    ·
      refine ⟨83808045439740565756315451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55872030293160377170876967 83808045439740565756315451)
      ·
        refine ⟨125712068159610848634473177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83808045439740565756315451 125712068159610848634473177)
        ·
          refine ⟨94284051119708136475854883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125712068159610848634473177 94284051119708136475854883)
          ·
            refine ⟨141426076679562204713782325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94284051119708136475854883 141426076679562204713782325)
            ·
              refine ⟨13258694688708956691917093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 141426076679562204713782325 13258694688708956691917093)
              ·
                refine ⟨2486005254132929379734455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13258694688708956691917093 2486005254132929379734455)
                ·
                  refine ⟨3729007881199394069601683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2486005254132929379734455 3729007881199394069601683)
                  ·
                    refine ⟨5593511821799091104402525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3729007881199394069601683 5593511821799091104402525)
                    ·
                      refine ⟨2097566933174659164150947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5593511821799091104402525 2097566933174659164150947)
                      ·
                        rfl

theorem cell23_4084997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 4, 1, 1, 3].length) (baseStart_4084997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4084997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4084997 prefixEnd_4084997 := by exact prefixLift 4084997
  have htrace : WordTrace (prefixWord ++ tailWord_4084997) baseStart_4084997 baseEnd_4084997 := by
    simpa [prefixWord, tailWord_4084997, baseEnd_4084997] using wordTrace_append hprefix tailTrace_4084997
  have hstable : (prefixWord ++ tailWord_4084997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4084997).length < 2 ^ (prefixWord ++ tailWord_4084997).sum := by decide
  have hdescent : baseEnd_4084997 < baseStart_4084997 := by decide
  rcases family_descends (prefixWord ++ tailWord_4084997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4085003 : List Nat := [1, 1, 1, 1, 5, 3, 1, 2, 3, 1, 4]
def baseStart_4085003 : Nat := 118140960795 + 4085003 * 2 ^ 59
def prefixEnd_4085003 : Nat := 4983230072969 + 3 ^ 40 * 4085003 * 2
def baseEnd_4085003 : Nat := 2097570014058586140675919

theorem tailTrace_4085003 : CollatzResearch.WordTrace tailWord_4085003 prefixEnd_4085003 2097570014058586140675919 := by
  unfold tailWord_4085003
  simp only [CollatzResearch.WordTrace]
  refine ⟨148992299619739268813723663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99328199746492845875815775 148992299619739268813723663)
  ·
    refine ⟨223488449429608903220585495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148992299619739268813723663 223488449429608903220585495)
    ·
      refine ⟨335232674144413354830878243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223488449429608903220585495 335232674144413354830878243)
      ·
        refine ⟨502849011216620032246317365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335232674144413354830878243 502849011216620032246317365)
        ·
          refine ⟨47142094801558128023092253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 502849011216620032246317365 47142094801558128023092253)
          ·
            refine ⟨17678285550584298008659595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47142094801558128023092253 17678285550584298008659595)
            ·
              refine ⟨26517428325876447012989393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17678285550584298008659595 26517428325876447012989393)
              ·
                refine ⟨19888071244407335259742045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26517428325876447012989393 19888071244407335259742045)
                ·
                  refine ⟨7458026716652750722403267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19888071244407335259742045 7458026716652750722403267)
                  ·
                    refine ⟨11187040074979126083604901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7458026716652750722403267 11187040074979126083604901)
                    ·
                      refine ⟨2097570014058586140675919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11187040074979126083604901 2097570014058586140675919)
                      ·
                        rfl

theorem cell23_4085003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 2, 3, 1, 4].length) (baseStart_4085003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4085003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4085003 prefixEnd_4085003 := by exact prefixLift 4085003
  have htrace : WordTrace (prefixWord ++ tailWord_4085003) baseStart_4085003 baseEnd_4085003 := by
    simpa [prefixWord, tailWord_4085003, baseEnd_4085003] using wordTrace_append hprefix tailTrace_4085003
  have hstable : (prefixWord ++ tailWord_4085003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4085003).length < 2 ^ (prefixWord ++ tailWord_4085003).sum := by decide
  have hdescent : baseEnd_4085003 < baseStart_4085003 := by decide
  rcases family_descends (prefixWord ++ tailWord_4085003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4085013 : List Nat := [1, 3, 2, 1, 2, 1, 1, 2, 6, 4]
def baseStart_4085013 : Nat := 118140960795 + 4085013 * 2 ^ 59
def prefixEnd_4085013 : Nat := 4983230072969 + 3 ^ 40 * 4085013 * 2
def baseEnd_4085013 : Nat := 699191716288377033850291

theorem tailTrace_4085013 : CollatzResearch.WordTrace tailWord_4085013 prefixEnd_4085013 699191716288377033850291 := by
  unfold tailWord_4085013
  simp only [CollatzResearch.WordTrace]
  refine ⟨148992664349703040521587693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99328442899802027014391795 148992664349703040521587693)
  ·
    refine ⟨55872249131138640195595385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148992664349703040521587693 55872249131138640195595385)
    ·
      refine ⟨41904186848353980146696539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55872249131138640195595385 41904186848353980146696539)
      ·
        refine ⟨62856280272530970220044809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41904186848353980146696539 62856280272530970220044809)
        ·
          refine ⟨47142210204398227665033607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62856280272530970220044809 47142210204398227665033607)
          ·
            refine ⟨70713315306597341497550411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47142210204398227665033607 70713315306597341497550411)
            ·
              refine ⟨106069972959896012246325617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70713315306597341497550411 106069972959896012246325617)
              ·
                refine ⟨79552479719922009184744213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106069972959896012246325617 79552479719922009184744213)
                ·
                  refine ⟨3729022486871344180534885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 79552479719922009184744213 3729022486871344180534885)
                  ·
                    refine ⟨699191716288377033850291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3729022486871344180534885 699191716288377033850291)
                    ·
                      rfl

theorem cell23_4085013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 2, 6, 4].length) (baseStart_4085013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4085013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4085013 prefixEnd_4085013 := by exact prefixLift 4085013
  have htrace : WordTrace (prefixWord ++ tailWord_4085013) baseStart_4085013 baseEnd_4085013 := by
    simpa [prefixWord, tailWord_4085013, baseEnd_4085013] using wordTrace_append hprefix tailTrace_4085013
  have hstable : (prefixWord ++ tailWord_4085013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4085013).length < 2 ^ (prefixWord ++ tailWord_4085013).sum := by decide
  have hdescent : baseEnd_4085013 < baseStart_4085013 := by decide
  rcases family_descends (prefixWord ++ tailWord_4085013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4085024 : List Nat := [2, 1, 1, 5, 3, 2, 1, 1, 2, 3, 2]
def baseStart_4085024 : Nat := 118140960795 + 4085024 * 2 ^ 59
def prefixEnd_4085024 : Nat := 4983230072969 + 3 ^ 40 * 4085024 * 2
def baseEnd_4085024 : Nat := 2097580797152330558513323

theorem tailTrace_4085024 : CollatzResearch.WordTrace tailWord_4085024 prefixEnd_4085024 2097580797152330558513323 := by
  unfold tailWord_4085024
  simp only [CollatzResearch.WordTrace]
  refine ⟨74496532776331594700119063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99328710368442126266825417 74496532776331594700119063)
  ·
    refine ⟨111744799164497392050178595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74496532776331594700119063 111744799164497392050178595)
    ·
      refine ⟨167617198746746088075267893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111744799164497392050178595 167617198746746088075267893)
      ·
        refine ⟨15714112382507445757056365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 167617198746746088075267893 15714112382507445757056365)
        ·
          refine ⟨5892792143440292158896137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15714112382507445757056365 5892792143440292158896137)
          ·
            refine ⟨4419594107580219119172103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5892792143440292158896137 4419594107580219119172103)
            ·
              refine ⟨6629391161370328678758155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4419594107580219119172103 6629391161370328678758155)
              ·
                refine ⟨9944086742055493018137233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6629391161370328678758155 9944086742055493018137233)
                ·
                  refine ⟨7458065056541619763602925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9944086742055493018137233 7458065056541619763602925)
                  ·
                    refine ⟨2796774396203107411351097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7458065056541619763602925 2796774396203107411351097)
                    ·
                      refine ⟨2097580797152330558513323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2796774396203107411351097 2097580797152330558513323)
                      ·
                        rfl

theorem cell23_4085024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 1, 1, 2, 3, 2].length) (baseStart_4085024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4085024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4085024 prefixEnd_4085024 := by exact prefixLift 4085024
  have htrace : WordTrace (prefixWord ++ tailWord_4085024) baseStart_4085024 baseEnd_4085024 := by
    simpa [prefixWord, tailWord_4085024, baseEnd_4085024] using wordTrace_append hprefix tailTrace_4085024
  have hstable : (prefixWord ++ tailWord_4085024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4085024).length < 2 ^ (prefixWord ++ tailWord_4085024).sum := by decide
  have hdescent : baseEnd_4085024 < baseStart_4085024 := by decide
  rcases family_descends (prefixWord ++ tailWord_4085024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4085034 : List Nat := [3, 1, 4, 2, 1, 3, 2, 1, 1, 5]
def baseStart_4085034 : Nat := 118140960795 + 4085034 * 2 ^ 59
def prefixEnd_4085034 : Nat := 4983230072969 + 3 ^ 40 * 4085034 * 2
def baseEnd_4085034 : Nat := 699195310652958506462759

theorem tailTrace_4085034 : CollatzResearch.WordTrace tailWord_4085034 prefixEnd_4085034 699195310652958506462759 := by
  unfold tailWord_4085034
  simp only [CollatzResearch.WordTrace]
  refine ⟨37248357570656740277025539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99328953521751307405401437 37248357570656740277025539)
  ·
    refine ⟨55872536355985110415538309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37248357570656740277025539 55872536355985110415538309)
    ·
      refine ⟨10476100566747208202913433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55872536355985110415538309 10476100566747208202913433)
      ·
        refine ⟨7857075425060406152185075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10476100566747208202913433 7857075425060406152185075)
        ·
          refine ⟨11785613137590609228277613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7857075425060406152185075 11785613137590609228277613)
          ·
            refine ⟨4419604926596478460604105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11785613137590609228277613 4419604926596478460604105)
            ·
              refine ⟨3314703694947358845453079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4419604926596478460604105 3314703694947358845453079)
              ·
                refine ⟨4972055542421038268179619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3314703694947358845453079 4972055542421038268179619)
                ·
                  refine ⟨7458083313631557402269429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4972055542421038268179619 7458083313631557402269429)
                  ·
                    refine ⟨699195310652958506462759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7458083313631557402269429 699195310652958506462759)
                    ·
                      rfl

theorem cell23_4085034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 2, 1, 1, 5].length) (baseStart_4085034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4085034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4085034 prefixEnd_4085034 := by exact prefixLift 4085034
  have htrace : WordTrace (prefixWord ++ tailWord_4085034) baseStart_4085034 baseEnd_4085034 := by
    simpa [prefixWord, tailWord_4085034, baseEnd_4085034] using wordTrace_append hprefix tailTrace_4085034
  have hstable : (prefixWord ++ tailWord_4085034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4085034).length < 2 ^ (prefixWord ++ tailWord_4085034).sum := by decide
  have hdescent : baseEnd_4085034 < baseStart_4085034 := by decide
  rcases family_descends (prefixWord ++ tailWord_4085034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4085040 : List Nat := [2, 1, 1, 1, 2, 2, 5, 3, 1, 2, 3]
def baseStart_4085040 : Nat := 118140960795 + 4085040 * 2 ^ 59
def prefixEnd_4085040 : Nat := 4983230072969 + 3 ^ 40 * 4085040 * 2
def baseEnd_4085040 : Nat := 2097589012842802495913249

theorem tailTrace_4085040 : CollatzResearch.WordTrace tailWord_4085040 prefixEnd_4085040 2097589012842802495913249 := by
  unfold tailWord_4085040
  simp only [CollatzResearch.WordTrace]
  refine ⟨74496824560302612066410287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99329099413736816088547049 74496824560302612066410287)
  ·
    refine ⟨111745236840453918099615431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74496824560302612066410287 111745236840453918099615431)
    ·
      refine ⟨167617855260680877149423147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111745236840453918099615431 167617855260680877149423147)
      ·
        refine ⟨251426782891021315724134721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167617855260680877149423147 251426782891021315724134721)
        ·
          refine ⟨188570087168265986793101041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 251426782891021315724134721 188570087168265986793101041)
          ·
            refine ⟨141427565376199490094825781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188570087168265986793101041 141427565376199490094825781)
            ·
              refine ⟨13258834254018702196389917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 141427565376199490094825781 13258834254018702196389917)
              ·
                refine ⟨4972062845257013323646219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13258834254018702196389917 4972062845257013323646219)
                ·
                  refine ⟨7458094267885519985469329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4972062845257013323646219 7458094267885519985469329)
                  ·
                    refine ⟨5593570700914139989101997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7458094267885519985469329 5593570700914139989101997)
                    ·
                      refine ⟨2097589012842802495913249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5593570700914139989101997 2097589012842802495913249)
                      ·
                        rfl

theorem cell23_4085040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 3, 1, 2, 3].length) (baseStart_4085040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4085040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4085040 prefixEnd_4085040 := by exact prefixLift 4085040
  have htrace : WordTrace (prefixWord ++ tailWord_4085040) baseStart_4085040 baseEnd_4085040 := by
    simpa [prefixWord, tailWord_4085040, baseEnd_4085040] using wordTrace_append hprefix tailTrace_4085040
  have hstable : (prefixWord ++ tailWord_4085040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4085040).length < 2 ^ (prefixWord ++ tailWord_4085040).sum := by decide
  have hdescent : baseEnd_4085040 < baseStart_4085040 := by decide
  rcases family_descends (prefixWord ++ tailWord_4085040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4085054 : List Nat := [4, 2, 1, 2, 1, 1, 4, 1, 3, 2, 2]
def baseStart_4085054 : Nat := 118140960795 + 4085054 * 2 ^ 59
def prefixEnd_4085054 : Nat := 4983230072969 + 3 ^ 40 * 4085054 * 2
def baseEnd_4085054 : Nat := 2097596201571965441138185

theorem tailTrace_4085054 : CollatzResearch.WordTrace tailWord_4085054 prefixEnd_4085054 2097596201571965441138185 := by
  unfold tailWord_4085054
  simp only [CollatzResearch.WordTrace]
  refine ⟨18624269967819313065478777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99329439828369669682553477 18624269967819313065478777)
  ·
    refine ⟨13968202475864484799109083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18624269967819313065478777 13968202475864484799109083)
    ·
      refine ⟨20952303713796727198663625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13968202475864484799109083 20952303713796727198663625)
      ·
        refine ⟨15714227785347545398997719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20952303713796727198663625 15714227785347545398997719)
        ·
          refine ⟨23571341678021318098496579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15714227785347545398997719 23571341678021318098496579)
          ·
            refine ⟨35357012517031977147744869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23571341678021318098496579 35357012517031977147744869)
            ·
              refine ⟨6629439846943495715202163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35357012517031977147744869 6629439846943495715202163)
              ·
                refine ⟨9944159770415243572803245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6629439846943495715202163 9944159770415243572803245)
                ·
                  refine ⟨3729059913905716339801217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9944159770415243572803245 3729059913905716339801217)
                  ·
                    refine ⟨2796794935429287254850913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3729059913905716339801217 2796794935429287254850913)
                    ·
                      refine ⟨2097596201571965441138185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2796794935429287254850913 2097596201571965441138185)
                      ·
                        rfl

theorem cell23_4085054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 4, 1, 3, 2, 2].length) (baseStart_4085054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4085054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4085054 prefixEnd_4085054 := by exact prefixLift 4085054
  have htrace : WordTrace (prefixWord ++ tailWord_4085054) baseStart_4085054 baseEnd_4085054 := by
    simpa [prefixWord, tailWord_4085054, baseEnd_4085054] using wordTrace_append hprefix tailTrace_4085054
  have hstable : (prefixWord ++ tailWord_4085054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4085054).length < 2 ^ (prefixWord ++ tailWord_4085054).sum := by decide
  have hdescent : baseEnd_4085054 < baseStart_4085054 := by decide
  rcases family_descends (prefixWord ++ tailWord_4085054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4085144 : List Nat := [2, 1, 2, 5, 2, 1, 1, 2, 1, 4, 2]
def baseStart_4085144 : Nat := 118140960795 + 4085144 * 2 ^ 59
def prefixEnd_4085144 : Nat := 4983230072969 + 3 ^ 40 * 4085144 * 2
def baseEnd_4085144 : Nat := 2097642414830870089012771

theorem tailTrace_4085144 : CollatzResearch.WordTrace tailWord_4085144 prefixEnd_4085144 2097642414830870089012771 := by
  unfold tailWord_4085144
  simp only [CollatzResearch.WordTrace]
  refine ⟨74498721156114224947303243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99331628208152299929737657 74498721156114224947303243)
  ·
    refine ⟨111748081734171337420954865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74498721156114224947303243 111748081734171337420954865)
    ·
      refine ⟨83811061300628503065716149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111748081734171337420954865 83811061300628503065716149)
      ·
        refine ⟨7857286996933922162410889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 83811061300628503065716149 7857286996933922162410889)
        ·
          refine ⟨5892965247700441621808167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7857286996933922162410889 5892965247700441621808167)
          ·
            refine ⟨8839447871550662432712251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5892965247700441621808167 8839447871550662432712251)
            ·
              refine ⟨13259171807325993649068377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8839447871550662432712251 13259171807325993649068377)
              ·
                refine ⟨9944378855494495236801283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13259171807325993649068377 9944378855494495236801283)
                ·
                  refine ⟨14916568283241742855201925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9944378855494495236801283 14916568283241742855201925)
                  ·
                    refine ⟨2796856553107826785350361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14916568283241742855201925 2796856553107826785350361)
                    ·
                      refine ⟨2097642414830870089012771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2796856553107826785350361 2097642414830870089012771)
                      ·
                        rfl

theorem cell23_4085144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 2, 1, 4, 2].length) (baseStart_4085144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4085144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4085144 prefixEnd_4085144 := by exact prefixLift 4085144
  have htrace : WordTrace (prefixWord ++ tailWord_4085144) baseStart_4085144 baseEnd_4085144 := by
    simpa [prefixWord, tailWord_4085144, baseEnd_4085144] using wordTrace_append hprefix tailTrace_4085144
  have hstable : (prefixWord ++ tailWord_4085144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4085144).length < 2 ^ (prefixWord ++ tailWord_4085144).sum := by decide
  have hdescent : baseEnd_4085144 < baseStart_4085144 := by decide
  rcases family_descends (prefixWord ++ tailWord_4085144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4085148 : List Nat := [2, 2, 3, 4, 1, 1, 3, 1, 1, 3, 2]
def baseStart_4085148 : Nat := 118140960795 + 4085148 * 2 ^ 59
def prefixEnd_4085148 : Nat := 4983230072969 + 3 ^ 40 * 4085148 * 2
def baseEnd_4085148 : Nat := 2097644468753488073362753

theorem tailTrace_4085148 : CollatzResearch.WordTrace tailWord_4085148 prefixEnd_4085148 2097644468753488073362753 := by
  unfold tailWord_4085148
  simp only [CollatzResearch.WordTrace]
  refine ⟨74498794102106979288876049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99331725469475972385168065 74498794102106979288876049)
  ·
    refine ⟨55874095576580234466657037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74498794102106979288876049 55874095576580234466657037)
    ·
      refine ⟨20952785841217587924996389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55874095576580234466657037 20952785841217587924996389)
      ·
        refine ⟨3928647345228297735936823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20952785841217587924996389 3928647345228297735936823)
        ·
          refine ⟨5892971017842446603905235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3928647345228297735936823 5892971017842446603905235)
          ·
            refine ⟨8839456526763669905857853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5892971017842446603905235 8839456526763669905857853)
            ·
              refine ⟨3314796197536376214696695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8839456526763669905857853 3314796197536376214696695)
              ·
                refine ⟨4972194296304564322045043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3314796197536376214696695 4972194296304564322045043)
                ·
                  refine ⟨7458291444456846483067565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4972194296304564322045043 7458291444456846483067565)
                  ·
                    refine ⟨2796859291671317431150337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7458291444456846483067565 2796859291671317431150337)
                    ·
                      refine ⟨2097644468753488073362753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2796859291671317431150337 2097644468753488073362753)
                      ·
                        rfl

theorem cell23_4085148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_4085148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4085148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4085148 prefixEnd_4085148 := by exact prefixLift 4085148
  have htrace : WordTrace (prefixWord ++ tailWord_4085148) baseStart_4085148 baseEnd_4085148 := by
    simpa [prefixWord, tailWord_4085148, baseEnd_4085148] using wordTrace_append hprefix tailTrace_4085148
  have hstable : (prefixWord ++ tailWord_4085148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4085148).length < 2 ^ (prefixWord ++ tailWord_4085148).sum := by decide
  have hdescent : baseEnd_4085148 < baseStart_4085148 := by decide
  rcases family_descends (prefixWord ++ tailWord_4085148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4085163 : List Nat := [1, 1, 1, 1, 2, 1, 1, 2, 8, 5]
def baseStart_4085163 : Nat := 118140960795 + 4085163 * 2 ^ 59
def prefixEnd_4085163 : Nat := 4983230072969 + 3 ^ 40 * 4085163 * 2
def baseEnd_4085163 : Nat := 699217390321101838225061

theorem tailTrace_4085163 : CollatzResearch.WordTrace tailWord_4085163 prefixEnd_4085163 699217390321101838225061 := by
  unfold tailWord_4085163
  simp only [CollatzResearch.WordTrace]
  refine ⟨148998135299159616139548143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99332090199439744093032095 148998135299159616139548143)
  ·
    refine ⟨223497202948739424209322215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148998135299159616139548143 223497202948739424209322215)
    ·
      refine ⟨335245804423109136313983323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223497202948739424209322215 335245804423109136313983323)
      ·
        refine ⟨502868706634663704470974985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335245804423109136313983323 502868706634663704470974985)
        ·
          refine ⟨377151529975997778353231239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 502868706634663704470974985 377151529975997778353231239)
          ·
            refine ⟨565727294963996667529846859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 377151529975997778353231239 565727294963996667529846859)
            ·
              refine ⟨848590942445995001294770289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 565727294963996667529846859 848590942445995001294770289)
              ·
                refine ⟨636443206834496250971077717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 848590942445995001294770289 636443206834496250971077717)
                ·
                  refine ⟨7458318830091752941067317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 636443206834496250971077717 7458318830091752941067317)
                  ·
                    refine ⟨699217390321101838225061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7458318830091752941067317 699217390321101838225061)
                    ·
                      rfl

theorem cell23_4085163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 8, 5].length) (baseStart_4085163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4085163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4085163 prefixEnd_4085163 := by exact prefixLift 4085163
  have htrace : WordTrace (prefixWord ++ tailWord_4085163) baseStart_4085163 baseEnd_4085163 := by
    simpa [prefixWord, tailWord_4085163, baseEnd_4085163] using wordTrace_append hprefix tailTrace_4085163
  have hstable : (prefixWord ++ tailWord_4085163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4085163).length < 2 ^ (prefixWord ++ tailWord_4085163).sum := by decide
  have hdescent : baseEnd_4085163 < baseStart_4085163 := by decide
  rcases family_descends (prefixWord ++ tailWord_4085163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4085177 : List Nat := [1, 2, 1, 4, 4, 1, 1, 1, 2, 3, 3]
def baseStart_4085177 : Nat := 118140960795 + 4085177 * 2 ^ 59
def prefixEnd_4085177 : Nat := 4983230072969 + 3 ^ 40 * 4085177 * 2
def baseEnd_4085177 : Nat := 2097659359692468459900119

theorem tailTrace_4085177 : CollatzResearch.WordTrace tailWord_4085177 prefixEnd_4085177 2097659359692468459900119 := by
  unfold tailWord_4085177
  simp only [CollatzResearch.WordTrace]
  refine ⟨148998645921108896530557785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99332430614072597687038523 148998645921108896530557785)
  ·
    refine ⟨111748984440831672397918339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148998645921108896530557785 111748984440831672397918339)
    ·
      refine ⟨167623476661247508596877509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111748984440831672397918339 167623476661247508596877509)
      ·
        refine ⟨31429401873983907861914533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 167623476661247508596877509 31429401873983907861914533)
        ·
          refine ⟨5893012851371982724108975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31429401873983907861914533 5893012851371982724108975)
          ·
            refine ⟨8839519277057974086163463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5893012851371982724108975 8839519277057974086163463)
            ·
              refine ⟨13259278915586961129245195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8839519277057974086163463 13259278915586961129245195)
              ·
                refine ⟨19888918373380441693867793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13259278915586961129245195 19888918373380441693867793)
                ·
                  refine ⟨14916688780035331270400845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19888918373380441693867793 14916688780035331270400845)
                  ·
                    refine ⟨5593758292513249226400317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14916688780035331270400845 5593758292513249226400317)
                    ·
                      refine ⟨2097659359692468459900119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5593758292513249226400317 2097659359692468459900119)
                      ·
                        rfl

theorem cell23_4085177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 1, 2, 3, 3].length) (baseStart_4085177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4085177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4085177 prefixEnd_4085177 := by exact prefixLift 4085177
  have htrace : WordTrace (prefixWord ++ tailWord_4085177) baseStart_4085177 baseEnd_4085177 := by
    simpa [prefixWord, tailWord_4085177, baseEnd_4085177] using wordTrace_append hprefix tailTrace_4085177
  have hstable : (prefixWord ++ tailWord_4085177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4085177).length < 2 ^ (prefixWord ++ tailWord_4085177).sum := by decide
  have hdescent : baseEnd_4085177 < baseStart_4085177 := by decide
  rcases family_descends (prefixWord ++ tailWord_4085177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4085217 : List Nat := [1, 2, 3, 1, 2, 3, 1, 2, 2, 4, 2]
def baseStart_4085217 : Nat := 118140960795 + 4085217 * 2 ^ 59
def prefixEnd_4085217 : Nat := 4983230072969 + 3 ^ 40 * 4085217 * 2
def baseEnd_4085217 : Nat := 2097679898918648303399935

theorem tailTrace_4085217 : CollatzResearch.WordTrace tailWord_4085217 prefixEnd_4085217 2097679898918648303399935 := by
  unfold tailWord_4085217
  simp only [CollatzResearch.WordTrace]
  refine ⟨149000104840963983362013905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99333403227309322241342603 149000104840963983362013905)
  ·
    refine ⟨111750078630722987521510429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149000104840963983362013905 111750078630722987521510429)
    ·
      refine ⟨41906279486521120320566411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111750078630722987521510429 41906279486521120320566411)
      ·
        refine ⟨62859419229781680480849617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41906279486521120320566411 62859419229781680480849617)
        ·
          refine ⟨47144564422336260360637213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62859419229781680480849617 47144564422336260360637213)
          ·
            refine ⟨17679211658376097635238955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47144564422336260360637213 17679211658376097635238955)
            ·
              refine ⟨26518817487564146452858433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17679211658376097635238955 26518817487564146452858433)
              ·
                refine ⟨19889113115673109839643825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26518817487564146452858433 19889113115673109839643825)
                ·
                  refine ⟨14916834836754832379732869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19889113115673109839643825 14916834836754832379732869)
                  ·
                    refine ⟨2796906531891531071199913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14916834836754832379732869 2796906531891531071199913)
                    ·
                      refine ⟨2097679898918648303399935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2796906531891531071199913 2097679898918648303399935)
                      ·
                        rfl

theorem cell23_4085217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 2, 2, 4, 2].length) (baseStart_4085217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4085217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4085217 prefixEnd_4085217 := by exact prefixLift 4085217
  have htrace : WordTrace (prefixWord ++ tailWord_4085217) baseStart_4085217 baseEnd_4085217 := by
    simpa [prefixWord, tailWord_4085217, baseEnd_4085217] using wordTrace_append hprefix tailTrace_4085217
  have hstable : (prefixWord ++ tailWord_4085217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4085217).length < 2 ^ (prefixWord ++ tailWord_4085217).sum := by decide
  have hdescent : baseEnd_4085217 < baseStart_4085217 := by decide
  rcases family_descends (prefixWord ++ tailWord_4085217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4085230 : List Nat := [4, 1, 2, 1, 2, 1, 1, 2, 2, 1, 6]
def baseStart_4085230 : Nat := 118140960795 + 4085230 * 2 ^ 59
def prefixEnd_4085230 : Nat := 4983230072969 + 3 ^ 40 * 4085230 * 2
def baseEnd_4085230 : Nat := 2097686574167156752537375

theorem tailTrace_4085230 : CollatzResearch.WordTrace tailWord_4085230 prefixEnd_4085230 2097686574167156752537375 := by
  unfold tailWord_4085230
  simp only [CollatzResearch.WordTrace]
  refine ⟨18625072373739610822779643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99333719326611257721491429 18625072373739610822779643)
  ·
    refine ⟨27937608560609416234169465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18625072373739610822779643 27937608560609416234169465)
    ·
      refine ⟨20953206420457062175627099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27937608560609416234169465 20953206420457062175627099)
      ·
        refine ⟨31429809630685593263440649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20953206420457062175627099 31429809630685593263440649)
        ·
          refine ⟨23572357223014194947580487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31429809630685593263440649 23572357223014194947580487)
          ·
            refine ⟨35358535834521292421370731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23572357223014194947580487 35358535834521292421370731)
            ·
              refine ⟨53037803751781938632056097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35358535834521292421370731 53037803751781938632056097)
              ·
                refine ⟨39778352813836453974042073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53037803751781938632056097 39778352813836453974042073)
                ·
                  refine ⟨29833764610377340480531555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39778352813836453974042073 29833764610377340480531555)
                  ·
                    refine ⟨44750646915566010720797333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29833764610377340480531555 44750646915566010720797333)
                    ·
                      refine ⟨2097686574167156752537375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44750646915566010720797333 2097686574167156752537375)
                      ·
                        rfl

theorem cell23_4085230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 2, 2, 1, 6].length) (baseStart_4085230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4085230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4085230 prefixEnd_4085230 := by exact prefixLift 4085230
  have htrace : WordTrace (prefixWord ++ tailWord_4085230) baseStart_4085230 baseEnd_4085230 := by
    simpa [prefixWord, tailWord_4085230, baseEnd_4085230] using wordTrace_append hprefix tailTrace_4085230
  have hstable : (prefixWord ++ tailWord_4085230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4085230).length < 2 ^ (prefixWord ++ tailWord_4085230).sum := by decide
  have hdescent : baseEnd_4085230 < baseStart_4085230 := by decide
  rcases family_descends (prefixWord ++ tailWord_4085230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4085234 : List Nat := [3, 2, 1, 4, 1, 1, 2, 1, 2, 4, 2]
def baseStart_4085234 : Nat := 118140960795 + 4085234 * 2 ^ 59
def prefixEnd_4085234 : Nat := 4983230072969 + 3 ^ 40 * 4085234 * 2
def baseEnd_4085234 : Nat := 2097688628089774736887357

theorem tailTrace_4085234 : CollatzResearch.WordTrace tailWord_4085234 prefixEnd_4085234 2097688628089774736887357 := by
  unfold tailWord_4085234
  simp only [CollatzResearch.WordTrace]
  refine ⟨37250181220475598816345689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99333816587934930176921837 37250181220475598816345689)
  ·
    refine ⟨27937635915356699112259267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37250181220475598816345689 27937635915356699112259267)
    ·
      refine ⟨41906453873035048668388901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27937635915356699112259267 41906453873035048668388901)
      ·
        refine ⟨7857460101194071625322919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41906453873035048668388901 7857460101194071625322919)
        ·
          refine ⟨11786190151791107437984379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7857460101194071625322919 11786190151791107437984379)
          ·
            refine ⟨17679285227686661156976569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11786190151791107437984379 17679285227686661156976569)
            ·
              refine ⟨13259463920764995867732427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17679285227686661156976569 13259463920764995867732427)
              ·
                refine ⟨19889195881147493801598641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13259463920764995867732427 19889195881147493801598641)
                ·
                  refine ⟨14916896910860620351198981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19889195881147493801598641 14916896910860620351198981)
                  ·
                    refine ⟨2796918170786366315849809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14916896910860620351198981 2796918170786366315849809)
                    ·
                      refine ⟨2097688628089774736887357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2796918170786366315849809 2097688628089774736887357)
                      ·
                        rfl

theorem cell23_4085234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 1, 2, 4, 2].length) (baseStart_4085234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4085234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4085234 prefixEnd_4085234 := by exact prefixLift 4085234
  have htrace : WordTrace (prefixWord ++ tailWord_4085234) baseStart_4085234 baseEnd_4085234 := by
    simpa [prefixWord, tailWord_4085234, baseEnd_4085234] using wordTrace_append hprefix tailTrace_4085234
  have hstable : (prefixWord ++ tailWord_4085234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4085234).length < 2 ^ (prefixWord ++ tailWord_4085234).sum := by decide
  have hdescent : baseEnd_4085234 < baseStart_4085234 := by decide
  rcases family_descends (prefixWord ++ tailWord_4085234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4085304 : List Nat := [2, 1, 2, 1, 4, 4, 1, 2, 1, 5]
def baseStart_4085304 : Nat := 118140960795 + 4085304 * 2 ^ 59
def prefixEnd_4085304 : Nat := 4983230072969 + 3 ^ 40 * 4085304 * 2
def baseEnd_4085304 : Nat := 699241523911863154337345

theorem tailTrace_4085304 : CollatzResearch.WordTrace tailWord_4085304 prefixEnd_4085304 699241523911863154337345 := by
  unfold tailWord_4085304
  simp only [CollatzResearch.WordTrace]
  refine ⟨74501638995824398610215483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99335518661099198146953977 74501638995824398610215483)
  ·
    refine ⟨111752458493736597915323225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74501638995824398610215483 111752458493736597915323225)
    ·
      refine ⟨83814343870302448436492419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111752458493736597915323225 83814343870302448436492419)
      ·
        refine ⟨125721515805453672654738629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83814343870302448436492419 125721515805453672654738629)
        ·
          refine ⟨23572784213522563622763493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125721515805453672654738629 23572784213522563622763493)
          ·
            refine ⟨4419897040035480679268155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23572784213522563622763493 4419897040035480679268155)
            ·
              refine ⟨6629845560053221018902233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4419897040035480679268155 6629845560053221018902233)
              ·
                refine ⟨4972384170039915764176675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6629845560053221018902233 4972384170039915764176675)
                ·
                  refine ⟨7458576255059873646265013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4972384170039915764176675 7458576255059873646265013)
                  ·
                    refine ⟨699241523911863154337345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7458576255059873646265013 699241523911863154337345)
                    ·
                      rfl

theorem cell23_4085304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 1, 2, 1, 5].length) (baseStart_4085304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4085304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4085304 prefixEnd_4085304 := by exact prefixLift 4085304
  have htrace : WordTrace (prefixWord ++ tailWord_4085304) baseStart_4085304 baseEnd_4085304 := by
    simpa [prefixWord, tailWord_4085304, baseEnd_4085304] using wordTrace_append hprefix tailTrace_4085304
  have hstable : (prefixWord ++ tailWord_4085304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4085304).length < 2 ^ (prefixWord ++ tailWord_4085304).sum := by decide
  have hdescent : baseEnd_4085304 < baseStart_4085304 := by decide
  rcases family_descends (prefixWord ++ tailWord_4085304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4085330 : List Nat := [3, 2, 2, 1, 2, 13]
def baseStart_4085330 : Nat := 118140960795 + 4085330 * 2 ^ 59
def prefixEnd_4085330 : Nat := 4983230072969 + 3 ^ 40 * 4085330 * 2
def baseEnd_4085330 : Nat := 8632666346636240169905

theorem tailTrace_4085330 : CollatzResearch.WordTrace tailWord_4085330 prefixEnd_4085330 8632666346636240169905 := by
  unfold tailWord_4085330
  simp only [CollatzResearch.WordTrace]
  refine ⟨37251056572388650915219361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99336150859703069107251629 37251056572388650915219361)
  ·
    refine ⟨27938292429291488186414521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37251056572388650915219361 27938292429291488186414521)
    ·
      refine ⟨20953719321968616139810891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27938292429291488186414521 20953719321968616139810891)
      ·
        refine ⟨31430578982952924209716337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20953719321968616139810891 31430578982952924209716337)
        ·
          refine ⟨23572934237214693157287253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31430578982952924209716337 23572934237214693157287253)
          ·
            refine ⟨8632666346636240169905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 23572934237214693157287253 8632666346636240169905)
            ·
              rfl

theorem cell23_4085330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 13].length) (baseStart_4085330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4085330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4085330 prefixEnd_4085330 := by exact prefixLift 4085330
  have htrace : WordTrace (prefixWord ++ tailWord_4085330) baseStart_4085330 baseEnd_4085330 := by
    simpa [prefixWord, tailWord_4085330, baseEnd_4085330] using wordTrace_append hprefix tailTrace_4085330
  have hstable : (prefixWord ++ tailWord_4085330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4085330).length < 2 ^ (prefixWord ++ tailWord_4085330).sum := by decide
  have hdescent : baseEnd_4085330 < baseStart_4085330 := by decide
  rcases family_descends (prefixWord ++ tailWord_4085330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4085347 : List Nat := [1, 1, 1, 5, 1, 5, 1, 8]
def baseStart_4085347 : Nat := 118140960795 + 4085347 * 2 ^ 59
def prefixEnd_4085347 : Nat := 4983230072969 + 3 ^ 40 * 4085347 * 2
def baseEnd_4085347 : Nat := 77694320422360473880531

theorem tailTrace_4085347 : CollatzResearch.WordTrace tailWord_4085347 prefixEnd_4085347 77694320422360473880531 := by
  unfold tailWord_4085347
  simp only [CollatzResearch.WordTrace]
  refine ⟨149004846330493015564246295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99336564220328677042830863 149004846330493015564246295)
  ·
    refine ⟨223507269495739523346369443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149004846330493015564246295 223507269495739523346369443)
    ·
      refine ⟨335260904243609285019554165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223507269495739523346369443 335260904243609285019554165)
      ·
        refine ⟨31430709772838370470583203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 335260904243609285019554165 31430709772838370470583203)
        ·
          refine ⟨47146064659257555705874805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31430709772838370470583203 47146064659257555705874805)
          ·
            refine ⟨4419943561805395847425763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47146064659257555705874805 4419943561805395847425763)
            ·
              refine ⟨6629915342708093771138645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4419943561805395847425763 6629915342708093771138645)
              ·
                refine ⟨77694320422360473880531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6629915342708093771138645 77694320422360473880531)
                ·
                  rfl

theorem cell23_4085347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 1, 8].length) (baseStart_4085347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4085347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4085347 prefixEnd_4085347 := by exact prefixLift 4085347
  have htrace : WordTrace (prefixWord ++ tailWord_4085347) baseStart_4085347 baseEnd_4085347 := by
    simpa [prefixWord, tailWord_4085347, baseEnd_4085347] using wordTrace_append hprefix tailTrace_4085347
  have hstable : (prefixWord ++ tailWord_4085347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4085347).length < 2 ^ (prefixWord ++ tailWord_4085347).sum := by decide
  have hdescent : baseEnd_4085347 < baseStart_4085347 := by decide
  rcases family_descends (prefixWord ++ tailWord_4085347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4085354 : List Nat := [3, 1, 3, 2, 1, 3, 2, 1, 1, 2, 4]
def baseStart_4085354 : Nat := 118140960795 + 4085354 * 2 ^ 59
def prefixEnd_4085354 : Nat := 4983230072969 + 3 ^ 40 * 4085354 * 2
def baseEnd_4085354 : Nat := 2097750245768314267386805

theorem tailTrace_4085354 : CollatzResearch.WordTrace tailWord_4085354 prefixEnd_4085354 2097750245768314267386805 := by
  unfold tailWord_4085354
  simp only [CollatzResearch.WordTrace]
  refine ⟨37251275410366913939937779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99336734427645103839834077 37251275410366913939937779)
  ·
    refine ⟨55876913115550370909906669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37251275410366913939937779 55876913115550370909906669)
    ·
      refine ⟨20953842418331389091215001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55876913115550370909906669 20953842418331389091215001)
      ·
        refine ⟨15715381813748541818411251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20953842418331389091215001 15715381813748541818411251)
        ·
          refine ⟨23573072720622812727616877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15715381813748541818411251 23573072720622812727616877)
          ·
            refine ⟨8839902270233554772856329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23573072720622812727616877 8839902270233554772856329)
            ·
              refine ⟨6629926702675166079642247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8839902270233554772856329 6629926702675166079642247)
              ·
                refine ⟨9944890054012749119463371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6629926702675166079642247 9944890054012749119463371)
                ·
                  refine ⟨14917335081019123679195057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9944890054012749119463371 14917335081019123679195057)
                  ·
                    refine ⟨11188001310764342759396293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14917335081019123679195057 11188001310764342759396293)
                    ·
                      refine ⟨2097750245768314267386805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11188001310764342759396293 2097750245768314267386805)
                      ·
                        rfl

theorem cell23_4085354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 2, 1, 1, 2, 4].length) (baseStart_4085354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4085354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4085354 prefixEnd_4085354 := by exact prefixLift 4085354
  have htrace : WordTrace (prefixWord ++ tailWord_4085354) baseStart_4085354 baseEnd_4085354 := by
    simpa [prefixWord, tailWord_4085354, baseEnd_4085354] using wordTrace_append hprefix tailTrace_4085354
  have hstable : (prefixWord ++ tailWord_4085354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4085354).length < 2 ^ (prefixWord ++ tailWord_4085354).sum := by decide
  have hdescent : baseEnd_4085354 < baseStart_4085354 := by decide
  rcases family_descends (prefixWord ++ tailWord_4085354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4085358 : List Nat := [4, 1, 2, 2, 3, 1, 1, 2, 3, 2, 2]
def baseStart_4085358 : Nat := 118140960795 + 4085358 * 2 ^ 59
def prefixEnd_4085358 : Nat := 4983230072969 + 3 ^ 40 * 4085358 * 2
def baseEnd_4085358 : Nat := 2097752299690932251736787

theorem tailTrace_4085358 : CollatzResearch.WordTrace tailWord_4085358 prefixEnd_4085358 2097752299690932251736787 := by
  unfold tailWord_4085358
  simp only [CollatzResearch.WordTrace]
  refine ⟨18625655941681645555362091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99336831688968776295264485 18625655941681645555362091)
  ·
    refine ⟨27938483912522468333043137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18625655941681645555362091 27938483912522468333043137)
    ·
      refine ⟨20953862934391851249782353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27938483912522468333043137 20953862934391851249782353)
      ·
        refine ⟨15715397200793888437336765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20953862934391851249782353 15715397200793888437336765)
        ·
          refine ⟨5893273950297708164001287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15715397200793888437336765 5893273950297708164001287)
          ·
            refine ⟨8839910925446562246001931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5893273950297708164001287 8839910925446562246001931)
            ·
              refine ⟨13259866388169843369002897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8839910925446562246001931 13259866388169843369002897)
              ·
                refine ⟨9944899791127382526752173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13259866388169843369002897 9944899791127382526752173)
                ·
                  refine ⟨3729337421672768447532065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9944899791127382526752173 3729337421672768447532065)
                  ·
                    refine ⟨2797003066254576335649049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3729337421672768447532065 2797003066254576335649049)
                    ·
                      refine ⟨2097752299690932251736787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2797003066254576335649049 2097752299690932251736787)
                      ·
                        rfl

theorem cell23_4085358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 2, 3, 2, 2].length) (baseStart_4085358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4085358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4085358 prefixEnd_4085358 := by exact prefixLift 4085358
  have htrace : WordTrace (prefixWord ++ tailWord_4085358) baseStart_4085358 baseEnd_4085358 := by
    simpa [prefixWord, tailWord_4085358, baseEnd_4085358] using wordTrace_append hprefix tailTrace_4085358
  have hstable : (prefixWord ++ tailWord_4085358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4085358).length < 2 ^ (prefixWord ++ tailWord_4085358).sum := by decide
  have hdescent : baseEnd_4085358 < baseStart_4085358 := by decide
  rcases family_descends (prefixWord ++ tailWord_4085358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4085408 : List Nat := [2, 1, 1, 4, 3, 2, 3, 1, 2, 1, 3]
def baseStart_4085408 : Nat := 118140960795 + 4085408 * 2 ^ 59
def prefixEnd_4085408 : Nat := 4983230072969 + 3 ^ 40 * 4085408 * 2
def baseEnd_4085408 : Nat := 2097777973723657056111557

theorem tailTrace_4085408 : CollatzResearch.WordTrace tailWord_4085408 prefixEnd_4085408 2097777973723657056111557 := by
  unfold tailWord_4085408
  simp only [CollatzResearch.WordTrace]
  refine ⟨74503535591636011491108439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99338047455514681988144585 74503535591636011491108439)
  ·
    refine ⟨111755303387454017236662659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74503535591636011491108439 111755303387454017236662659)
    ·
      refine ⟨167632955081181025854993989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111755303387454017236662659 167632955081181025854993989)
      ·
        refine ⟨31431179077721442347811373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 167632955081181025854993989 31431179077721442347811373)
        ·
          refine ⟨11786692154145540880429265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31431179077721442347811373 11786692154145540880429265)
          ·
            refine ⟨8840019115609155660321949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11786692154145540880429265 8840019115609155660321949)
            ·
              refine ⟨3315007168353433372620731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8840019115609155660321949 3315007168353433372620731)
              ·
                refine ⟨4972510752530150058931097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3315007168353433372620731 4972510752530150058931097)
                ·
                  refine ⟨3729383064397612544198323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4972510752530150058931097 3729383064397612544198323)
                  ·
                    refine ⟨5594074596596418816297485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3729383064397612544198323 5594074596596418816297485)
                    ·
                      refine ⟨2097777973723657056111557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5594074596596418816297485 2097777973723657056111557)
                      ·
                        rfl

theorem cell23_4085408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 3, 1, 2, 1, 3].length) (baseStart_4085408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4085408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4085408 prefixEnd_4085408 := by exact prefixLift 4085408
  have htrace : WordTrace (prefixWord ++ tailWord_4085408) baseStart_4085408 baseEnd_4085408 := by
    simpa [prefixWord, tailWord_4085408, baseEnd_4085408] using wordTrace_append hprefix tailTrace_4085408
  have hstable : (prefixWord ++ tailWord_4085408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4085408).length < 2 ^ (prefixWord ++ tailWord_4085408).sum := by decide
  have hdescent : baseEnd_4085408 < baseStart_4085408 := by decide
  rcases family_descends (prefixWord ++ tailWord_4085408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4085431 : List Nat := [1, 1, 3, 1, 5, 1, 1, 2, 4, 2, 2]
def baseStart_4085431 : Nat := 118140960795 + 4085431 * 2 ^ 59
def prefixEnd_4085431 : Nat := 4983230072969 + 3 ^ 40 * 4085431 * 2
def baseEnd_4085431 : Nat := 2097789783778710466123951

theorem tailTrace_4085431 : CollatzResearch.WordTrace tailWord_4085431 prefixEnd_4085431 2097789783778710466123951 := by
  unfold tailWord_4085431
  simp only [CollatzResearch.WordTrace]
  refine ⟨149007910062188697910304147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99338606708125798606869431 149007910062188697910304147)
  ·
    refine ⟨223511865093283046865456221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149007910062188697910304147 223511865093283046865456221)
    ·
      refine ⟨83816949409981142574546083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223511865093283046865456221 83816949409981142574546083)
      ·
        refine ⟨125725424114971713861819125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83816949409981142574546083 125725424114971713861819125)
        ·
          refine ⟨11786758510778598174545543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 125725424114971713861819125 11786758510778598174545543)
          ·
            refine ⟨17680137766167897261818315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11786758510778598174545543 17680137766167897261818315)
            ·
              refine ⟨26520206649251845892727473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17680137766167897261818315 26520206649251845892727473)
              ·
                refine ⟨19890154986938884419545605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26520206649251845892727473 19890154986938884419545605)
                ·
                  refine ⟨3729404060051040828664801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19890154986938884419545605 3729404060051040828664801)
                  ·
                    refine ⟨2797053045038280621498601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3729404060051040828664801 2797053045038280621498601)
                    ·
                      refine ⟨2097789783778710466123951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2797053045038280621498601 2097789783778710466123951)
                      ·
                        rfl

theorem cell23_4085431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 2, 4, 2, 2].length) (baseStart_4085431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4085431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4085431 prefixEnd_4085431 := by exact prefixLift 4085431
  have htrace : WordTrace (prefixWord ++ tailWord_4085431) baseStart_4085431 baseEnd_4085431 := by
    simpa [prefixWord, tailWord_4085431, baseEnd_4085431] using wordTrace_append hprefix tailTrace_4085431
  have hstable : (prefixWord ++ tailWord_4085431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4085431).length < 2 ^ (prefixWord ++ tailWord_4085431).sum := by decide
  have hdescent : baseEnd_4085431 < baseStart_4085431 := by decide
  rcases family_descends (prefixWord ++ tailWord_4085431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4085465 : List Nat := [1, 2, 1, 2, 3, 5, 2, 1, 2, 2, 2]
def baseStart_4085465 : Nat := 118140960795 + 4085465 * 2 ^ 59
def prefixEnd_4085465 : Nat := 4983230072969 + 3 ^ 40 * 4085465 * 2
def baseEnd_4085465 : Nat := 2097807242120963333098795

theorem tailTrace_4085465 : CollatzResearch.WordTrace tailWord_4085465 prefixEnd_4085465 2097807242120963333098795 := by
  unfold tailWord_4085465
  simp only [CollatzResearch.WordTrace]
  refine ⟨149009150144065521717041849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99339433429377014478027899 149009150144065521717041849)
  ·
    refine ⟨111756862608049141287781387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149009150144065521717041849 111756862608049141287781387)
    ·
      refine ⟨167635293912073711931672081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111756862608049141287781387 167635293912073711931672081)
      ·
        refine ⟨125726470434055283948754061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167635293912073711931672081 125726470434055283948754061)
        ·
          refine ⟨47147426412770731480782773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125726470434055283948754061 47147426412770731480782773)
          ·
            refine ⟨4420071226197256076323385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47147426412770731480782773 4420071226197256076323385)
            ·
              refine ⟨3315053419647942057242539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4420071226197256076323385 3315053419647942057242539)
              ·
                refine ⟨4972580129471913085863809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3315053419647942057242539 4972580129471913085863809)
                ·
                  refine ⟨3729435097103934814397857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4972580129471913085863809 3729435097103934814397857)
                  ·
                    refine ⟨2797076322827951110798393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3729435097103934814397857 2797076322827951110798393)
                    ·
                      refine ⟨2097807242120963333098795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2797076322827951110798393 2097807242120963333098795)
                      ·
                        rfl

theorem cell23_4085465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 2, 1, 2, 2, 2].length) (baseStart_4085465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4085465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4085465 prefixEnd_4085465 := by exact prefixLift 4085465
  have htrace : WordTrace (prefixWord ++ tailWord_4085465) baseStart_4085465 baseEnd_4085465 := by
    simpa [prefixWord, tailWord_4085465, baseEnd_4085465] using wordTrace_append hprefix tailTrace_4085465
  have hstable : (prefixWord ++ tailWord_4085465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4085465).length < 2 ^ (prefixWord ++ tailWord_4085465).sum := by decide
  have hdescent : baseEnd_4085465 < baseStart_4085465 := by decide
  rcases family_descends (prefixWord ++ tailWord_4085465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4085477 : List Nat := [1, 3, 1, 4, 1, 1, 1, 2, 1, 1, 7]
def baseStart_4085477 : Nat := 118140960795 + 4085477 * 2 ^ 59
def prefixEnd_4085477 : Nat := 4983230072969 + 3 ^ 40 * 4085477 * 2
def baseEnd_4085477 : Nat := 2097813403888817286148739

theorem tailTrace_4085477 : CollatzResearch.WordTrace tailWord_4085477 prefixEnd_4085477 2097813403888817286148739 := by
  unfold tailWord_4085477
  simp only [CollatzResearch.WordTrace]
  refine ⟨149009587820022047766478685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99339725213348031844319123 149009587820022047766478685)
  ·
    refine ⟨55878595432508267912429507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149009587820022047766478685 55878595432508267912429507)
    ·
      refine ⟨83817893148762401868644261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55878595432508267912429507 83817893148762401868644261)
      ·
        refine ⟨15715854965392950350370799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83817893148762401868644261 15715854965392950350370799)
        ·
          refine ⟨23573782448089425525556199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15715854965392950350370799 23573782448089425525556199)
          ·
            refine ⟨35360673672134138288334299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23573782448089425525556199 35360673672134138288334299)
            ·
              refine ⟨53041010508201207432501449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35360673672134138288334299 53041010508201207432501449)
              ·
                refine ⟨39780757881150905574376087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53041010508201207432501449 39780757881150905574376087)
                ·
                  refine ⟨59671136821726358361564131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39780757881150905574376087 59671136821726358361564131)
                  ·
                    refine ⟨89506705232589537542346197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59671136821726358361564131 89506705232589537542346197)
                    ·
                      refine ⟨2097813403888817286148739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 89506705232589537542346197 2097813403888817286148739)
                      ·
                        rfl

theorem cell23_4085477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_4085477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4085477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4085477 prefixEnd_4085477 := by exact prefixLift 4085477
  have htrace : WordTrace (prefixWord ++ tailWord_4085477) baseStart_4085477 baseEnd_4085477 := by
    simpa [prefixWord, tailWord_4085477, baseEnd_4085477] using wordTrace_append hprefix tailTrace_4085477
  have hstable : (prefixWord ++ tailWord_4085477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4085477).length < 2 ^ (prefixWord ++ tailWord_4085477).sum := by decide
  have hdescent : baseEnd_4085477 < baseStart_4085477 := by decide
  rcases family_descends (prefixWord ++ tailWord_4085477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4085494 : List Nat := [5, 1, 1, 1, 1, 3, 1, 2, 1, 2, 5]
def baseStart_4085494 : Nat := 118140960795 + 4085494 * 2 ^ 59
def prefixEnd_4085494 : Nat := 4983230072969 + 3 ^ 40 * 4085494 * 2
def baseEnd_4085494 : Nat := 2097822133059943719636161

theorem tailTrace_4085494 : CollatzResearch.WordTrace tailWord_4085494 prefixEnd_4085494 2097822133059943719636161 := by
  unfold tailWord_4085494
  simp only [CollatzResearch.WordTrace]
  refine ⟨9313137991310028729365471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 99340138573973639779898357 9313137991310028729365471)
  ·
    refine ⟨13969706986965043094048207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9313137991310028729365471 13969706986965043094048207)
    ·
      refine ⟨20954560480447564641072311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13969706986965043094048207 20954560480447564641072311)
      ·
        refine ⟨31431840720671346961608467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20954560480447564641072311 31431840720671346961608467)
        ·
          refine ⟨47147761081007020442412701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31431840720671346961608467 47147761081007020442412701)
          ·
            refine ⟨17680410405377632665904763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47147761081007020442412701 17680410405377632665904763)
            ·
              refine ⟨26520615608066448998857145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17680410405377632665904763 26520615608066448998857145)
              ·
                refine ⟨19890461706049836749142859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26520615608066448998857145 19890461706049836749142859)
                ·
                  refine ⟨29835692559074755123714289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19890461706049836749142859 29835692559074755123714289)
                  ·
                    refine ⟨22376769419306066342785717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29835692559074755123714289 22376769419306066342785717)
                    ·
                      refine ⟨2097822133059943719636161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22376769419306066342785717 2097822133059943719636161)
                      ·
                        rfl

theorem cell23_4085494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 2, 1, 2, 5].length) (baseStart_4085494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4085494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4085494 prefixEnd_4085494 := by exact prefixLift 4085494
  have htrace : WordTrace (prefixWord ++ tailWord_4085494) baseStart_4085494 baseEnd_4085494 := by
    simpa [prefixWord, tailWord_4085494, baseEnd_4085494] using wordTrace_append hprefix tailTrace_4085494
  have hstable : (prefixWord ++ tailWord_4085494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4085494).length < 2 ^ (prefixWord ++ tailWord_4085494).sum := by decide
  have hdescent : baseEnd_4085494 < baseStart_4085494 := by decide
  rcases family_descends (prefixWord ++ tailWord_4085494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4085504 : List Nat := [2, 1, 1, 2, 1, 1, 2, 3, 4, 4, 2]
def baseStart_4085504 : Nat := 118140960795 + 4085504 * 2 ^ 59
def prefixEnd_4085504 : Nat := 4983230072969 + 3 ^ 40 * 4085504 * 2
def baseEnd_4085504 : Nat := 2097827267866488680511115

theorem tailTrace_4085504 : CollatzResearch.WordTrace tailWord_4085504 prefixEnd_4085504 2097827267866488680511115 := by
  unfold tailWord_4085504
  simp only [CollatzResearch.WordTrace]
  refine ⟨74505286295462115688855783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99340381727282820918474377 74505286295462115688855783)
  ·
    refine ⟨111757929443193173533283675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74505286295462115688855783 111757929443193173533283675)
    ·
      refine ⟨167636894164789760299925513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111757929443193173533283675 167636894164789760299925513)
      ·
        refine ⟨125727670623592320224944135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167636894164789760299925513 125727670623592320224944135)
        ·
          refine ⟨188591505935388480337416203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125727670623592320224944135 188591505935388480337416203)
          ·
            refine ⟨282887258903082720506124305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188591505935388480337416203 282887258903082720506124305)
            ·
              refine ⟨212165444177312040379593229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 282887258903082720506124305 212165444177312040379593229)
              ·
                refine ⟨79562041566492015142347461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 212165444177312040379593229 79562041566492015142347461)
                ·
                  refine ⟨14917882793717252839190149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79562041566492015142347461 14917882793717252839190149)
                  ·
                    refine ⟨2797103023821984907348153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14917882793717252839190149 2797103023821984907348153)
                    ·
                      refine ⟨2097827267866488680511115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2797103023821984907348153 2097827267866488680511115)
                      ·
                        rfl

theorem cell23_4085504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 4, 4, 2].length) (baseStart_4085504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4085504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4085504 prefixEnd_4085504 := by exact prefixLift 4085504
  have htrace : WordTrace (prefixWord ++ tailWord_4085504) baseStart_4085504 baseEnd_4085504 := by
    simpa [prefixWord, tailWord_4085504, baseEnd_4085504] using wordTrace_append hprefix tailTrace_4085504
  have hstable : (prefixWord ++ tailWord_4085504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4085504).length < 2 ^ (prefixWord ++ tailWord_4085504).sum := by decide
  have hdescent : baseEnd_4085504 < baseStart_4085504 := by decide
  rcases family_descends (prefixWord ++ tailWord_4085504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4085541 : List Nat := [1, 3, 1, 2, 3, 2, 3, 1, 2, 2, 3]
def baseStart_4085541 : Nat := 118140960795 + 4085541 * 2 ^ 59
def prefixEnd_4085541 : Nat := 4983230072969 + 3 ^ 40 * 4085541 * 2
def baseEnd_4085541 : Nat := 2097846266650705035748445

theorem tailTrace_4085541 : CollatzResearch.WordTrace tailWord_4085541 prefixEnd_4085541 2097846266650705035748445 := by
  unfold tailWord_4085541
  simp only [CollatzResearch.WordTrace]
  refine ⟨149011922091790186696808477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99341281394526791131205651 149011922091790186696808477)
  ·
    refine ⟨55879470784421320011303179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149011922091790186696808477 55879470784421320011303179)
    ·
      refine ⟨83819206176631980016954769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55879470784421320011303179 83819206176631980016954769)
      ·
        refine ⟨62864404632473985012716077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83819206176631980016954769 62864404632473985012716077)
        ·
          refine ⟨23574151737177744379768529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62864404632473985012716077 23574151737177744379768529)
          ·
            refine ⟨17680613802883308284826397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23574151737177744379768529 17680613802883308284826397)
            ·
              refine ⟨6630230176081240606809899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17680613802883308284826397 6630230176081240606809899)
              ·
                refine ⟨9945345264121860910214849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6630230176081240606809899 9945345264121860910214849)
                ·
                  refine ⟨7459008948091395682661137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9945345264121860910214849 7459008948091395682661137)
                  ·
                    refine ⟨5594256711068546761995853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7459008948091395682661137 5594256711068546761995853)
                    ·
                      refine ⟨2097846266650705035748445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5594256711068546761995853 2097846266650705035748445)
                      ·
                        rfl

theorem cell23_4085541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 3, 1, 2, 2, 3].length) (baseStart_4085541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4085541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4085541 prefixEnd_4085541 := by exact prefixLift 4085541
  have htrace : WordTrace (prefixWord ++ tailWord_4085541) baseStart_4085541 baseEnd_4085541 := by
    simpa [prefixWord, tailWord_4085541, baseEnd_4085541] using wordTrace_append hprefix tailTrace_4085541
  have hstable : (prefixWord ++ tailWord_4085541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4085541).length < 2 ^ (prefixWord ++ tailWord_4085541).sum := by decide
  have hdescent : baseEnd_4085541 < baseStart_4085541 := by decide
  rcases family_descends (prefixWord ++ tailWord_4085541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4085548 : List Nat := [2, 2, 1, 1, 1, 6, 2, 3, 1, 4]
def baseStart_4085548 : Nat := 118140960795 + 4085548 * 2 ^ 59
def prefixEnd_4085548 : Nat := 4983230072969 + 3 ^ 40 * 4085548 * 2
def baseEnd_4085548 : Nat := 699283287005095502786971

theorem tailTrace_4085548 : CollatzResearch.WordTrace tailWord_4085548 prefixEnd_4085548 699283287005095502786971 := by
  unfold tailWord_4085548
  simp only [CollatzResearch.WordTrace]
  refine ⟨74506088701382413446156649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99341451601843217928208865 74506088701382413446156649)
  ·
    refine ⟨55879566526036810084617487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74506088701382413446156649 55879566526036810084617487)
    ·
      refine ⟨83819349789055215126926231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55879566526036810084617487 83819349789055215126926231)
      ·
        refine ⟨125729024683582822690389347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83819349789055215126926231 125729024683582822690389347)
        ·
          refine ⟨188593537025374234035584021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125729024683582822690389347 188593537025374234035584021)
          ·
            refine ⟨8840322048064417220418001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 188593537025374234035584021 8840322048064417220418001)
            ·
              refine ⟨6630241536048312915313501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8840322048064417220418001 6630241536048312915313501)
              ·
                refine ⟨2486340576018117343242563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6630241536048312915313501 2486340576018117343242563)
                ·
                  refine ⟨3729510864027176014863845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2486340576018117343242563 3729510864027176014863845)
                  ·
                    refine ⟨699283287005095502786971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3729510864027176014863845 699283287005095502786971)
                    ·
                      rfl

theorem cell23_4085548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 2, 3, 1, 4].length) (baseStart_4085548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4085548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4085548 prefixEnd_4085548 := by exact prefixLift 4085548
  have htrace : WordTrace (prefixWord ++ tailWord_4085548) baseStart_4085548 baseEnd_4085548 := by
    simpa [prefixWord, tailWord_4085548, baseEnd_4085548] using wordTrace_append hprefix tailTrace_4085548
  have hstable : (prefixWord ++ tailWord_4085548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4085548).length < 2 ^ (prefixWord ++ tailWord_4085548).sum := by decide
  have hdescent : baseEnd_4085548 < baseStart_4085548 := by decide
  rcases family_descends (prefixWord ++ tailWord_4085548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4085561 : List Nat := [1, 2, 1, 7, 1, 1, 1, 1, 8]
def baseStart_4085561 : Nat := 118140960795 + 4085561 * 2 ^ 59
def prefixEnd_4085561 : Nat := 4983230072969 + 3 ^ 40 * 4085561 * 2
def baseEnd_4085561 : Nat := 233095170695977217499817

theorem tailTrace_4085561 : CollatzResearch.WordTrace tailWord_4085561 prefixEnd_4085561 233095170695977217499817 := by
  unfold tailWord_4085561
  simp only [CollatzResearch.WordTrace]
  refine ⟨149012651551717730112536537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99341767701145153408357691 149012651551717730112536537)
  ·
    refine ⟨111759488663788297584402403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149012651551717730112536537 111759488663788297584402403)
    ·
      refine ⟨167639232995682446376603605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111759488663788297584402403 167639232995682446376603605)
      ·
        refine ⟨3929044523336307336951647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 167639232995682446376603605 3929044523336307336951647)
        ·
          refine ⟨5893566785004461005427471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3929044523336307336951647 5893566785004461005427471)
          ·
            refine ⟨8840350177506691508141207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5893566785004461005427471 8840350177506691508141207)
            ·
              refine ⟨13260525266260037262211811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8840350177506691508141207 13260525266260037262211811)
              ·
                refine ⟨19890787899390055893317717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13260525266260037262211811 19890787899390055893317717)
                ·
                  refine ⟨233095170695977217499817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19890787899390055893317717 233095170695977217499817)
                  ·
                    rfl

theorem cell23_4085561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 1, 8].length) (baseStart_4085561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4085561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4085561 prefixEnd_4085561 := by exact prefixLift 4085561
  have htrace : WordTrace (prefixWord ++ tailWord_4085561) baseStart_4085561 baseEnd_4085561 := by
    simpa [prefixWord, tailWord_4085561, baseEnd_4085561] using wordTrace_append hprefix tailTrace_4085561
  have hstable : (prefixWord ++ tailWord_4085561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4085561).length < 2 ^ (prefixWord ++ tailWord_4085561).sum := by decide
  have hdescent : baseEnd_4085561 < baseStart_4085561 := by decide
  rcases family_descends (prefixWord ++ tailWord_4085561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4085571 : List Nat := [1, 1, 1, 3, 1, 5, 1, 3, 3, 1, 3]
def baseStart_4085571 : Nat := 118140960795 + 4085571 * 2 ^ 59
def prefixEnd_4085571 : Nat := 4983230072969 + 3 ^ 40 * 4085571 * 2
def baseEnd_4085571 : Nat := 2097861671070339918373307

theorem tailTrace_4085571 : CollatzResearch.WordTrace tailWord_4085571 prefixEnd_4085571 2097861671070339918373307 := by
  unfold tailWord_4085571
  simp only [CollatzResearch.WordTrace]
  refine ⟨149013016281681501820400567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99342010854454334546933711 149013016281681501820400567)
  ·
    refine ⟨223519524422522252730600851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149013016281681501820400567 223519524422522252730600851)
    ·
      refine ⟨335279286633783379095901277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223519524422522252730600851 335279286633783379095901277)
      ·
        refine ⟨125729732487668767160962979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 335279286633783379095901277 125729732487668767160962979)
        ·
          refine ⟨188594598731503150741444469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125729732487668767160962979 188594598731503150741444469)
          ·
            refine ⟨17680743631078420382010419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 188594598731503150741444469 17680743631078420382010419)
            ·
              refine ⟨26521115446617630573015629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17680743631078420382010419 26521115446617630573015629)
              ·
                refine ⟨9945418292481611464880861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26521115446617630573015629 9945418292481611464880861)
                ·
                  refine ⟨3729531859680604299330323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9945418292481611464880861 3729531859680604299330323)
                  ·
                    refine ⟨5594297789520906448995485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3729531859680604299330323 5594297789520906448995485)
                    ·
                      refine ⟨2097861671070339918373307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5594297789520906448995485 2097861671070339918373307)
                      ·
                        rfl

theorem cell23_4085571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 3, 3, 1, 3].length) (baseStart_4085571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4085571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4085571 prefixEnd_4085571 := by exact prefixLift 4085571
  have htrace : WordTrace (prefixWord ++ tailWord_4085571) baseStart_4085571 baseEnd_4085571 := by
    simpa [prefixWord, tailWord_4085571, baseEnd_4085571] using wordTrace_append hprefix tailTrace_4085571
  have hstable : (prefixWord ++ tailWord_4085571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4085571).length < 2 ^ (prefixWord ++ tailWord_4085571).sum := by decide
  have hdescent : baseEnd_4085571 < baseStart_4085571 := by decide
  rcases family_descends (prefixWord ++ tailWord_4085571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4085588 : List Nat := [2, 4, 1, 1, 3, 1, 2, 2, 3, 1, 3]
def baseStart_4085588 : Nat := 118140960795 + 4085588 * 2 ^ 59
def prefixEnd_4085588 : Nat := 4983230072969 + 3 ^ 40 * 4085588 * 2
def baseEnd_4085588 : Nat := 2097870400241466351860729

theorem tailTrace_4085588 : CollatzResearch.WordTrace tailWord_4085588 prefixEnd_4085588 2097870400241466351860729 := by
  unfold tailWord_4085588
  simp only [CollatzResearch.WordTrace]
  refine ⟨74506818161309956861884709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99342424215079942482512945 74506818161309956861884709)
  ·
    refine ⟨13970028405245616911603383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74506818161309956861884709 13970028405245616911603383)
    ·
      refine ⟨20955042607868425367405075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13970028405245616911603383 20955042607868425367405075)
      ·
        refine ⟨31432563911802638051107613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20955042607868425367405075 31432563911802638051107613)
        ·
          refine ⟨11787211466925989269165355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31432563911802638051107613 11787211466925989269165355)
          ·
            refine ⟨17680817200388983903748033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11787211466925989269165355 17680817200388983903748033)
            ·
              refine ⟨13260612900291737927811025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17680817200388983903748033 13260612900291737927811025)
              ·
                refine ⟨9945459675218803445858269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13260612900291737927811025 9945459675218803445858269)
                ·
                  refine ⟨3729547378207051292196851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9945459675218803445858269 3729547378207051292196851)
                  ·
                    refine ⟨5594321067310576938295277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3729547378207051292196851 5594321067310576938295277)
                    ·
                      refine ⟨2097870400241466351860729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5594321067310576938295277 2097870400241466351860729)
                      ·
                        rfl

theorem cell23_4085588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 2, 3, 1, 3].length) (baseStart_4085588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4085588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4085588 prefixEnd_4085588 := by exact prefixLift 4085588
  have htrace : WordTrace (prefixWord ++ tailWord_4085588) baseStart_4085588 baseEnd_4085588 := by
    simpa [prefixWord, tailWord_4085588, baseEnd_4085588] using wordTrace_append hprefix tailTrace_4085588
  have hstable : (prefixWord ++ tailWord_4085588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4085588).length < 2 ^ (prefixWord ++ tailWord_4085588).sum := by decide
  have hdescent : baseEnd_4085588 < baseStart_4085588 := by decide
  rcases family_descends (prefixWord ++ tailWord_4085588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4085621 : List Nat := [1, 3, 4, 1, 1, 1, 1, 3, 4, 4]
def baseStart_4085621 : Nat := 118140960795 + 4085621 * 2 ^ 59
def prefixEnd_4085621 : Nat := 4983230072969 + 3 ^ 40 * 4085621 * 2
def baseEnd_4085621 : Nat := 699295781701021574249359

theorem tailTrace_4085621 : CollatzResearch.WordTrace tailWord_4085621 prefixEnd_4085621 699295781701021574249359 := by
  unfold tailWord_4085621
  simp only [CollatzResearch.WordTrace]
  refine ⟨149014839931500360359720717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99343226621000240239813811 149014839931500360359720717)
  ·
    refine ⟨55880564974312635134895269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 149014839931500360359720717 55880564974312635134895269)
    ·
      refine ⟨10477605932683619087792863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55880564974312635134895269 10477605932683619087792863)
      ·
        refine ⟨15716408899025428631689295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10477605932683619087792863 15716408899025428631689295)
        ·
          refine ⟨23574613348538142947533943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15716408899025428631689295 23574613348538142947533943)
          ·
            refine ⟨35361920022807214421300915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23574613348538142947533943 35361920022807214421300915)
            ·
              refine ⟨53042880034210821631951373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35361920022807214421300915 53042880034210821631951373)
              ·
                refine ⟨19891080012829058111981765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53042880034210821631951373 19891080012829058111981765)
                ·
                  refine ⟨3729577502405448395996581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19891080012829058111981765 3729577502405448395996581)
                  ·
                    refine ⟨699295781701021574249359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3729577502405448395996581 699295781701021574249359)
                    ·
                      rfl

theorem cell23_4085621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 3, 4, 4].length) (baseStart_4085621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4085621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4085621 prefixEnd_4085621 := by exact prefixLift 4085621
  have htrace : WordTrace (prefixWord ++ tailWord_4085621) baseStart_4085621 baseEnd_4085621 := by
    simpa [prefixWord, tailWord_4085621, baseEnd_4085621] using wordTrace_append hprefix tailTrace_4085621
  have hstable : (prefixWord ++ tailWord_4085621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4085621).length < 2 ^ (prefixWord ++ tailWord_4085621).sum := by decide
  have hdescent : baseEnd_4085621 < baseStart_4085621 := by decide
  rcases family_descends (prefixWord ++ tailWord_4085621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4085622 : List Nat := [5, 1, 1, 3, 2, 2, 1, 1, 3, 1, 3]
def baseStart_4085622 : Nat := 118140960795 + 4085622 * 2 ^ 59
def prefixEnd_4085622 : Nat := 4983230072969 + 3 ^ 40 * 4085622 * 2
def baseEnd_4085622 : Nat := 2097887858583719218835573

theorem tailTrace_4085622 : CollatzResearch.WordTrace tailWord_4085622 prefixEnd_4085622 2097887858583719218835573 := by
  unfold tailWord_4085622
  simp only [CollatzResearch.WordTrace]
  refine ⟨9313429775281046095656695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 99343250936331158353671413 9313429775281046095656695)
  ·
    refine ⟨13970144662921569143485043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9313429775281046095656695 13970144662921569143485043)
    ·
      refine ⟨20955216994382353715227565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13970144662921569143485043 20955216994382353715227565)
      ·
        refine ⟨7858206372893382643210337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20955216994382353715227565 7858206372893382643210337)
        ·
          refine ⟨5893654779670036982407753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7858206372893382643210337 5893654779670036982407753)
          ·
            refine ⟨4420241084752527736805815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5893654779670036982407753 4420241084752527736805815)
            ·
              refine ⟨6630361627128791605208723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4420241084752527736805815 6630361627128791605208723)
              ·
                refine ⟨9945542440693187407813085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6630361627128791605208723 9945542440693187407813085)
                ·
                  refine ⟨3729578415259945277929907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9945542440693187407813085 3729578415259945277929907)
                  ·
                    refine ⟨5594367622889917916894861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3729578415259945277929907 5594367622889917916894861)
                    ·
                      refine ⟨2097887858583719218835573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5594367622889917916894861 2097887858583719218835573)
                      ·
                        rfl

theorem cell23_4085622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_4085622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4085622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4085622 prefixEnd_4085622 := by exact prefixLift 4085622
  have htrace : WordTrace (prefixWord ++ tailWord_4085622) baseStart_4085622 baseEnd_4085622 := by
    simpa [prefixWord, tailWord_4085622, baseEnd_4085622] using wordTrace_append hprefix tailTrace_4085622
  have hstable : (prefixWord ++ tailWord_4085622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4085622).length < 2 ^ (prefixWord ++ tailWord_4085622).sum := by decide
  have hdescent : baseEnd_4085622 < baseStart_4085622 := by decide
  rcases family_descends (prefixWord ++ tailWord_4085622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4085661 : List Nat := [1, 4, 2, 1, 2, 2, 1, 1, 3, 3, 3]
def baseStart_4085661 : Nat := 118140960795 + 4085661 * 2 ^ 59
def prefixEnd_4085661 : Nat := 4983230072969 + 3 ^ 40 * 4085661 * 2
def baseEnd_4085661 : Nat := 2097907884329244566247893

theorem tailTrace_4085661 : CollatzResearch.WordTrace tailWord_4085661 prefixEnd_4085661 2097907884329244566247893 := by
  unfold tailWord_4085661
  simp only [CollatzResearch.WordTrace]
  refine ⟨149016298851355447191176837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99344199234236964794117891 149016298851355447191176837)
  ·
    refine ⟨27940556034629146348345657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149016298851355447191176837 27940556034629146348345657)
    ·
      refine ⟨20955417025971859761259243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27940556034629146348345657 20955417025971859761259243)
      ·
        refine ⟨31433125538957789641888865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20955417025971859761259243 31433125538957789641888865)
        ·
          refine ⟨23574844154218342231416649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31433125538957789641888865 23574844154218342231416649)
          ·
            refine ⟨17681133115663756673562487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23574844154218342231416649 17681133115663756673562487)
            ·
              refine ⟨26521699673495635010343731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17681133115663756673562487 26521699673495635010343731)
              ·
                refine ⟨39782549510243452515515597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26521699673495635010343731 39782549510243452515515597)
                ·
                  refine ⟨14918456066341294693318349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39782549510243452515515597 14918456066341294693318349)
                  ·
                    refine ⟨5594421024877985509994381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14918456066341294693318349 5594421024877985509994381)
                    ·
                      refine ⟨2097907884329244566247893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5594421024877985509994381 2097907884329244566247893)
                      ·
                        rfl

theorem cell23_4085661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 1, 3, 3, 3].length) (baseStart_4085661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4085661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4085661 prefixEnd_4085661 := by exact prefixLift 4085661
  have htrace : WordTrace (prefixWord ++ tailWord_4085661) baseStart_4085661 baseEnd_4085661 := by
    simpa [prefixWord, tailWord_4085661, baseEnd_4085661] using wordTrace_append hprefix tailTrace_4085661
  have hstable : (prefixWord ++ tailWord_4085661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4085661).length < 2 ^ (prefixWord ++ tailWord_4085661).sum := by decide
  have hdescent : baseEnd_4085661 < baseStart_4085661 := by decide
  rcases family_descends (prefixWord ++ tailWord_4085661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4085665 : List Nat := [1, 2, 3, 4, 3, 1, 1, 1, 1, 1, 5]
def baseStart_4085665 : Nat := 118140960795 + 4085665 * 2 ^ 59
def prefixEnd_4085665 : Nat := 4983230072969 + 3 ^ 40 * 4085665 * 2
def baseEnd_4085665 : Nat := 2097909938251862550597875

theorem tailTrace_4085665 : CollatzResearch.WordTrace tailWord_4085665 prefixEnd_4085665 2097909938251862550597875 := by
  unfold tailWord_4085665
  simp only [CollatzResearch.WordTrace]
  refine ⟨149016444743340955874322449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99344296495560637249548299 149016444743340955874322449)
  ·
    refine ⟨111762333557505716905741837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149016444743340955874322449 111762333557505716905741837)
    ·
      refine ⟨41910875084064643839653189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111762333557505716905741837 41910875084064643839653189)
      ·
        refine ⟨7858289078262120719934973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41910875084064643839653189 7858289078262120719934973)
        ·
          refine ⟨2946858404348295269975615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7858289078262120719934973 2946858404348295269975615)
          ·
            refine ⟨4420287606522442904963423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2946858404348295269975615 4420287606522442904963423)
            ·
              refine ⟨6630431409783664357445135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4420287606522442904963423 6630431409783664357445135)
              ·
                refine ⟨9945647114675496536167703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6630431409783664357445135 9945647114675496536167703)
                ·
                  refine ⟨14918470672013244804251555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9945647114675496536167703 14918470672013244804251555)
                  ·
                    refine ⟨22377706008019867206377333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14918470672013244804251555 22377706008019867206377333)
                    ·
                      refine ⟨2097909938251862550597875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22377706008019867206377333 2097909938251862550597875)
                      ·
                        rfl

theorem cell23_4085665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 1, 1, 1, 1, 5].length) (baseStart_4085665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4085665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4085665 prefixEnd_4085665 := by exact prefixLift 4085665
  have htrace : WordTrace (prefixWord ++ tailWord_4085665) baseStart_4085665 baseEnd_4085665 := by
    simpa [prefixWord, tailWord_4085665, baseEnd_4085665] using wordTrace_append hprefix tailTrace_4085665
  have hstable : (prefixWord ++ tailWord_4085665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4085665).length < 2 ^ (prefixWord ++ tailWord_4085665).sum := by decide
  have hdescent : baseEnd_4085665 < baseStart_4085665 := by decide
  rcases family_descends (prefixWord ++ tailWord_4085665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4085672 : List Nat := [2, 1, 6, 2, 1, 1, 2, 2, 2, 4]
def baseStart_4085672 : Nat := 118140960795 + 4085672 * 2 ^ 59
def prefixEnd_4085672 : Nat := 4983230072969 + 3 ^ 40 * 4085672 * 2
def baseEnd_4085672 : Nat := 699304510872148007736781

theorem tailTrace_4085672 : CollatzResearch.WordTrace tailWord_4085672 prefixEnd_4085672 699304510872148007736781 := by
  unfold tailWord_4085672
  simp only [CollatzResearch.WordTrace]
  refine ⟨74508350027157798034913635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99344466702877064046551513 74508350027157798034913635)
  ·
    refine ⟨111762525040736697052370453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74508350027157798034913635 111762525040736697052370453)
    ·
      refine ⟨5238868361284532674329865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 111762525040736697052370453 5238868361284532674329865)
      ·
        refine ⟨3929151270963399505747399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5238868361284532674329865 3929151270963399505747399)
        ·
          refine ⟨5893726906445099258621099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3929151270963399505747399 5893726906445099258621099)
          ·
            refine ⟨8840590359667648887931649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5893726906445099258621099 8840590359667648887931649)
            ·
              refine ⟨6630442769750736665948737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8840590359667648887931649 6630442769750736665948737)
              ·
                refine ⟨4972832077313052499461553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6630442769750736665948737 4972832077313052499461553)
                ·
                  refine ⟨3729624057984789374596165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4972832077313052499461553 3729624057984789374596165)
                  ·
                    refine ⟨699304510872148007736781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3729624057984789374596165 699304510872148007736781)
                    ·
                      rfl

theorem cell23_4085672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_4085672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4085672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4085672 prefixEnd_4085672 := by exact prefixLift 4085672
  have htrace : WordTrace (prefixWord ++ tailWord_4085672) baseStart_4085672 baseEnd_4085672 := by
    simpa [prefixWord, tailWord_4085672, baseEnd_4085672] using wordTrace_append hprefix tailTrace_4085672
  have hstable : (prefixWord ++ tailWord_4085672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4085672).length < 2 ^ (prefixWord ++ tailWord_4085672).sum := by decide
  have hdescent : baseEnd_4085672 < baseStart_4085672 := by decide
  rcases family_descends (prefixWord ++ tailWord_4085672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4085731 : List Nat := [1, 1, 1, 6, 1, 2, 1, 2, 2, 2, 4]
def baseStart_4085731 : Nat := 118140960795 + 4085731 * 2 ^ 59
def prefixEnd_4085731 : Nat := 4983230072969 + 3 ^ 40 * 4085731 * 2
def baseEnd_4085731 : Nat := 2097943827975059292372571

theorem tailTrace_4085731 : CollatzResearch.WordTrace tailWord_4085731 prefixEnd_4085731 2097943827975059292372571 := by
  unfold tailWord_4085731
  simp only [CollatzResearch.WordTrace]
  refine ⟨149018851961101849146225047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99345901307401232764150031 149018851961101849146225047)
  ·
    refine ⟨223528277941652773719337571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149018851961101849146225047 223528277941652773719337571)
    ·
      refine ⟨335292416912479160579006357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223528277941652773719337571 335292416912479160579006357)
      ·
        refine ⟨15716832042772460652140923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 335292416912479160579006357 15716832042772460652140923)
        ·
          refine ⟨23575248064158690978211385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15716832042772460652140923 23575248064158690978211385)
          ·
            refine ⟨17681436048119018233658539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23575248064158690978211385 17681436048119018233658539)
            ·
              refine ⟨26522154072178527350487809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17681436048119018233658539 26522154072178527350487809)
              ·
                refine ⟨19891615554133895512865857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26522154072178527350487809 19891615554133895512865857)
                ·
                  refine ⟨14918711665600421634649393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19891615554133895512865857 14918711665600421634649393)
                  ·
                    refine ⟨11189033749200316225987045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14918711665600421634649393 11189033749200316225987045)
                    ·
                      refine ⟨2097943827975059292372571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11189033749200316225987045 2097943827975059292372571)
                      ·
                        rfl

theorem cell23_4085731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_4085731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4085731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4085731 prefixEnd_4085731 := by exact prefixLift 4085731
  have htrace : WordTrace (prefixWord ++ tailWord_4085731) baseStart_4085731 baseEnd_4085731 := by
    simpa [prefixWord, tailWord_4085731, baseEnd_4085731] using wordTrace_append hprefix tailTrace_4085731
  have hstable : (prefixWord ++ tailWord_4085731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4085731).length < 2 ^ (prefixWord ++ tailWord_4085731).sum := by decide
  have hdescent : baseEnd_4085731 < baseStart_4085731 := by decide
  rcases family_descends (prefixWord ++ tailWord_4085731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4085758 : List Nat := [4, 2, 2, 2, 1, 1, 2, 2, 7]
def baseStart_4085758 : Nat := 118140960795 + 4085758 * 2 ^ 59
def prefixEnd_4085758 : Nat := 4983230072969 + 3 ^ 40 * 4085758 * 2
def baseEnd_4085758 : Nat := 233106410216970076303883

theorem tailTrace_4085758 : CollatzResearch.WordTrace tailWord_4085758 prefixEnd_4085758 233106410216970076303883 := by
  unfold tailWord_4085758
  simp only [CollatzResearch.WordTrace]
  refine ⟨18627479591500504094682241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99346557821336021838305285 18627479591500504094682241)
  ·
    refine ⟨13970609693625378071011681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18627479591500504094682241 13970609693625378071011681)
    ·
      refine ⟨10477957270219033553258761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13970609693625378071011681 10477957270219033553258761)
      ·
        refine ⟨7858467952664275164944071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10477957270219033553258761 7858467952664275164944071)
        ·
          refine ⟨11787701928996412747416107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7858467952664275164944071 11787701928996412747416107)
          ·
            refine ⟨17681552893494619121124161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11787701928996412747416107 17681552893494619121124161)
            ·
              refine ⟨13261164670120964340843121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17681552893494619121124161 13261164670120964340843121)
              ·
                refine ⟨9945873502590723255632341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13261164670120964340843121 9945873502590723255632341)
                ·
                  refine ⟨233106410216970076303883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9945873502590723255632341 233106410216970076303883)
                  ·
                    rfl

theorem cell23_4085758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 2, 7].length) (baseStart_4085758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4085758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4085758 prefixEnd_4085758 := by exact prefixLift 4085758
  have htrace : WordTrace (prefixWord ++ tailWord_4085758) baseStart_4085758 baseEnd_4085758 := by
    simpa [prefixWord, tailWord_4085758, baseEnd_4085758] using wordTrace_append hprefix tailTrace_4085758
  have hstable : (prefixWord ++ tailWord_4085758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4085758).length < 2 ^ (prefixWord ++ tailWord_4085758).sum := by decide
  have hdescent : baseEnd_4085758 < baseStart_4085758 := by decide
  rcases family_descends (prefixWord ++ tailWord_4085758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4085771 : List Nat := [1, 1, 1, 1, 6, 1, 2, 3, 2, 5]
def baseStart_4085771 : Nat := 118140960795 + 4085771 * 2 ^ 59
def prefixEnd_4085771 : Nat := 4983230072969 + 3 ^ 40 * 4085771 * 2
def baseEnd_4085771 : Nat := 699321455733746378624129

theorem tailTrace_4085771 : CollatzResearch.WordTrace tailWord_4085771 prefixEnd_4085771 699321455733746378624129 := by
  unfold tailWord_4085771
  simp only [CollatzResearch.WordTrace]
  refine ⟨149020310880956935977681167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99346873920637957318454111 149020310880956935977681167)
  ·
    refine ⟨223530466321435403966521751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149020310880956935977681167 223530466321435403966521751)
    ·
      refine ⟨335295699482153105949782627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223530466321435403966521751 335295699482153105949782627)
      ·
        refine ⟨502943549223229658924673941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335295699482153105949782627 502943549223229658924673941)
        ·
          refine ⟨23575478869838890262094091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 502943549223229658924673941 23575478869838890262094091)
          ·
            refine ⟨35363218304758335393141137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23575478869838890262094091 35363218304758335393141137)
            ·
              refine ⟨26522413728568751544855853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35363218304758335393141137 26522413728568751544855853)
              ·
                refine ⟨9945905148213281829320945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26522413728568751544855853 9945905148213281829320945)
                ·
                  refine ⟨7459428861159961371990709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9945905148213281829320945 7459428861159961371990709)
                  ·
                    refine ⟨699321455733746378624129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7459428861159961371990709 699321455733746378624129)
                    ·
                      rfl

theorem cell23_4085771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 3, 2, 5].length) (baseStart_4085771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4085771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4085771 prefixEnd_4085771 := by exact prefixLift 4085771
  have htrace : WordTrace (prefixWord ++ tailWord_4085771) baseStart_4085771 baseEnd_4085771 := by
    simpa [prefixWord, tailWord_4085771, baseEnd_4085771] using wordTrace_append hprefix tailTrace_4085771
  have hstable : (prefixWord ++ tailWord_4085771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4085771).length < 2 ^ (prefixWord ++ tailWord_4085771).sum := by decide
  have hdescent : baseEnd_4085771 < baseStart_4085771 := by decide
  rcases family_descends (prefixWord ++ tailWord_4085771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4085788 : List Nat := [2, 2, 3, 1, 3, 2, 1, 2, 2, 5]
def baseStart_4085788 : Nat := 118140960795 + 4085788 * 2 ^ 59
def prefixEnd_4085788 : Nat := 4983230072969 + 3 ^ 40 * 4085788 * 2
def baseEnd_4085788 : Nat := 699324365457455189786603

theorem tailTrace_4085788 : CollatzResearch.WordTrace tailWord_4085788 prefixEnd_4085788 699324365457455189786603 := by
  unfold tailWord_4085788
  simp only [CollatzResearch.WordTrace]
  refine ⟨74510465460947673940525009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99347287281263565254033345 74510465460947673940525009)
  ·
    refine ⟨55882849095710755455393757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74510465460947673940525009 55882849095710755455393757)
    ·
      refine ⟨20956068410891533295772659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55882849095710755455393757 20956068410891533295772659)
      ·
        refine ⟨31434102616337299943658989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20956068410891533295772659 31434102616337299943658989)
        ·
          refine ⟨11787788481126487478872121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31434102616337299943658989 11787788481126487478872121)
          ·
            refine ⟨8840841360844865609154091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11787788481126487478872121 8840841360844865609154091)
            ·
              refine ⟨13261262041267298413731137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8840841360844865609154091 13261262041267298413731137)
              ·
                refine ⟨9945946530950473810298353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13261262041267298413731137 9945946530950473810298353)
                ·
                  refine ⟨7459459898212855357723765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9945946530950473810298353 7459459898212855357723765)
                  ·
                    refine ⟨699324365457455189786603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7459459898212855357723765 699324365457455189786603)
                    ·
                      rfl

theorem cell23_4085788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 2, 2, 5].length) (baseStart_4085788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4085788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4085788 prefixEnd_4085788 := by exact prefixLift 4085788
  have htrace : WordTrace (prefixWord ++ tailWord_4085788) baseStart_4085788 baseEnd_4085788 := by
    simpa [prefixWord, tailWord_4085788, baseEnd_4085788] using wordTrace_append hprefix tailTrace_4085788
  have hstable : (prefixWord ++ tailWord_4085788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4085788).length < 2 ^ (prefixWord ++ tailWord_4085788).sum := by decide
  have hdescent : baseEnd_4085788 < baseStart_4085788 := by decide
  rcases family_descends (prefixWord ++ tailWord_4085788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4085811 : List Nat := [1, 1, 1, 2, 4, 1, 2, 1, 3, 4, 3]
def baseStart_4085811 : Nat := 118140960795 + 4085811 * 2 ^ 59
def prefixEnd_4085811 : Nat := 4983230072969 + 3 ^ 40 * 4085811 * 2
def baseEnd_4085811 : Nat := 2097984906427418979372203

theorem tailTrace_4085811 : CollatzResearch.WordTrace tailWord_4085811 prefixEnd_4085811 2097984906427418979372203 := by
  unfold tailWord_4085811
  simp only [CollatzResearch.WordTrace]
  refine ⟨149021769800812022809137287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99347846533874681872758191 149021769800812022809137287)
  ·
    refine ⟨223532654701218034213705931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149021769800812022809137287 223532654701218034213705931)
    ·
      refine ⟨335298982051827051320558897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223532654701218034213705931 335298982051827051320558897)
      ·
        refine ⟨251474236538870288490419173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 335298982051827051320558897 251474236538870288490419173)
        ·
          refine ⟨47151419351038179091953595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 251474236538870288490419173 47151419351038179091953595)
          ·
            refine ⟨70727129026557268637930393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47151419351038179091953595 70727129026557268637930393)
            ·
              refine ⟨53045346769917951478447795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70727129026557268637930393 53045346769917951478447795)
              ·
                refine ⟨79568020154876927217671693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53045346769917951478447795 79568020154876927217671693)
                ·
                  refine ⟨29838007558078847706626885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79568020154876927217671693 29838007558078847706626885)
                  ·
                    refine ⟨5594626417139783944992541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29838007558078847706626885 5594626417139783944992541)
                    ·
                      refine ⟨2097984906427418979372203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5594626417139783944992541 2097984906427418979372203)
                      ·
                        rfl

theorem cell23_4085811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 1, 3, 4, 3].length) (baseStart_4085811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4085811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4085811 prefixEnd_4085811 := by exact prefixLift 4085811
  have htrace : WordTrace (prefixWord ++ tailWord_4085811) baseStart_4085811 baseEnd_4085811 := by
    simpa [prefixWord, tailWord_4085811, baseEnd_4085811] using wordTrace_append hprefix tailTrace_4085811
  have hstable : (prefixWord ++ tailWord_4085811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4085811).length < 2 ^ (prefixWord ++ tailWord_4085811).sum := by decide
  have hdescent : baseEnd_4085811 < baseStart_4085811 := by decide
  rcases family_descends (prefixWord ++ tailWord_4085811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4085825 : List Nat := [1, 2, 5, 1, 2, 2, 2, 1, 2, 1, 4]
def baseStart_4085825 : Nat := 118140960795 + 4085825 * 2 ^ 59
def prefixEnd_4085825 : Nat := 4983230072969 + 3 ^ 40 * 4085825 * 2
def baseEnd_4085825 : Nat := 2097992095156581924597139

theorem tailTrace_4085825 : CollatzResearch.WordTrace tailWord_4085825 prefixEnd_4085825 2097992095156581924597139 := by
  unfold tailWord_4085825
  simp only [CollatzResearch.WordTrace]
  refine ⟨149022280422761303200146929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99348186948507535466764619 149022280422761303200146929)
  ·
    refine ⟨111766710317070977400110197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149022280422761303200146929 111766710317070977400110197)
    ·
      refine ⟨10478129092225404131260331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 111766710317070977400110197 10478129092225404131260331)
      ·
        refine ⟨15717193638338106196890497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10478129092225404131260331 15717193638338106196890497)
        ·
          refine ⟨11787895228753579647667873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15717193638338106196890497 11787895228753579647667873)
          ·
            refine ⟨8840921421565184735750905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11787895228753579647667873 8840921421565184735750905)
            ·
              refine ⟨6630691066173888551813179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8840921421565184735750905 6630691066173888551813179)
              ·
                refine ⟨9946036599260832827719769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6630691066173888551813179 9946036599260832827719769)
                ·
                  refine ⟨7459527449445624620789827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9946036599260832827719769 7459527449445624620789827)
                  ·
                    refine ⟨11189291174168436931184741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7459527449445624620789827 11189291174168436931184741)
                    ·
                      refine ⟨2097992095156581924597139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11189291174168436931184741 2097992095156581924597139)
                      ·
                        rfl

theorem cell23_4085825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 2, 1, 2, 1, 4].length) (baseStart_4085825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4085825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4085825 prefixEnd_4085825 := by exact prefixLift 4085825
  have htrace : WordTrace (prefixWord ++ tailWord_4085825) baseStart_4085825 baseEnd_4085825 := by
    simpa [prefixWord, tailWord_4085825, baseEnd_4085825] using wordTrace_append hprefix tailTrace_4085825
  have hstable : (prefixWord ++ tailWord_4085825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4085825).length < 2 ^ (prefixWord ++ tailWord_4085825).sum := by decide
  have hdescent : baseEnd_4085825 < baseStart_4085825 := by decide
  rcases family_descends (prefixWord ++ tailWord_4085825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4085848 : List Nat := [2, 1, 2, 2, 1, 5, 2, 2, 6]
def baseStart_4085848 : Nat := 118140960795 + 4085848 * 2 ^ 59
def prefixEnd_4085848 : Nat := 4983230072969 + 3 ^ 40 * 4085848 * 2
def baseEnd_4085848 : Nat := 233111545023515037178837

theorem tailTrace_4085848 : CollatzResearch.WordTrace tailWord_4085848 prefixEnd_4085848 233111545023515037178837 := by
  unfold tailWord_4085848
  simp only [CollatzResearch.WordTrace]
  refine ⟨74511559650838989064117099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99348746201118652085489465 74511559650838989064117099)
  ·
    refine ⟨111767339476258483596175649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74511559650838989064117099 111767339476258483596175649)
    ·
      refine ⟨83825504607193862697131737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111767339476258483596175649 83825504607193862697131737)
      ·
        refine ⟨62869128455395397022848803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83825504607193862697131737 62869128455395397022848803)
        ·
          refine ⟨94303692683093095534273205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62869128455395397022848803 94303692683093095534273205)
          ·
            refine ⟨8840971189039977706338113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 94303692683093095534273205 8840971189039977706338113)
            ·
              refine ⟨6630728391779983279753585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8840971189039977706338113 6630728391779983279753585)
              ·
                refine ⟨4973046293834987459815189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6630728391779983279753585 4973046293834987459815189)
                ·
                  refine ⟨233111545023515037178837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4973046293834987459815189 233111545023515037178837)
                  ·
                    rfl

theorem cell23_4085848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 2, 2, 6].length) (baseStart_4085848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4085848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4085848 prefixEnd_4085848 := by exact prefixLift 4085848
  have htrace : WordTrace (prefixWord ++ tailWord_4085848) baseStart_4085848 baseEnd_4085848 := by
    simpa [prefixWord, tailWord_4085848, baseEnd_4085848] using wordTrace_append hprefix tailTrace_4085848
  have hstable : (prefixWord ++ tailWord_4085848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4085848).length < 2 ^ (prefixWord ++ tailWord_4085848).sum := by decide
  have hdescent : baseEnd_4085848 < baseStart_4085848 := by decide
  rcases family_descends (prefixWord ++ tailWord_4085848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4085852 : List Nat := [2, 2, 4, 1, 1, 3, 1, 4, 1, 4]
def baseStart_4085852 : Nat := 118140960795 + 4085852 * 2 ^ 59
def prefixEnd_4085852 : Nat := 4983230072969 + 3 ^ 40 * 4085852 * 2
def baseEnd_4085852 : Nat := 699335319711417772986505

theorem tailTrace_4085852 : CollatzResearch.WordTrace tailWord_4085852 prefixEnd_4085852 699335319711417772986505 := by
  unfold tailWord_4085852
  simp only [CollatzResearch.WordTrace]
  refine ⟨74511632596831743405689905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99348843462442324540919873 74511632596831743405689905)
  ·
    refine ⟨55883724447623807554267429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74511632596831743405689905 55883724447623807554267429)
    ·
      refine ⟨10478198333929463916425143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55883724447623807554267429 10478198333929463916425143)
      ·
        refine ⟨15717297500894195874637715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10478198333929463916425143 15717297500894195874637715)
        ·
          refine ⟨23575946251341293811956573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15717297500894195874637715 23575946251341293811956573)
          ·
            refine ⟨8840979844252985179483715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23575946251341293811956573 8840979844252985179483715)
            ·
              refine ⟨13261469766379477769225573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8840979844252985179483715 13261469766379477769225573)
              ·
                refine ⟨2486525581196152081729795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13261469766379477769225573 2486525581196152081729795)
                ·
                  refine ⟨3729788371794228122594693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2486525581196152081729795 3729788371794228122594693)
                  ·
                    refine ⟨699335319711417772986505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3729788371794228122594693 699335319711417772986505)
                    ·
                      rfl

theorem cell23_4085852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 4, 1, 4].length) (baseStart_4085852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4085852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4085852 prefixEnd_4085852 := by exact prefixLift 4085852
  have htrace : WordTrace (prefixWord ++ tailWord_4085852) baseStart_4085852 baseEnd_4085852 := by
    simpa [prefixWord, tailWord_4085852, baseEnd_4085852] using wordTrace_append hprefix tailTrace_4085852
  have hstable : (prefixWord ++ tailWord_4085852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4085852).length < 2 ^ (prefixWord ++ tailWord_4085852).sum := by decide
  have hdescent : baseEnd_4085852 < baseStart_4085852 := by decide
  rcases family_descends (prefixWord ++ tailWord_4085852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4085885 : List Nat := [1, 4, 1, 1, 3, 3, 1, 1, 1, 5, 2]
def baseStart_4085885 : Nat := 118140960795 + 4085885 * 2 ^ 59
def prefixEnd_4085885 : Nat := 4983230072969 + 3 ^ 40 * 4085885 * 2
def baseEnd_4085885 : Nat := 2098022903995851689846863

theorem tailTrace_4085885 : CollatzResearch.WordTrace tailWord_4085885 prefixEnd_4085885 2098022903995851689846863 := by
  unfold tailWord_4085885
  simp only [CollatzResearch.WordTrace]
  refine ⟨149024468802543933447331109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99349645868362622298220739 149024468802543933447331109)
  ·
    refine ⟨27942087900476987521374583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149024468802543933447331109 27942087900476987521374583)
    ·
      refine ⟨41913131850715481282061875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27942087900476987521374583 41913131850715481282061875)
      ·
        refine ⟨62869697776073221923092813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41913131850715481282061875 62869697776073221923092813)
        ·
          refine ⟨23576136666027458221159805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62869697776073221923092813 23576136666027458221159805)
          ·
            refine ⟨8841051249760296832934927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23576136666027458221159805 8841051249760296832934927)
            ·
              refine ⟨13261576874640445249402391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8841051249760296832934927 13261576874640445249402391)
              ·
                refine ⟨19892365311960667874103587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13261576874640445249402391 19892365311960667874103587)
                ·
                  refine ⟨29838547967941001811155381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19892365311960667874103587 29838547967941001811155381)
                  ·
                    refine ⟨2797363871994468919795817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29838547967941001811155381 2797363871994468919795817)
                    ·
                      refine ⟨2098022903995851689846863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2797363871994468919795817 2098022903995851689846863)
                      ·
                        rfl

theorem cell23_4085885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 1, 1, 5, 2].length) (baseStart_4085885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4085885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4085885 prefixEnd_4085885 := by exact prefixLift 4085885
  have htrace : WordTrace (prefixWord ++ tailWord_4085885) baseStart_4085885 baseEnd_4085885 := by
    simpa [prefixWord, tailWord_4085885, baseEnd_4085885] using wordTrace_append hprefix tailTrace_4085885
  have hstable : (prefixWord ++ tailWord_4085885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4085885).length < 2 ^ (prefixWord ++ tailWord_4085885).sum := by decide
  have hdescent : baseEnd_4085885 < baseStart_4085885 := by decide
  rcases family_descends (prefixWord ++ tailWord_4085885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4085895 : List Nat := [1, 1, 4, 2, 1, 1, 6, 1, 1, 5]
def baseStart_4085895 : Nat := 118140960795 + 4085895 * 2 ^ 59
def prefixEnd_4085895 : Nat := 4983230072969 + 3 ^ 40 * 4085895 * 2
def baseEnd_4085895 : Nat := 699342679600798883573939

theorem tailTrace_4085895 : CollatzResearch.WordTrace tailWord_4085895 prefixEnd_4085895 699342679600798883573939 := by
  unfold tailWord_4085895
  simp only [CollatzResearch.WordTrace]
  refine ⟨149024833532507705155195139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99349889021671803436796759 149024833532507705155195139)
  ·
    refine ⟨223537250298761557732792709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149024833532507705155195139 223537250298761557732792709)
    ·
      refine ⟨41913234431017792074898633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 223537250298761557732792709 41913234431017792074898633)
      ·
        refine ⟨31434925823263344056173975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41913234431017792074898633 31434925823263344056173975)
        ·
          refine ⟨47152388734895016084260963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31434925823263344056173975 47152388734895016084260963)
          ·
            refine ⟨70728583102342524126391445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47152388734895016084260963 70728583102342524126391445)
            ·
              refine ⟨3315402332922305818424599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 70728583102342524126391445 3315402332922305818424599)
              ·
                refine ⟨4973103499383458727636899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3315402332922305818424599 4973103499383458727636899)
                ·
                  refine ⟨7459655249075188091455349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4973103499383458727636899 7459655249075188091455349)
                  ·
                    refine ⟨699342679600798883573939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7459655249075188091455349 699342679600798883573939)
                    ·
                      rfl

theorem cell23_4085895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 6, 1, 1, 5].length) (baseStart_4085895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4085895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4085895 prefixEnd_4085895 := by exact prefixLift 4085895
  have htrace : WordTrace (prefixWord ++ tailWord_4085895) baseStart_4085895 baseEnd_4085895 := by
    simpa [prefixWord, tailWord_4085895, baseEnd_4085895] using wordTrace_append hprefix tailTrace_4085895
  have hstable : (prefixWord ++ tailWord_4085895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4085895).length < 2 ^ (prefixWord ++ tailWord_4085895).sum := by decide
  have hdescent : baseEnd_4085895 < baseStart_4085895 := by decide
  rcases family_descends (prefixWord ++ tailWord_4085895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4085951 : List Nat := [1, 1, 2, 2, 2, 2, 1, 2, 1, 9]
def baseStart_4085951 : Nat := 118140960795 + 4085951 * 2 ^ 59
def prefixEnd_4085951 : Nat := 4983230072969 + 3 ^ 40 * 4085951 * 2
def baseEnd_4085951 : Nat := 699352264573016143873853

theorem tailTrace_4085951 : CollatzResearch.WordTrace tailWord_4085951 prefixEnd_4085951 699352264573016143873853 := by
  unfold tailWord_4085951
  simp only [CollatzResearch.WordTrace]
  refine ⟨149026876020304826719233707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99351250680203217812822471 149026876020304826719233707)
  ·
    refine ⟨223540314030457240078850561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149026876020304826719233707 223540314030457240078850561)
    ·
      refine ⟨167655235522842930059137921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223540314030457240078850561 167655235522842930059137921)
      ·
        refine ⟨125741426642132197544353441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167655235522842930059137921 125741426642132197544353441)
        ·
          refine ⟨94306069981599148158265081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125741426642132197544353441 94306069981599148158265081)
          ·
            refine ⟨70729552486199361118698811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94306069981599148158265081 70729552486199361118698811)
            ·
              refine ⟨106094328729299041678048217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70729552486199361118698811 106094328729299041678048217)
              ·
                refine ⟨79570746546974281258536163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106094328729299041678048217 79570746546974281258536163)
                ·
                  refine ⟨119356119820461421887804245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79570746546974281258536163 119356119820461421887804245)
                  ·
                    refine ⟨699352264573016143873853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 119356119820461421887804245 699352264573016143873853)
                    ·
                      rfl

theorem cell23_4085951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 9].length) (baseStart_4085951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4085951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4085951 prefixEnd_4085951 := by exact prefixLift 4085951
  have htrace : WordTrace (prefixWord ++ tailWord_4085951) baseStart_4085951 baseEnd_4085951 := by
    simpa [prefixWord, tailWord_4085951, baseEnd_4085951] using wordTrace_append hprefix tailTrace_4085951
  have hstable : (prefixWord ++ tailWord_4085951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4085951).length < 2 ^ (prefixWord ++ tailWord_4085951).sum := by decide
  have hdescent : baseEnd_4085951 < baseStart_4085951 := by decide
  rcases family_descends (prefixWord ++ tailWord_4085951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4085975 : List Nat := [1, 1, 3, 2, 1, 2, 1, 4, 3, 3, 2]
def baseStart_4085975 : Nat := 118140960795 + 4085975 * 2 ^ 59
def prefixEnd_4085975 : Nat := 4983230072969 + 3 ^ 40 * 4085975 * 2
def baseEnd_4085975 : Nat := 2098069117254756337721449

theorem tailTrace_4085975 : CollatzResearch.WordTrace tailWord_4085975 prefixEnd_4085975 2098069117254756337721449 := by
  unfold tailWord_4085975
  simp only [CollatzResearch.WordTrace]
  refine ⟨149027751372217878818107379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99351834248145252545404919 149027751372217878818107379)
  ·
    refine ⟨223541627058326818227161069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149027751372217878818107379 223541627058326818227161069)
    ·
      refine ⟨83828110146872556835185401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223541627058326818227161069 83828110146872556835185401)
      ·
        refine ⟨62871082610154417626389051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83828110146872556835185401 62871082610154417626389051)
        ·
          refine ⟨94306623915231626439583577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62871082610154417626389051 94306623915231626439583577)
          ·
            refine ⟨70729967936423719829687683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94306623915231626439583577 70729967936423719829687683)
            ·
              refine ⟨106094951904635579744531525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70729967936423719829687683 106094951904635579744531525)
              ·
                refine ⟨19892803482119171202099661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 106094951904635579744531525 19892803482119171202099661)
                ·
                  refine ⟨7459801305794689200787373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19892803482119171202099661 7459801305794689200787373)
                  ·
                    refine ⟨2797425489673008450295265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7459801305794689200787373 2797425489673008450295265)
                    ·
                      refine ⟨2098069117254756337721449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2797425489673008450295265 2098069117254756337721449)
                      ·
                        rfl

theorem cell23_4085975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 4, 3, 3, 2].length) (baseStart_4085975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4085975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4085975 prefixEnd_4085975 := by exact prefixLift 4085975
  have htrace : WordTrace (prefixWord ++ tailWord_4085975) baseStart_4085975 baseEnd_4085975 := by
    simpa [prefixWord, tailWord_4085975, baseEnd_4085975] using wordTrace_append hprefix tailTrace_4085975
  have hstable : (prefixWord ++ tailWord_4085975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4085975).length < 2 ^ (prefixWord ++ tailWord_4085975).sum := by decide
  have hdescent : baseEnd_4085975 < baseStart_4085975 := by decide
  rcases family_descends (prefixWord ++ tailWord_4085975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4085986 : List Nat := [3, 3, 4, 1, 1, 1, 1, 1, 3, 2, 3]
def baseStart_4085986 : Nat := 118140960795 + 4085986 * 2 ^ 59
def prefixEnd_4085986 : Nat := 4983230072969 + 3 ^ 40 * 4085986 * 2
def baseEnd_4085986 : Nat := 2098074765541955794683899

theorem tailTrace_4085986 : CollatzResearch.WordTrace tailWord_4085986 prefixEnd_4085986 2098074765541955794683899 := by
  unfold tailWord_4085986
  simp only [CollatzResearch.WordTrace]
  refine ⟨37257038143794506924189453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99352101716785351797838541 37257038143794506924189453)
  ·
    refine ⟨13971389303922940096571045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37257038143794506924189453 13971389303922940096571045)
    ·
      refine ⟨2619635494485551268107071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13971389303922940096571045 2619635494485551268107071)
      ·
        refine ⟨3929453241728326902160607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2619635494485551268107071 3929453241728326902160607)
        ·
          refine ⟨5894179862592490353240911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3929453241728326902160607 5894179862592490353240911)
          ·
            refine ⟨8841269793888735529861367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5894179862592490353240911 8841269793888735529861367)
            ·
              refine ⟨13261904690833103294792051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8841269793888735529861367 13261904690833103294792051)
              ·
                refine ⟨19892857036249654942188077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13261904690833103294792051 19892857036249654942188077)
                ·
                  refine ⟨7459821388593620603320529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19892857036249654942188077 7459821388593620603320529)
                  ·
                    refine ⟨5594866041445215452490397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7459821388593620603320529 5594866041445215452490397)
                    ·
                      refine ⟨2098074765541955794683899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5594866041445215452490397 2098074765541955794683899)
                      ·
                        rfl

theorem cell23_4085986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_4085986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4085986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4085986 prefixEnd_4085986 := by exact prefixLift 4085986
  have htrace : WordTrace (prefixWord ++ tailWord_4085986) baseStart_4085986 baseEnd_4085986 := by
    simpa [prefixWord, tailWord_4085986, baseEnd_4085986] using wordTrace_append hprefix tailTrace_4085986
  have hstable : (prefixWord ++ tailWord_4085986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4085986).length < 2 ^ (prefixWord ++ tailWord_4085986).sum := by decide
  have hdescent : baseEnd_4085986 < baseStart_4085986 := by decide
  rcases family_descends (prefixWord ++ tailWord_4085986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4085992 : List Nat := [2, 1, 4, 1, 2, 3, 1, 1, 3, 3, 2]
def baseStart_4085992 : Nat := 118140960795 + 4085992 * 2 ^ 59
def prefixEnd_4085992 : Nat := 4983230072969 + 3 ^ 40 * 4085992 * 2
def baseEnd_4085992 : Nat := 2098077846425882771208871

theorem tailTrace_4085992 : CollatzResearch.WordTrace tailWord_4085992 prefixEnd_4085992 2098077846425882771208871 := by
  unfold tailWord_4085992
  simp only [CollatzResearch.WordTrace]
  refine ⟨74514185706578145360738115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99352247608770860480984153 74514185706578145360738115)
  ·
    refine ⟨111771278559867218041107173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74514185706578145360738115 111771278559867218041107173)
    ·
      refine ⟨20957114729975103382707595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111771278559867218041107173 20957114729975103382707595)
      ·
        refine ⟨31435672094962655074061393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20957114729975103382707595 31435672094962655074061393)
        ·
          refine ⟨23576754071221991305546045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31435672094962655074061393 23576754071221991305546045)
          ·
            refine ⟨8841282776708246739579767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23576754071221991305546045 8841282776708246739579767)
            ·
              refine ⟨13261924165062370109369651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8841282776708246739579767 13261924165062370109369651)
              ·
                refine ⟨19892886247593555164054477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13261924165062370109369651 19892886247593555164054477)
                ·
                  refine ⟨7459832342847583186520429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19892886247593555164054477 7459832342847583186520429)
                  ·
                    refine ⟨2797437128567843694945161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7459832342847583186520429 2797437128567843694945161)
                    ·
                      refine ⟨2098077846425882771208871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2797437128567843694945161 2098077846425882771208871)
                      ·
                        rfl

theorem cell23_4085992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 1, 3, 3, 2].length) (baseStart_4085992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4085992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4085992 prefixEnd_4085992 := by exact prefixLift 4085992
  have htrace : WordTrace (prefixWord ++ tailWord_4085992) baseStart_4085992 baseEnd_4085992 := by
    simpa [prefixWord, tailWord_4085992, baseEnd_4085992] using wordTrace_append hprefix tailTrace_4085992
  have hstable : (prefixWord ++ tailWord_4085992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4085992).length < 2 ^ (prefixWord ++ tailWord_4085992).sum := by decide
  have hdescent : baseEnd_4085992 < baseStart_4085992 := by decide
  rcases family_descends (prefixWord ++ tailWord_4085992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4085998 : List Nat := [4, 1, 2, 1, 1, 1, 1, 2, 4, 6]
def baseStart_4085998 : Nat := 118140960795 + 4085998 * 2 ^ 59
def prefixEnd_4085998 : Nat := 4983230072969 + 3 ^ 40 * 4085998 * 2
def baseEnd_4085998 : Nat := 699360309103269915911281

theorem tailTrace_4085998 : CollatzResearch.WordTrace tailWord_4085998 prefixEnd_4085998 699360309103269915911281 := by
  unfold tailWord_4085998
  simp only [CollatzResearch.WordTrace]
  refine ⟨18628573781391819218274331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99352393500756369164129765 18628573781391819218274331)
  ·
    refine ⟨27942860672087728827411497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18628573781391819218274331 27942860672087728827411497)
    ·
      refine ⟨20957145504065796620558623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27942860672087728827411497 20957145504065796620558623)
      ·
        refine ⟨31435718256098694930837935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20957145504065796620558623 31435718256098694930837935)
        ·
          refine ⟨47153577384148042396256903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31435718256098694930837935 47153577384148042396256903)
          ·
            refine ⟨70730366076222063594385355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47153577384148042396256903 70730366076222063594385355)
            ·
              refine ⟨106095549114333095391578033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70730366076222063594385355 106095549114333095391578033)
              ·
                refine ⟨79571661835749821543683525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106095549114333095391578033 79571661835749821543683525)
                ·
                  refine ⟨14919686594203091539440661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79571661835749821543683525 14919686594203091539440661)
                  ·
                    refine ⟨699360309103269915911281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14919686594203091539440661 699360309103269915911281)
                    ·
                      rfl

theorem cell23_4085998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 2, 4, 6].length) (baseStart_4085998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4085998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4085998 prefixEnd_4085998 := by exact prefixLift 4085998
  have htrace : WordTrace (prefixWord ++ tailWord_4085998) baseStart_4085998 baseEnd_4085998 := by
    simpa [prefixWord, tailWord_4085998, baseEnd_4085998] using wordTrace_append hprefix tailTrace_4085998
  have hstable : (prefixWord ++ tailWord_4085998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4085998).length < 2 ^ (prefixWord ++ tailWord_4085998).sum := by decide
  have hdescent : baseEnd_4085998 < baseStart_4085998 := by decide
  rcases family_descends (prefixWord ++ tailWord_4085998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4086008 : List Nat := [2, 1, 2, 1, 1, 2, 1, 2, 4, 4, 3]
def baseStart_4086008 : Nat := 118140960795 + 4086008 * 2 ^ 59
def prefixEnd_4086008 : Nat := 4983230072969 + 3 ^ 40 * 4086008 * 2
def baseEnd_4086008 : Nat := 2098086062116354708608797

theorem tailTrace_4086008 : CollatzResearch.WordTrace tailWord_4086008 prefixEnd_4086008 2098086062116354708608797 := by
  unfold tailWord_4086008
  simp only [CollatzResearch.WordTrace]
  refine ⟨74514477490549162727029339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99352636654065550302705785 74514477490549162727029339)
  ·
    refine ⟨111771716235823744090544009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74514477490549162727029339 111771716235823744090544009)
    ·
      refine ⟨83828787176867808067908007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111771716235823744090544009 83828787176867808067908007)
      ·
        refine ⟨125743180765301712101862011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83828787176867808067908007 125743180765301712101862011)
        ·
          refine ⟨188614771147952568152793017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125743180765301712101862011 188614771147952568152793017)
          ·
            refine ⟨141461078360964426114594763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188614771147952568152793017 141461078360964426114594763)
            ·
              refine ⟨212191617541446639171892145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141461078360964426114594763 212191617541446639171892145)
              ·
                refine ⟨159143713156084979378919109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 212191617541446639171892145 159143713156084979378919109)
                ·
                  refine ⟨29839446216765933633547333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 159143713156084979378919109 29839446216765933633547333)
                  ·
                    refine ⟨5594896165643612556290125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29839446216765933633547333 5594896165643612556290125)
                    ·
                      refine ⟨2098086062116354708608797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5594896165643612556290125 2098086062116354708608797)
                      ·
                        rfl

theorem cell23_4086008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 2, 4, 4, 3].length) (baseStart_4086008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4086008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4086008 prefixEnd_4086008 := by exact prefixLift 4086008
  have htrace : WordTrace (prefixWord ++ tailWord_4086008) baseStart_4086008 baseEnd_4086008 := by
    simpa [prefixWord, tailWord_4086008, baseEnd_4086008] using wordTrace_append hprefix tailTrace_4086008
  have hstable : (prefixWord ++ tailWord_4086008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4086008).length < 2 ^ (prefixWord ++ tailWord_4086008).sum := by decide
  have hdescent : baseEnd_4086008 < baseStart_4086008 := by decide
  rcases family_descends (prefixWord ++ tailWord_4086008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4086028 : List Nat := [2, 2, 1, 2, 2, 2, 2, 3, 7]
def baseStart_4086028 : Nat := 118140960795 + 4086028 * 2 ^ 59
def prefixEnd_4086028 : Nat := 4983230072969 + 3 ^ 40 * 4086028 * 2
def baseEnd_4086028 : Nat := 233121814636604958928745

theorem tailTrace_4086028 : CollatzResearch.WordTrace tailWord_4086028 prefixEnd_4086028 233121814636604958928745 := by
  unfold tailWord_4086028
  simp only [CollatzResearch.WordTrace]
  refine ⟨74514842220512934434893369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99353122960683912579857825 74514842220512934434893369)
  ·
    refine ⟨55886131665384700826170027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74514842220512934434893369 55886131665384700826170027)
    ·
      refine ⟨83829197498077051239255041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55886131665384700826170027 83829197498077051239255041)
      ·
        refine ⟨62871898123557788429441281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83829197498077051239255041 62871898123557788429441281)
        ·
          refine ⟨47153923592668341322080961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62871898123557788429441281 47153923592668341322080961)
          ·
            refine ⟨35365442694501255991560721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47153923592668341322080961 35365442694501255991560721)
            ·
              refine ⟨26524082020875941993670541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35365442694501255991560721 26524082020875941993670541)
              ·
                refine ⟨9946530757828478247626453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26524082020875941993670541 9946530757828478247626453)
                ·
                  refine ⟨233121814636604958928745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9946530757828478247626453 233121814636604958928745)
                  ·
                    rfl

theorem cell23_4086028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 3, 7].length) (baseStart_4086028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4086028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4086028 prefixEnd_4086028 := by exact prefixLift 4086028
  have htrace : WordTrace (prefixWord ++ tailWord_4086028) baseStart_4086028 baseEnd_4086028 := by
    simpa [prefixWord, tailWord_4086028, baseEnd_4086028] using wordTrace_append hprefix tailTrace_4086028
  have hstable : (prefixWord ++ tailWord_4086028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4086028).length < 2 ^ (prefixWord ++ tailWord_4086028).sum := by decide
  have hdescent : baseEnd_4086028 < baseStart_4086028 := by decide
  rcases family_descends (prefixWord ++ tailWord_4086028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4086039 : List Nat := [1, 1, 3, 4, 1, 2, 2, 3, 2, 2, 2]
def baseStart_4086039 : Nat := 118140960795 + 4086039 * 2 ^ 59
def prefixEnd_4086039 : Nat := 4983230072969 + 3 ^ 40 * 4086039 * 2
def baseEnd_4086039 : Nat := 2098101980016644087321155

theorem tailTrace_4086039 : CollatzResearch.WordTrace tailWord_4086039 prefixEnd_4086039 2098101980016644087321155 := by
  unfold tailWord_4086039
  simp only [CollatzResearch.WordTrace]
  refine ⟨149030085643986017748437171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99353390429324011832291447 149030085643986017748437171)
  ·
    refine ⟨223545128465979026622655757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149030085643986017748437171 223545128465979026622655757)
    ·
      refine ⟨83829423174742134983495909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223545128465979026622655757 83829423174742134983495909)
      ·
        refine ⟨15718016845264150309405483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83829423174742134983495909 15718016845264150309405483)
        ·
          refine ⟨23577025267896225464108225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15718016845264150309405483 23577025267896225464108225)
          ·
            refine ⟨17682768950922169098081169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23577025267896225464108225 17682768950922169098081169)
            ·
              refine ⟨13262076713191626823560877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17682768950922169098081169 13262076713191626823560877)
              ·
                refine ⟨4973278767446860058835329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13262076713191626823560877 4973278767446860058835329)
                ·
                  refine ⟨3729959075585145044126497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4973278767446860058835329 3729959075585145044126497)
                  ·
                    refine ⟨2797469306688858783094873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3729959075585145044126497 2797469306688858783094873)
                    ·
                      refine ⟨2098101980016644087321155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2797469306688858783094873 2098101980016644087321155)
                      ·
                        rfl

theorem cell23_4086039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 3, 2, 2, 2].length) (baseStart_4086039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4086039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4086039 prefixEnd_4086039 := by exact prefixLift 4086039
  have htrace : WordTrace (prefixWord ++ tailWord_4086039) baseStart_4086039 baseEnd_4086039 := by
    simpa [prefixWord, tailWord_4086039, baseEnd_4086039] using wordTrace_append hprefix tailTrace_4086039
  have hstable : (prefixWord ++ tailWord_4086039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4086039).length < 2 ^ (prefixWord ++ tailWord_4086039).sum := by decide
  have hdescent : baseEnd_4086039 < baseStart_4086039 := by decide
  rcases family_descends (prefixWord ++ tailWord_4086039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4086095 : List Nat := [1, 1, 2, 1, 1, 2, 1, 5, 1, 6, 2]
def baseStart_4086095 : Nat := 118140960795 + 4086095 * 2 ^ 59
def prefixEnd_4086095 : Nat := 4983230072969 + 3 ^ 40 * 4086095 * 2
def baseEnd_4086095 : Nat := 2098130734933295868220897

theorem tailTrace_4086095 : CollatzResearch.WordTrace tailWord_4086095 prefixEnd_4086095 2098130734933295868220897 := by
  unfold tailWord_4086095
  simp only [CollatzResearch.WordTrace]
  refine ⟨149032128131783139312475739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99354752087855426208317159 149032128131783139312475739)
  ·
    refine ⟨223548192197674708968713609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149032128131783139312475739 223548192197674708968713609)
    ·
      refine ⟨167661144148256031726535207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223548192197674708968713609 167661144148256031726535207)
      ·
        refine ⟨251491716222384047589802811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167661144148256031726535207 251491716222384047589802811)
        ·
          refine ⟨377237574333576071384704217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251491716222384047589802811 377237574333576071384704217)
          ·
            refine ⟨282928180750182053538528163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 377237574333576071384704217 282928180750182053538528163)
            ·
              refine ⟨424392271125273080307792245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 282928180750182053538528163 424392271125273080307792245)
              ·
                refine ⟨39786775417994351278855523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 424392271125273080307792245 39786775417994351278855523)
                ·
                  refine ⟨59680163126991526918283285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39786775417994351278855523 59680163126991526918283285)
                  ·
                    refine ⟨2797507646577727824294529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 59680163126991526918283285 2797507646577727824294529)
                    ·
                      refine ⟨2098130734933295868220897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2797507646577727824294529 2098130734933295868220897)
                      ·
                        rfl

theorem cell23_4086095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 5, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 5, 1, 6, 2].length) (baseStart_4086095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4086095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4086095 prefixEnd_4086095 := by exact prefixLift 4086095
  have htrace : WordTrace (prefixWord ++ tailWord_4086095) baseStart_4086095 baseEnd_4086095 := by
    simpa [prefixWord, tailWord_4086095, baseEnd_4086095] using wordTrace_append hprefix tailTrace_4086095
  have hstable : (prefixWord ++ tailWord_4086095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4086095).length < 2 ^ (prefixWord ++ tailWord_4086095).sum := by decide
  have hdescent : baseEnd_4086095 < baseStart_4086095 := by decide
  rcases family_descends (prefixWord ++ tailWord_4086095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4086115 : List Nat := [1, 1, 1, 5, 2, 1, 1, 3, 1, 4, 3]
def baseStart_4086115 : Nat := 118140960795 + 4086115 * 2 ^ 59
def prefixEnd_4086115 : Nat := 4983230072969 + 3 ^ 40 * 4086115 * 2
def baseEnd_4086115 : Nat := 2098141004546385789970805

theorem tailTrace_4086115 : CollatzResearch.WordTrace tailWord_4086115 prefixEnd_4086115 2098141004546385789970805 := by
  unfold tailWord_4086115
  simp only [CollatzResearch.WordTrace]
  refine ⟨149032857591710682728203799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99355238394473788485469199 149032857591710682728203799)
  ·
    refine ⟨223549286387566024092305699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149032857591710682728203799 223549286387566024092305699)
    ·
      refine ⟨335323929581349036138458549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223549286387566024092305699 335323929581349036138458549)
      ·
        refine ⟨31436618398251472137980489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 335323929581349036138458549 31436618398251472137980489)
        ·
          refine ⟨23577463798688604103485367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31436618398251472137980489 23577463798688604103485367)
          ·
            refine ⟨35366195698032906155228051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23577463798688604103485367 35366195698032906155228051)
            ·
              refine ⟨53049293547049359232842077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35366195698032906155228051 53049293547049359232842077)
              ·
                refine ⟨19893485080143509712315779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53049293547049359232842077 19893485080143509712315779)
                ·
                  refine ⟨29840227620215264568473669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19893485080143509712315779 29840227620215264568473669)
                  ·
                    refine ⟨5595042678790362106588813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29840227620215264568473669 5595042678790362106588813)
                    ·
                      refine ⟨2098141004546385789970805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5595042678790362106588813 2098141004546385789970805)
                      ·
                        rfl

theorem cell23_4086115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 3, 1, 4, 3].length) (baseStart_4086115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4086115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4086115 prefixEnd_4086115 := by exact prefixLift 4086115
  have htrace : WordTrace (prefixWord ++ tailWord_4086115) baseStart_4086115 baseEnd_4086115 := by
    simpa [prefixWord, tailWord_4086115, baseEnd_4086115] using wordTrace_append hprefix tailTrace_4086115
  have hstable : (prefixWord ++ tailWord_4086115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4086115).length < 2 ^ (prefixWord ++ tailWord_4086115).sum := by decide
  have hdescent : baseEnd_4086115 < baseStart_4086115 := by decide
  rcases family_descends (prefixWord ++ tailWord_4086115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4086239 : List Nat := [1, 1, 2, 3, 3, 3, 1, 3, 1, 2, 3]
def baseStart_4086239 : Nat := 118140960795 + 4086239 * 2 ^ 59
def prefixEnd_4086239 : Nat := 4983230072969 + 3 ^ 40 * 4086239 * 2
def baseEnd_4086239 : Nat := 2098204676147543304820235

theorem tailTrace_4086239 : CollatzResearch.WordTrace tailWord_4086239 prefixEnd_4086239 2098204676147543304820235 := by
  unfold tailWord_4086239
  simp only [CollatzResearch.WordTrace]
  refine ⟨149037380243261451905717771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99358253495507634603811847 149037380243261451905717771)
  ·
    refine ⟨223556070364892177858576657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149037380243261451905717771 223556070364892177858576657)
    ·
      refine ⟨167667052773669133393932493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223556070364892177858576657 167667052773669133393932493)
      ·
        refine ⟨62875144790125925022724685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167667052773669133393932493 62875144790125925022724685)
        ·
          refine ⟨23578179296297221883521757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62875144790125925022724685 23578179296297221883521757)
          ·
            refine ⟨8841817236111458206320659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23578179296297221883521757 8841817236111458206320659)
            ·
              refine ⟨13262725854167187309480989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8841817236111458206320659 13262725854167187309480989)
              ·
                refine ⟨4973522195312695241055371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13262725854167187309480989 4973522195312695241055371)
                ·
                  refine ⟨7460283292969042861583057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4973522195312695241055371 7460283292969042861583057)
                  ·
                    refine ⟨5595212469726782146187293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7460283292969042861583057 5595212469726782146187293)
                    ·
                      refine ⟨2098204676147543304820235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5595212469726782146187293 2098204676147543304820235)
                      ·
                        rfl

theorem cell23_4086239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 3, 1, 2, 3].length) (baseStart_4086239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4086239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4086239 prefixEnd_4086239 := by exact prefixLift 4086239
  have htrace : WordTrace (prefixWord ++ tailWord_4086239) baseStart_4086239 baseEnd_4086239 := by
    simpa [prefixWord, tailWord_4086239, baseEnd_4086239] using wordTrace_append hprefix tailTrace_4086239
  have hstable : (prefixWord ++ tailWord_4086239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4086239).length < 2 ^ (prefixWord ++ tailWord_4086239).sum := by decide
  have hdescent : baseEnd_4086239 < baseStart_4086239 := by decide
  rcases family_descends (prefixWord ++ tailWord_4086239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4086253 : List Nat := [1, 5, 1, 3, 1, 2, 2, 1, 3, 2, 2]
def baseStart_4086253 : Nat := 118140960795 + 4086253 * 2 ^ 59
def prefixEnd_4086253 : Nat := 4983230072969 + 3 ^ 40 * 4086253 * 2
def baseEnd_4086253 : Nat := 2098211864876706250045171

theorem tailTrace_4086253 : CollatzResearch.WordTrace tailWord_4086253 prefixEnd_4086253 2098211864876706250045171 := by
  unfold tailWord_4086253
  simp only [CollatzResearch.WordTrace]
  refine ⟨149037890865210732296727413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99358593910140488197818275 149037890865210732296727413)
  ·
    refine ⟨13972302268613506152818195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 149037890865210732296727413 13972302268613506152818195)
    ·
      refine ⟨20958453402920259229227293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13972302268613506152818195 20958453402920259229227293)
      ·
        refine ⟨7859420026095097210960235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20958453402920259229227293 7859420026095097210960235)
        ·
          refine ⟨11789130039142645816440353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7859420026095097210960235 11789130039142645816440353)
          ·
            refine ⟨8841847529356984362330265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11789130039142645816440353 8841847529356984362330265)
            ·
              refine ⟨6631385647017738271747699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8841847529356984362330265 6631385647017738271747699)
              ·
                refine ⟨9947078470526607407621549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6631385647017738271747699 9947078470526607407621549)
                ·
                  refine ⟨3730154426447477777858081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9947078470526607407621549 3730154426447477777858081)
                  ·
                    refine ⟨2797615819835608333393561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3730154426447477777858081 2797615819835608333393561)
                    ·
                      refine ⟨2098211864876706250045171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2797615819835608333393561 2098211864876706250045171)
                      ·
                        rfl

theorem cell23_4086253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 2, 1, 3, 2, 2].length) (baseStart_4086253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4086253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4086253 prefixEnd_4086253 := by exact prefixLift 4086253
  have htrace : WordTrace (prefixWord ++ tailWord_4086253) baseStart_4086253 baseEnd_4086253 := by
    simpa [prefixWord, tailWord_4086253, baseEnd_4086253] using wordTrace_append hprefix tailTrace_4086253
  have hstable : (prefixWord ++ tailWord_4086253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4086253).length < 2 ^ (prefixWord ++ tailWord_4086253).sum := by decide
  have hdescent : baseEnd_4086253 < baseStart_4086253 := by decide
  rcases family_descends (prefixWord ++ tailWord_4086253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4086296 : List Nat := [2, 1, 2, 3, 3, 1, 2, 3, 1, 3, 2]
def baseStart_4086296 : Nat := 118140960795 + 4086296 * 2 ^ 59
def prefixEnd_4086296 : Nat := 4983230072969 + 3 ^ 40 * 4086296 * 2
def baseEnd_4086296 : Nat := 2098233944544849581807473

theorem tailTrace_4086296 : CollatzResearch.WordTrace tailWord_4086296 prefixEnd_4086296 2098233944544849581807473 := by
  unfold tailWord_4086296
  simp only [CollatzResearch.WordTrace]
  refine ⟨74519729602027475320271371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99359639469369967093695161 74519729602027475320271371)
  ·
    refine ⟨111779594403041212980407057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74519729602027475320271371 111779594403041212980407057)
    ·
      refine ⟨83834695802280909735305293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111779594403041212980407057 83834695802280909735305293)
      ·
        refine ⟨31438010925855341150739485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83834695802280909735305293 31438010925855341150739485)
        ·
          refine ⟨11789254097195752931527307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31438010925855341150739485 11789254097195752931527307)
          ·
            refine ⟨17683881145793629397290961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11789254097195752931527307 17683881145793629397290961)
            ·
              refine ⟨13262910859345222047968221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17683881145793629397290961 13262910859345222047968221)
              ·
                refine ⟨4973591572254458267988083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13262910859345222047968221 4973591572254458267988083)
                ·
                  refine ⟨7460387358381687401982125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4973591572254458267988083 7460387358381687401982125)
                  ·
                    refine ⟨2797645259393132775743297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7460387358381687401982125 2797645259393132775743297)
                    ·
                      refine ⟨2098233944544849581807473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2797645259393132775743297 2098233944544849581807473)
                      ·
                        rfl

theorem cell23_4086296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 3, 1, 3, 2].length) (baseStart_4086296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4086296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4086296 prefixEnd_4086296 := by exact prefixLift 4086296
  have htrace : WordTrace (prefixWord ++ tailWord_4086296) baseStart_4086296 baseEnd_4086296 := by
    simpa [prefixWord, tailWord_4086296, baseEnd_4086296] using wordTrace_append hprefix tailTrace_4086296
  have hstable : (prefixWord ++ tailWord_4086296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4086296).length < 2 ^ (prefixWord ++ tailWord_4086296).sum := by decide
  have hdescent : baseEnd_4086296 < baseStart_4086296 := by decide
  rcases family_descends (prefixWord ++ tailWord_4086296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4086322 : List Nat := [3, 2, 1, 1, 2, 1, 2, 3, 2, 2, 4]
def baseStart_4086322 : Nat := 118140960795 + 4086322 * 2 ^ 59
def prefixEnd_4086322 : Nat := 4983230072969 + 3 ^ 40 * 4086322 * 2
def baseEnd_4086322 : Nat := 2098247295041866480082353

theorem tailTrace_4086322 : CollatzResearch.WordTrace tailWord_4086322 prefixEnd_4086322 2098247295041866480082353 := by
  unfold tailWord_4086322
  simp only [CollatzResearch.WordTrace]
  refine ⟨37260101875490189270247305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99360271667973838053992813 37260101875490189270247305)
  ·
    refine ⟨27945076406617641952685479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37260101875490189270247305 27945076406617641952685479)
    ·
      refine ⟨41917614609926462929028219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27945076406617641952685479 41917614609926462929028219)
      ·
        refine ⟨62876421914889694393542329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41917614609926462929028219 62876421914889694393542329)
        ·
          refine ⟨47157316436167270795156747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62876421914889694393542329 47157316436167270795156747)
          ·
            refine ⟨70735974654250906192735121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47157316436167270795156747 70735974654250906192735121)
            ·
              refine ⟨53051980990688179644551341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70735974654250906192735121 53051980990688179644551341)
              ·
                refine ⟨19894492871508067366706753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53051980990688179644551341 19894492871508067366706753)
                ·
                  refine ⟨14920869653631050525030065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19894492871508067366706753 14920869653631050525030065)
                  ·
                    refine ⟨11190652240223287893772549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14920869653631050525030065 11190652240223287893772549)
                    ·
                      refine ⟨2098247295041866480082353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11190652240223287893772549 2098247295041866480082353)
                      ·
                        rfl

theorem cell23_4086322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 3, 2, 2, 4].length) (baseStart_4086322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4086322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4086322 prefixEnd_4086322 := by exact prefixLift 4086322
  have htrace : WordTrace (prefixWord ++ tailWord_4086322) baseStart_4086322 baseEnd_4086322 := by
    simpa [prefixWord, tailWord_4086322, baseEnd_4086322] using wordTrace_append hprefix tailTrace_4086322
  have hstable : (prefixWord ++ tailWord_4086322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4086322).length < 2 ^ (prefixWord ++ tailWord_4086322).sum := by decide
  have hdescent : baseEnd_4086322 < baseStart_4086322 := by decide
  rcases family_descends (prefixWord ++ tailWord_4086322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4086369 : List Nat := [1, 2, 3, 1, 1, 4, 1, 1, 2, 5, 2]
def baseStart_4086369 : Nat := 118140960795 + 4086369 * 2 ^ 59
def prefixEnd_4086369 : Nat := 4983230072969 + 3 ^ 40 * 4086369 * 2
def baseEnd_4086369 : Nat := 2098271428632627796194637

theorem tailTrace_4086369 : CollatzResearch.WordTrace tailWord_4086369 prefixEnd_4086369 2098271428632627796194637 := by
  unfold tailWord_4086369
  simp only [CollatzResearch.WordTrace]
  refine ⟨149042121732790484107950161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99361414488526989405300107 149042121732790484107950161)
  ·
    refine ⟨111781591299592863080962621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149042121732790484107950161 111781591299592863080962621)
    ·
      refine ⟨41918096737347323655360983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111781591299592863080962621 41918096737347323655360983)
      ·
        refine ⟨62877145106020985483041475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41918096737347323655360983 62877145106020985483041475)
        ·
          refine ⟨94315717659031478224562213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62877145106020985483041475 94315717659031478224562213)
          ·
            refine ⟨17684197061068402167105415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94315717659031478224562213 17684197061068402167105415)
            ·
              refine ⟨26526295591602603250658123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17684197061068402167105415 26526295591602603250658123)
              ·
                refine ⟨39789443387403904875987185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26526295591602603250658123 39789443387403904875987185)
                ·
                  refine ⟨29842082540552928656990389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39789443387403904875987185 29842082540552928656990389)
                  ·
                    refine ⟨2797695238176837061592849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29842082540552928656990389 2797695238176837061592849)
                    ·
                      refine ⟨2098271428632627796194637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2797695238176837061592849 2098271428632627796194637)
                      ·
                        rfl

theorem cell23_4086369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 1, 2, 5, 2].length) (baseStart_4086369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4086369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4086369 prefixEnd_4086369 := by exact prefixLift 4086369
  have htrace : WordTrace (prefixWord ++ tailWord_4086369) baseStart_4086369 baseEnd_4086369 := by
    simpa [prefixWord, tailWord_4086369, baseEnd_4086369] using wordTrace_append hprefix tailTrace_4086369
  have hstable : (prefixWord ++ tailWord_4086369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4086369).length < 2 ^ (prefixWord ++ tailWord_4086369).sum := by decide
  have hdescent : baseEnd_4086369 < baseStart_4086369 := by decide
  rcases family_descends (prefixWord ++ tailWord_4086369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4086372 : List Nat := [2, 3, 1, 1, 2, 2, 1, 3, 1, 2, 5]
def baseStart_4086372 : Nat := 118140960795 + 4086372 * 2 ^ 59
def prefixEnd_4086372 : Nat := 4983230072969 + 3 ^ 40 * 4086372 * 2
def baseEnd_4086372 : Nat := 2098272969074591284457123

theorem tailTrace_4086372 : CollatzResearch.WordTrace tailWord_4086372 prefixEnd_4086372 2098272969074591284457123 := by
  unfold tailWord_4086372
  simp only [CollatzResearch.WordTrace]
  refine ⟨74521115575889807810154685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99361487434519743746872913 74521115575889807810154685)
  ·
    refine ⟨27945418340958677928808007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74521115575889807810154685 27945418340958677928808007)
    ·
      refine ⟨41918127511438016893212011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27945418340958677928808007 41918127511438016893212011)
      ·
        refine ⟨62877191267157025339818017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41918127511438016893212011 62877191267157025339818017)
        ·
          refine ⟨47157893450367769004863513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62877191267157025339818017 47157893450367769004863513)
          ·
            refine ⟨35368420087775826753647635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47157893450367769004863513 35368420087775826753647635)
            ·
              refine ⟨53052630131663740130471453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35368420087775826753647635 53052630131663740130471453)
              ·
                refine ⟨19894736299373902548926795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53052630131663740130471453 19894736299373902548926795)
                ·
                  refine ⟨29842104449060853823390193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19894736299373902548926795 29842104449060853823390193)
                  ·
                    refine ⟨22381578336795640367542645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29842104449060853823390193 22381578336795640367542645)
                    ·
                      refine ⟨2098272969074591284457123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22381578336795640367542645 2098272969074591284457123)
                      ·
                        rfl

theorem cell23_4086372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 3, 1, 2, 5].length) (baseStart_4086372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4086372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4086372 prefixEnd_4086372 := by exact prefixLift 4086372
  have htrace : WordTrace (prefixWord ++ tailWord_4086372) baseStart_4086372 baseEnd_4086372 := by
    simpa [prefixWord, tailWord_4086372, baseEnd_4086372] using wordTrace_append hprefix tailTrace_4086372
  have hstable : (prefixWord ++ tailWord_4086372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4086372).length < 2 ^ (prefixWord ++ tailWord_4086372).sum := by decide
  have hdescent : baseEnd_4086372 < baseStart_4086372 := by decide
  rcases family_descends (prefixWord ++ tailWord_4086372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4086376 : List Nat := [2, 1, 4, 3, 2, 1, 1, 1, 2, 3, 3]
def baseStart_4086376 : Nat := 118140960795 + 4086376 * 2 ^ 59
def prefixEnd_4086376 : Nat := 4983230072969 + 3 ^ 40 * 4086376 * 2
def baseEnd_4086376 : Nat := 2098275022997209268807105

theorem tailTrace_4086376 : CollatzResearch.WordTrace tailWord_4086376 prefixEnd_4086376 2098275022997209268807105 := by
  unfold tailWord_4086376
  simp only [CollatzResearch.WordTrace]
  refine ⟨74521188521882562151727491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99361584695843416202303321 74521188521882562151727491)
  ·
    refine ⟨111781782782823843227591237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74521188521882562151727491 111781782782823843227591237)
    ·
      refine ⟨20959084271779470605173357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111781782782823843227591237 20959084271779470605173357)
      ·
        refine ⟨7859656601917301476940009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20959084271779470605173357 7859656601917301476940009)
        ·
          refine ⟨5894742451437976107705007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7859656601917301476940009 5894742451437976107705007)
          ·
            refine ⟨8842113677156964161557511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5894742451437976107705007 8842113677156964161557511)
            ·
              refine ⟨13263170515735446242336267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8842113677156964161557511 13263170515735446242336267)
              ·
                refine ⟨19894755773603169363504401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13263170515735446242336267 19894755773603169363504401)
                ·
                  refine ⟨14921066830202377022628301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19894755773603169363504401 14921066830202377022628301)
                  ·
                    refine ⟨5595400061325891383485613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14921066830202377022628301 5595400061325891383485613)
                    ·
                      refine ⟨2098275022997209268807105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5595400061325891383485613 2098275022997209268807105)
                      ·
                        rfl

theorem cell23_4086376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_4086376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4086376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4086376 prefixEnd_4086376 := by exact prefixLift 4086376
  have htrace : WordTrace (prefixWord ++ tailWord_4086376) baseStart_4086376 baseEnd_4086376 := by
    simpa [prefixWord, tailWord_4086376, baseEnd_4086376] using wordTrace_append hprefix tailTrace_4086376
  have hstable : (prefixWord ++ tailWord_4086376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4086376).length < 2 ^ (prefixWord ++ tailWord_4086376).sum := by decide
  have hdescent : baseEnd_4086376 < baseStart_4086376 := by decide
  rcases family_descends (prefixWord ++ tailWord_4086376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4086477 : List Nat := [1, 6, 2, 1, 3, 1, 1, 1, 3, 4]
def baseStart_4086477 : Nat := 118140960795 + 4086477 * 2 ^ 59
def prefixEnd_4086477 : Nat := 4983230072969 + 3 ^ 40 * 4086477 * 2
def baseEnd_4086477 : Nat := 699442294847771124548047

theorem tailTrace_4086477 : CollatzResearch.WordTrace tailWord_4086477 prefixEnd_4086477 699442294847771124548047 := by
  unfold tailWord_4086477
  simp only [CollatzResearch.WordTrace]
  refine ⟨149046060816399218552881685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99364040544266145701921123 149046060816399218552881685)
  ·
    refine ⟨6986534100768713369666329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 149046060816399218552881685 6986534100768713369666329)
    ·
      refine ⟨5239900575576535027249747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6986534100768713369666329 5239900575576535027249747)
      ·
        refine ⟨7859850863364802540874621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5239900575576535027249747 7859850863364802540874621)
        ·
          refine ⟨2947444073761800952827983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7859850863364802540874621 2947444073761800952827983)
          ·
            refine ⟨4421166110642701429241975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2947444073761800952827983 4421166110642701429241975)
            ·
              refine ⟨6631749165964052143862963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4421166110642701429241975 6631749165964052143862963)
              ·
                refine ⟨9947623748946078215794445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6631749165964052143862963 9947623748946078215794445)
                ·
                  refine ⟨3730358905854779330922917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9947623748946078215794445 3730358905854779330922917)
                  ·
                    refine ⟨699442294847771124548047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3730358905854779330922917 699442294847771124548047)
                    ·
                      rfl

theorem cell23_4086477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_4086477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4086477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4086477 prefixEnd_4086477 := by exact prefixLift 4086477
  have htrace : WordTrace (prefixWord ++ tailWord_4086477) baseStart_4086477 baseEnd_4086477 := by
    simpa [prefixWord, tailWord_4086477, baseEnd_4086477] using wordTrace_append hprefix tailTrace_4086477
  have hstable : (prefixWord ++ tailWord_4086477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4086477).length < 2 ^ (prefixWord ++ tailWord_4086477).sum := by decide
  have hdescent : baseEnd_4086477 < baseStart_4086477 := by decide
  rcases family_descends (prefixWord ++ tailWord_4086477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4086489 : List Nat := [1, 2, 1, 2, 3, 2, 2, 2, 3, 1, 4]
def baseStart_4086489 : Nat := 118140960795 + 4086489 * 2 ^ 59
def prefixEnd_4086489 : Nat := 4983230072969 + 3 ^ 40 * 4086489 * 2
def baseEnd_4086489 : Nat := 2098333046311167326694085

theorem tailTrace_4086489 : CollatzResearch.WordTrace tailWord_4086489 prefixEnd_4086489 2098333046311167326694085 := by
  unfold tailWord_4086489
  simp only [CollatzResearch.WordTrace]
  refine ⟨149046498492355744602318521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99364332328237163068212347 149046498492355744602318521)
  ·
    refine ⟨111784873869266808451738891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 149046498492355744602318521 111784873869266808451738891)
    ·
      refine ⟨167677310803900212677608337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111784873869266808451738891 167677310803900212677608337)
      ·
        refine ⟨125757983102925159508206253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167677310803900212677608337 125757983102925159508206253)
        ·
          refine ⟨47159243663596934815577345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125757983102925159508206253 47159243663596934815577345)
          ·
            refine ⟨35369432747697701111683009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47159243663596934815577345 35369432747697701111683009)
            ·
              refine ⟨26527074560773275833762257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35369432747697701111683009 26527074560773275833762257)
              ·
                refine ⟨19895305920579956875321693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26527074560773275833762257 19895305920579956875321693)
                ·
                  refine ⟨7460739720217483828245635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19895305920579956875321693 7460739720217483828245635)
                  ·
                    refine ⟨11191109580326225742368453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7460739720217483828245635 11191109580326225742368453)
                    ·
                      refine ⟨2098333046311167326694085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11191109580326225742368453 2098333046311167326694085)
                      ·
                        rfl

theorem cell23_4086489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 2, 3, 1, 4].length) (baseStart_4086489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4086489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4086489 prefixEnd_4086489 := by exact prefixLift 4086489
  have htrace : WordTrace (prefixWord ++ tailWord_4086489) baseStart_4086489 baseEnd_4086489 := by
    simpa [prefixWord, tailWord_4086489, baseEnd_4086489] using wordTrace_append hprefix tailTrace_4086489
  have hstable : (prefixWord ++ tailWord_4086489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4086489).length < 2 ^ (prefixWord ++ tailWord_4086489).sum := by decide
  have hdescent : baseEnd_4086489 < baseStart_4086489 := by decide
  rcases family_descends (prefixWord ++ tailWord_4086489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4086512 : List Nat := [2, 1, 1, 1, 3, 1, 3, 11]
def baseStart_4086512 : Nat := 118140960795 + 4086512 * 2 ^ 59
def prefixEnd_4086512 : Nat := 4983230072969 + 3 ^ 40 * 4086512 * 2
def baseEnd_4086512 : Nat := 77716476161711879137277

theorem tailTrace_4086512 : CollatzResearch.WordTrace tailWord_4086512 prefixEnd_4086512 77716476161711879137277 := by
  unfold tailWord_4086512
  simp only [CollatzResearch.WordTrace]
  refine ⟨74523668685636209765202895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99364891580848279686937193 74523668685636209765202895)
  ·
    refine ⟨111785503028454314647804343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74523668685636209765202895 111785503028454314647804343)
    ·
      refine ⟨167678254542681471971706515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111785503028454314647804343 167678254542681471971706515)
      ·
        refine ⟨251517381814022207957559773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167678254542681471971706515 251517381814022207957559773)
        ·
          refine ⟨94319018180258327984084915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 251517381814022207957559773 94319018180258327984084915)
          ·
            refine ⟨141478527270387491976127373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94319018180258327984084915 141478527270387491976127373)
            ·
              refine ⟨53054447726395309491047765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141478527270387491976127373 53054447726395309491047765)
              ·
                refine ⟨77716476161711879137277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 53054447726395309491047765 77716476161711879137277)
                ·
                  rfl

theorem cell23_4086512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 11].length) (baseStart_4086512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4086512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4086512 prefixEnd_4086512 := by exact prefixLift 4086512
  have htrace : WordTrace (prefixWord ++ tailWord_4086512) baseStart_4086512 baseEnd_4086512 := by
    simpa [prefixWord, tailWord_4086512, baseEnd_4086512] using wordTrace_append hprefix tailTrace_4086512
  have hstable : (prefixWord ++ tailWord_4086512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4086512).length < 2 ^ (prefixWord ++ tailWord_4086512).sum := by decide
  have hdescent : baseEnd_4086512 < baseStart_4086512 := by decide
  rcases family_descends (prefixWord ++ tailWord_4086512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4086539 : List Nat := [1, 1, 1, 1, 5, 1, 1, 1, 5, 3, 3]
def baseStart_4086539 : Nat := 118140960795 + 4086539 * 2 ^ 59
def prefixEnd_4086539 : Nat := 4983230072969 + 3 ^ 40 * 4086539 * 2
def baseEnd_4086539 : Nat := 2098358720343892131068855

theorem tailTrace_4086539 : CollatzResearch.WordTrace tailWord_4086539 prefixEnd_4086539 2098358720343892131068855 := by
  unfold tailWord_4086539
  simp only [CollatzResearch.WordTrace]
  refine ⟨149048322142174603141638671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99365548094783068761092447 149048322142174603141638671)
  ·
    refine ⟨223572483213261904712458007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149048322142174603141638671 223572483213261904712458007)
    ·
      refine ⟨335358724819892857068687011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223572483213261904712458007 335358724819892857068687011)
      ·
        refine ⟨503038087229839285603030517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335358724819892857068687011 503038087229839285603030517)
        ·
          refine ⟨47159820677797433025284111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 503038087229839285603030517 47159820677797433025284111)
          ·
            refine ⟨70739731016696149537926167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47159820677797433025284111 70739731016696149537926167)
            ·
              refine ⟨106109596525044224306889251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70739731016696149537926167 106109596525044224306889251)
              ·
                refine ⟨159164394787566336460333877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106109596525044224306889251 159164394787566336460333877)
                ·
                  refine ⟨14921662011334344043156301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 159164394787566336460333877 14921662011334344043156301)
                  ·
                    refine ⟨5595623254250379016183613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14921662011334344043156301 5595623254250379016183613)
                    ·
                      refine ⟨2098358720343892131068855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5595623254250379016183613 2098358720343892131068855)
                      ·
                        rfl

theorem cell23_4086539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 5, 3, 3].length) (baseStart_4086539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4086539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4086539 prefixEnd_4086539 := by exact prefixLift 4086539
  have htrace : WordTrace (prefixWord ++ tailWord_4086539) baseStart_4086539 baseEnd_4086539 := by
    simpa [prefixWord, tailWord_4086539, baseEnd_4086539] using wordTrace_append hprefix tailTrace_4086539
  have hstable : (prefixWord ++ tailWord_4086539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4086539).length < 2 ^ (prefixWord ++ tailWord_4086539).sum := by decide
  have hdescent : baseEnd_4086539 < baseStart_4086539 := by decide
  rcases family_descends (prefixWord ++ tailWord_4086539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4086556 : List Nat := [2, 2, 3, 1, 1, 3, 1, 3, 1, 3, 3]
def baseStart_4086556 : Nat := 118140960795 + 4086556 * 2 ^ 59
def prefixEnd_4086556 : Nat := 4983230072969 + 3 ^ 40 * 4086556 * 2
def baseEnd_4086556 : Nat := 2098367449515018564556277

theorem tailTrace_4086556 : CollatzResearch.WordTrace tailWord_4086556 prefixEnd_4086556 2098367449515018564556277 := by
  unfold tailWord_4086556
  simp only [CollatzResearch.WordTrace]
  refine ⟨74524471091556507522503761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99365961455408676696671681 74524471091556507522503761)
  ·
    refine ⟨55893353318667380641877821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74524471091556507522503761 55893353318667380641877821)
    ·
      refine ⟨20960007494500267740704183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55893353318667380641877821 20960007494500267740704183)
      ·
        refine ⟨31440011241750401611056275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20960007494500267740704183 31440011241750401611056275)
        ·
          refine ⟨47160016862625602416584413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31440011241750401611056275 47160016862625602416584413)
          ·
            refine ⟨17685006323484600906219155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47160016862625602416584413 17685006323484600906219155)
            ·
              refine ⟨26527509485226901359328733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17685006323484600906219155 26527509485226901359328733)
              ·
                refine ⟨9947816056960088009748275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26527509485226901359328733 9947816056960088009748275)
                ·
                  refine ⟨14921724085440132014622413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9947816056960088009748275 14921724085440132014622413)
                  ·
                    refine ⟨5595646532040049505483405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14921724085440132014622413 5595646532040049505483405)
                    ·
                      refine ⟨2098367449515018564556277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5595646532040049505483405 2098367449515018564556277)
                      ·
                        rfl

theorem cell23_4086556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 3, 1, 3, 3].length) (baseStart_4086556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4086556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4086556 prefixEnd_4086556 := by exact prefixLift 4086556
  have htrace : WordTrace (prefixWord ++ tailWord_4086556) baseStart_4086556 baseEnd_4086556 := by
    simpa [prefixWord, tailWord_4086556, baseEnd_4086556] using wordTrace_append hprefix tailTrace_4086556
  have hstable : (prefixWord ++ tailWord_4086556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4086556).length < 2 ^ (prefixWord ++ tailWord_4086556).sum := by decide
  have hdescent : baseEnd_4086556 < baseStart_4086556 := by decide
  rcases family_descends (prefixWord ++ tailWord_4086556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4086557 : List Nat := [1, 4, 2, 4, 1, 1, 1, 2, 3, 2, 2]
def baseStart_4086557 : Nat := 118140960795 + 4086557 * 2 ^ 59
def prefixEnd_4086557 : Nat := 4983230072969 + 3 ^ 40 * 4086557 * 2
def baseEnd_4086557 : Nat := 2098367962995673060643773

theorem tailTrace_4086557 : CollatzResearch.WordTrace tailWord_4086557 prefixEnd_4086557 2098367962995673060643773 := by
  unfold tailWord_4086557
  simp only [CollatzResearch.WordTrace]
  refine ⟨149048978656109392215793925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99365985770739594810529283 149048978656109392215793925)
  ·
    refine ⟨27946683498020511040461361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 149048978656109392215793925 27946683498020511040461361)
    ·
      refine ⟨20960012623515383280346021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27946683498020511040461361 20960012623515383280346021)
      ·
        refine ⟨3930002366909134365064879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20960012623515383280346021 3930002366909134365064879)
        ·
          refine ⟨5895003550363701547597319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3930002366909134365064879 5895003550363701547597319)
          ·
            refine ⟨8842505325545552321395979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5895003550363701547597319 8842505325545552321395979)
            ·
              refine ⟨13263757988318328482093969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8842505325545552321395979 13263757988318328482093969)
              ·
                refine ⟨9947818491238746361570477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13263757988318328482093969 9947818491238746361570477)
                ·
                  refine ⟨3730431934214529885588929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9947818491238746361570477 3730431934214529885588929)
                  ·
                    refine ⟨2797823950660897414191697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3730431934214529885588929 2797823950660897414191697)
                    ·
                      refine ⟨2098367962995673060643773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2797823950660897414191697 2098367962995673060643773)
                      ·
                        rfl

theorem cell23_4086557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_4086557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4086557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4086557 prefixEnd_4086557 := by exact prefixLift 4086557
  have htrace : WordTrace (prefixWord ++ tailWord_4086557) baseStart_4086557 baseEnd_4086557 := by
    simpa [prefixWord, tailWord_4086557, baseEnd_4086557] using wordTrace_append hprefix tailTrace_4086557
  have hstable : (prefixWord ++ tailWord_4086557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4086557).length < 2 ^ (prefixWord ++ tailWord_4086557).sum := by decide
  have hdescent : baseEnd_4086557 < baseStart_4086557 := by decide
  rcases family_descends (prefixWord ++ tailWord_4086557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4086574 : List Nat := [4, 1, 3, 2, 1, 2, 2, 3, 1, 2, 2]
def baseStart_4086574 : Nat := 118140960795 + 4086574 * 2 ^ 59
def prefixEnd_4086574 : Nat := 4983230072969 + 3 ^ 40 * 4086574 * 2
def baseEnd_4086574 : Nat := 2098376692166799494131195

theorem tailTrace_4086574 : CollatzResearch.WordTrace tailWord_4086574 prefixEnd_4086574 2098376692166799494131195 := by
  unfold tailWord_4086574
  simp only [CollatzResearch.WordTrace]
  refine ⟨18631199837130975514895347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99366399131365202746108517 18631199837130975514895347)
  ·
    refine ⟨27946799755696463272343021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18631199837130975514895347 27946799755696463272343021)
    ·
      refine ⟨10480049908386173727128633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27946799755696463272343021 10480049908386173727128633)
      ·
        refine ⟨7860037431289630295346475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10480049908386173727128633 7860037431289630295346475)
        ·
          refine ⟨11790056146934445443019713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7860037431289630295346475 11790056146934445443019713)
          ·
            refine ⟨8842542110200834082264785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11790056146934445443019713 8842542110200834082264785)
            ·
              refine ⟨6631906582650625561698589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8842542110200834082264785 6631906582650625561698589)
              ·
                refine ⟨2486964968493984585636971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6631906582650625561698589 2486964968493984585636971)
                ·
                  refine ⟨3730447452740976878455457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2486964968493984585636971 3730447452740976878455457)
                  ·
                    refine ⟨2797835589555732658841593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3730447452740976878455457 2797835589555732658841593)
                    ·
                      refine ⟨2098376692166799494131195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2797835589555732658841593 2098376692166799494131195)
                      ·
                        rfl

theorem cell23_4086574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 2, 3, 1, 2, 2].length) (baseStart_4086574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4086574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4086574 prefixEnd_4086574 := by exact prefixLift 4086574
  have htrace : WordTrace (prefixWord ++ tailWord_4086574) baseStart_4086574 baseEnd_4086574 := by
    simpa [prefixWord, tailWord_4086574, baseEnd_4086574] using wordTrace_append hprefix tailTrace_4086574
  have hstable : (prefixWord ++ tailWord_4086574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4086574).length < 2 ^ (prefixWord ++ tailWord_4086574).sum := by decide
  have hdescent : baseEnd_4086574 < baseStart_4086574 := by decide
  rcases family_descends (prefixWord ++ tailWord_4086574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4086583 : List Nat := [1, 1, 3, 1, 2, 1, 5, 3, 1, 3, 2]
def baseStart_4086583 : Nat := 118140960795 + 4086583 * 2 ^ 59
def prefixEnd_4086583 : Nat := 4983230072969 + 3 ^ 40 * 4086583 * 2
def baseEnd_4086583 : Nat := 2098381313492689958918653

theorem tailTrace_4086583 : CollatzResearch.WordTrace tailWord_4086583 prefixEnd_4086583 2098381313492689958918653 := by
  unfold tailWord_4086583
  simp only [CollatzResearch.WordTrace]
  refine ⟨149049926954015198656240403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99366617969343465770826935 149049926954015198656240403)
  ·
    refine ⟨223574890431022797984360605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 149049926954015198656240403 223574890431022797984360605)
    ·
      refine ⟨83840583911633549244135227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223574890431022797984360605 83840583911633549244135227)
      ·
        refine ⟨125760875867450323866202841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83840583911633549244135227 125760875867450323866202841)
        ·
          refine ⟨94320656900587742899652131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125760875867450323866202841 94320656900587742899652131)
          ·
            refine ⟨141480985350881614349478197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94320656900587742899652131 141480985350881614349478197)
            ·
              refine ⟨13263842376645151345263581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 141480985350881614349478197 13263842376645151345263581)
              ·
                refine ⟨4973940891241931754473843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13263842376645151345263581 4973940891241931754473843)
                ·
                  refine ⟨7460911336862897631710765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4973940891241931754473843 7460911336862897631710765)
                  ·
                    refine ⟨2797841751323586611891537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7460911336862897631710765 2797841751323586611891537)
                    ·
                      refine ⟨2098381313492689958918653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2797841751323586611891537 2098381313492689958918653)
                      ·
                        rfl

theorem cell23_4086583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 3, 1, 3, 2].length) (baseStart_4086583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4086583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4086583 prefixEnd_4086583 := by exact prefixLift 4086583
  have htrace : WordTrace (prefixWord ++ tailWord_4086583) baseStart_4086583 baseEnd_4086583 := by
    simpa [prefixWord, tailWord_4086583, baseEnd_4086583] using wordTrace_append hprefix tailTrace_4086583
  have hstable : (prefixWord ++ tailWord_4086583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4086583).length < 2 ^ (prefixWord ++ tailWord_4086583).sum := by decide
  have hdescent : baseEnd_4086583 < baseStart_4086583 := by decide
  rcases family_descends (prefixWord ++ tailWord_4086583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
