import V185TrunkScan23Chunk1115

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6610074 : List Nat := [3, 1, 1, 5, 1, 1, 2, 2, 2, 5]
def baseStart_6610074 : Nat := 118140960795 + 6610074 * 2 ^ 59
def prefixEnd_6610074 : Nat := 4983230072969 + 3 ^ 40 * 6610074 * 2
def baseEnd_6610074 : Nat := 1131381707929225429591943

theorem tailTrace_6610074 : CollatzResearch.WordTrace tailWord_6610074 prefixEnd_6610074 1131381707929225429591943 := by
  unfold tailWord_6610074
  simp only [CollatzResearch.WordTrace]
  refine ⟨60272301263709570901783319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160726136703225522404755517 60272301263709570901783319)
  ·
    refine ⟨90408451895564356352674979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60272301263709570901783319 90408451895564356352674979)
    ·
      refine ⟨135612677843346534529012469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90408451895564356352674979 135612677843346534529012469)
      ·
        refine ⟨12713688547813737612094919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 135612677843346534529012469 12713688547813737612094919)
        ·
          refine ⟨19070532821720606418142379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12713688547813737612094919 19070532821720606418142379)
          ·
            refine ⟨28605799232580909627213569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19070532821720606418142379 28605799232580909627213569)
            ·
              refine ⟨21454349424435682220410177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28605799232580909627213569 21454349424435682220410177)
              ·
                refine ⟨16090762068326761665307633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21454349424435682220410177 16090762068326761665307633)
                ·
                  refine ⟨12068071551245071248980725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16090762068326761665307633 12068071551245071248980725)
                  ·
                    refine ⟨1131381707929225429591943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12068071551245071248980725 1131381707929225429591943)
                    ·
                      rfl

theorem cell23_6610074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 2, 2, 5].length) (baseStart_6610074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6610074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6610074 prefixEnd_6610074 := by exact prefixLift 6610074
  have htrace : WordTrace (prefixWord ++ tailWord_6610074) baseStart_6610074 baseEnd_6610074 := by
    simpa [prefixWord, tailWord_6610074, baseEnd_6610074] using wordTrace_append hprefix tailTrace_6610074
  have hstable : (prefixWord ++ tailWord_6610074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6610074).length < 2 ^ (prefixWord ++ tailWord_6610074).sum := by decide
  have hdescent : baseEnd_6610074 < baseStart_6610074 := by decide
  rcases family_descends (prefixWord ++ tailWord_6610074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6610078 : List Nat := [4, 3, 1, 1, 2, 1, 4, 2, 5]
def baseStart_6610078 : Nat := 118140960795 + 6610078 * 2 ^ 59
def prefixEnd_6610078 : Nat := 4983230072969 + 3 ^ 40 * 6610078 * 2
def baseEnd_6610078 : Nat := 377127464190032697013979

theorem tailTrace_6610078 : CollatzResearch.WordTrace tailWord_6610078 prefixEnd_6610078 377127464190032697013979 := by
  unfold tailWord_6610078
  simp only [CollatzResearch.WordTrace]
  refine ⟨30136168868352974036284861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 160726233964549194860185925 30136168868352974036284861)
  ·
    refine ⟨11301063325632365263606823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30136168868352974036284861 11301063325632365263606823)
    ·
      refine ⟨16951594988448547895410235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11301063325632365263606823 16951594988448547895410235)
      ·
        refine ⟨25427392482672821843115353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16951594988448547895410235 25427392482672821843115353)
        ·
          refine ⟨19070544362004616382336515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25427392482672821843115353 19070544362004616382336515)
          ·
            refine ⟨28605816543006924573504773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19070544362004616382336515 28605816543006924573504773)
            ·
              refine ⟨5363590601813798357532145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28605816543006924573504773 5363590601813798357532145)
              ·
                refine ⟨4022692951360348768149109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5363590601813798357532145 4022692951360348768149109)
                ·
                  refine ⟨377127464190032697013979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4022692951360348768149109 377127464190032697013979)
                  ·
                    rfl

theorem cell23_6610078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 4, 2, 5].length) (baseStart_6610078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6610078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6610078 prefixEnd_6610078 := by exact prefixLift 6610078
  have htrace : WordTrace (prefixWord ++ tailWord_6610078) baseStart_6610078 baseEnd_6610078 := by
    simpa [prefixWord, tailWord_6610078, baseEnd_6610078] using wordTrace_append hprefix tailTrace_6610078
  have hstable : (prefixWord ++ tailWord_6610078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6610078).length < 2 ^ (prefixWord ++ tailWord_6610078).sum := by decide
  have hdescent : baseEnd_6610078 < baseStart_6610078 := by decide
  rcases family_descends (prefixWord ++ tailWord_6610078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6610204 : List Nat := [2, 2, 3, 1, 1, 1, 4, 2, 1, 1, 5]
def baseStart_6610204 : Nat := 118140960795 + 6610204 * 2 ^ 59
def prefixEnd_6610204 : Nat := 4983230072969 + 3 ^ 40 * 6610204 * 2
def baseEnd_6610204 : Nat := 3394211876272760780150231

theorem tailTrace_6610204 : CollatzResearch.WordTrace tailWord_6610204 prefixEnd_6610204 3394211876272760780150231 := by
  unfold tailWord_6610204
  simp only [CollatzResearch.WordTrace]
  refine ⟨120546973272183657904682833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160729297696244877206243777 120546973272183657904682833)
  ·
    refine ⟨90410229954137743428512125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120546973272183657904682833 90410229954137743428512125)
    ·
      refine ⟨33903836232801653785692047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90410229954137743428512125 33903836232801653785692047)
      ·
        refine ⟨50855754349202480678538071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33903836232801653785692047 50855754349202480678538071)
        ·
          refine ⟨76283631523803721017807107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50855754349202480678538071 76283631523803721017807107)
          ·
            refine ⟨114425447285705581526710661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76283631523803721017807107 114425447285705581526710661)
            ·
              refine ⟨21454771366069796536258249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 114425447285705581526710661 21454771366069796536258249)
              ·
                refine ⟨16091078524552347402193687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21454771366069796536258249 16091078524552347402193687)
                ·
                  refine ⟨24136617786828521103290531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16091078524552347402193687 24136617786828521103290531)
                  ·
                    refine ⟨36204926680242781654935797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24136617786828521103290531 36204926680242781654935797)
                    ·
                      refine ⟨3394211876272760780150231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36204926680242781654935797 3394211876272760780150231)
                      ·
                        rfl

theorem cell23_6610204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 2, 1, 1, 5].length) (baseStart_6610204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6610204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6610204 prefixEnd_6610204 := by exact prefixLift 6610204
  have htrace : WordTrace (prefixWord ++ tailWord_6610204) baseStart_6610204 baseEnd_6610204 := by
    simpa [prefixWord, tailWord_6610204, baseEnd_6610204] using wordTrace_append hprefix tailTrace_6610204
  have hstable : (prefixWord ++ tailWord_6610204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6610204).length < 2 ^ (prefixWord ++ tailWord_6610204).sum := by decide
  have hdescent : baseEnd_6610204 < baseStart_6610204 := by decide
  rcases family_descends (prefixWord ++ tailWord_6610204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6610211 : List Nat := [1, 1, 1, 4, 2, 4, 1, 3, 2, 4]
def baseStart_6610211 : Nat := 118140960795 + 6610211 * 2 ^ 59
def prefixEnd_6610211 : Nat := 4983230072969 + 3 ^ 40 * 6610211 * 2
def baseEnd_6610211 : Nat := 1131405156879114084254233

theorem tailTrace_6610211 : CollatzResearch.WordTrace tailWord_6610211 prefixEnd_6610211 1131405156879114084254233 := by
  unfold tailWord_6610211
  simp only [CollatzResearch.WordTrace]
  refine ⟨241094201855341956004870487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160729467903561304003246991 241094201855341956004870487)
  ·
    refine ⟨361641302783012934007305731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241094201855341956004870487 361641302783012934007305731)
    ·
      refine ⟨542461954174519401010958597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 361641302783012934007305731 542461954174519401010958597)
      ·
        refine ⟨101711616407722387689554737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 542461954174519401010958597 101711616407722387689554737)
        ·
          refine ⟨76283712305791790767166053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101711616407722387689554737 76283712305791790767166053)
          ·
            refine ⟨14303196057335960768843635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76283712305791790767166053 14303196057335960768843635)
            ·
              refine ⟨21454794086003941153265453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14303196057335960768843635 21454794086003941153265453)
              ·
                refine ⟨8045547782251477932474545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21454794086003941153265453 8045547782251477932474545)
                ·
                  refine ⟨6034160836688608449355909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8045547782251477932474545 6034160836688608449355909)
                  ·
                    refine ⟨1131405156879114084254233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6034160836688608449355909 1131405156879114084254233)
                    ·
                      rfl

theorem cell23_6610211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 3, 2, 4].length) (baseStart_6610211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6610211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6610211 prefixEnd_6610211 := by exact prefixLift 6610211
  have htrace : WordTrace (prefixWord ++ tailWord_6610211) baseStart_6610211 baseEnd_6610211 := by
    simpa [prefixWord, tailWord_6610211, baseEnd_6610211] using wordTrace_append hprefix tailTrace_6610211
  have hstable : (prefixWord ++ tailWord_6610211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6610211).length < 2 ^ (prefixWord ++ tailWord_6610211).sum := by decide
  have hdescent : baseEnd_6610211 < baseStart_6610211 := by decide
  rcases family_descends (prefixWord ++ tailWord_6610211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6610218 : List Nat := [3, 1, 4, 2, 1, 1, 3, 2, 1, 1, 4]
def baseStart_6610218 : Nat := 118140960795 + 6610218 * 2 ^ 59
def prefixEnd_6610218 : Nat := 4983230072969 + 3 ^ 40 * 6610218 * 2
def baseEnd_6610218 : Nat := 3394219065001923725375167

theorem tailTrace_6610218 : CollatzResearch.WordTrace tailWord_6610218 prefixEnd_6610218 3394219065001923725375167 := by
  unfold tailWord_6610218
  simp only [CollatzResearch.WordTrace]
  refine ⟨60273614291579149050093827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160729638110877730800250205 60273614291579149050093827)
  ·
    refine ⟨90410421437368723575140741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60273614291579149050093827 90410421437368723575140741)
    ·
      refine ⟨16951954019506635670338889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90410421437368723575140741 16951954019506635670338889)
      ·
        refine ⟨12713965514629976752754167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16951954019506635670338889 12713965514629976752754167)
        ·
          refine ⟨19070948271944965129131251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12713965514629976752754167 19070948271944965129131251)
          ·
            refine ⟨28606422407917447693696877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19070948271944965129131251 28606422407917447693696877)
            ·
              refine ⟨10727408402969042885136329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28606422407917447693696877 10727408402969042885136329)
              ·
                refine ⟨8045556302226782163852247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10727408402969042885136329 8045556302226782163852247)
                ·
                  refine ⟨12068334453340173245778371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8045556302226782163852247 12068334453340173245778371)
                  ·
                    refine ⟨18102501680010259868667557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12068334453340173245778371 18102501680010259868667557)
                    ·
                      refine ⟨3394219065001923725375167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18102501680010259868667557 3394219065001923725375167)
                      ·
                        rfl

theorem cell23_6610218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_6610218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6610218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6610218 prefixEnd_6610218 := by exact prefixLift 6610218
  have htrace : WordTrace (prefixWord ++ tailWord_6610218) baseStart_6610218 baseEnd_6610218 := by
    simpa [prefixWord, tailWord_6610218, baseEnd_6610218] using wordTrace_append hprefix tailTrace_6610218
  have hstable : (prefixWord ++ tailWord_6610218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6610218).length < 2 ^ (prefixWord ++ tailWord_6610218).sum := by decide
  have hdescent : baseEnd_6610218 < baseStart_6610218 := by decide
  rcases family_descends (prefixWord ++ tailWord_6610218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6610252 : List Nat := [2, 2, 1, 3, 2, 2, 4, 2, 1, 2, 2]
def baseStart_6610252 : Nat := 118140960795 + 6610252 * 2 ^ 59
def prefixEnd_6610252 : Nat := 4983230072969 + 3 ^ 40 * 6610252 * 2
def baseEnd_6610252 : Nat := 3394236523344176592350011

theorem tailTrace_6610252 : CollatzResearch.WordTrace tailWord_6610252 prefixEnd_6610252 3394236523344176592350011 := by
  unfold tailWord_6610252
  simp only [CollatzResearch.WordTrace]
  refine ⟨120547848624096710003556505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160730464832128946671408673 120547848624096710003556505)
  ·
    refine ⟨90410886468072532502667379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120547848624096710003556505 90410886468072532502667379)
    ·
      refine ⟨135616329702108798754001069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90410886468072532502667379 135616329702108798754001069)
      ·
        refine ⟨50856123638290799532750401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135616329702108798754001069 50856123638290799532750401)
        ·
          refine ⟨38142092728718099649562801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50856123638290799532750401 38142092728718099649562801)
          ·
            refine ⟨28606569546538574737172101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38142092728718099649562801 28606569546538574737172101)
            ·
              refine ⟨5363731789975982763219769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28606569546538574737172101 5363731789975982763219769)
              ·
                refine ⟨4022798842481987072414827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5363731789975982763219769 4022798842481987072414827)
                ·
                  refine ⟨6034198263722980608622241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4022798842481987072414827 6034198263722980608622241)
                  ·
                    refine ⟨4525648697792235456466681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6034198263722980608622241 4525648697792235456466681)
                    ·
                      refine ⟨3394236523344176592350011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4525648697792235456466681 3394236523344176592350011)
                      ·
                        rfl

theorem cell23_6610252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 4, 2, 1, 2, 2].length) (baseStart_6610252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6610252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6610252 prefixEnd_6610252 := by exact prefixLift 6610252
  have htrace : WordTrace (prefixWord ++ tailWord_6610252) baseStart_6610252 baseEnd_6610252 := by
    simpa [prefixWord, tailWord_6610252, baseEnd_6610252] using wordTrace_append hprefix tailTrace_6610252
  have hstable : (prefixWord ++ tailWord_6610252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6610252).length < 2 ^ (prefixWord ++ tailWord_6610252).sum := by decide
  have hdescent : baseEnd_6610252 < baseStart_6610252 := by decide
  rcases family_descends (prefixWord ++ tailWord_6610252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6610262 : List Nat := [5, 2, 3, 1, 1, 1, 2, 1, 1, 6]
def baseStart_6610262 : Nat := 118140960795 + 6610262 * 2 ^ 59
def prefixEnd_6610262 : Nat := 4983230072969 + 3 ^ 40 * 6610262 * 2
def baseEnd_6610262 : Nat := 1131413886050240517741655

theorem tailTrace_6610262 : CollatzResearch.WordTrace tailWord_6610262 prefixEnd_6610262 1131413886050240517741655 := by
  unfold tailWord_6610262
  simp only [CollatzResearch.WordTrace]
  refine ⟨15068503873634824482186065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 160730707985438127809984693 15068503873634824482186065)
  ·
    refine ⟨11301377905226118361639549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15068503873634824482186065 11301377905226118361639549)
    ·
      refine ⟨4238016714459794385614831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11301377905226118361639549 4238016714459794385614831)
      ·
        refine ⟨6357025071689691578422247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4238016714459794385614831 6357025071689691578422247)
        ·
          refine ⟨9535537607534537367633371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6357025071689691578422247 9535537607534537367633371)
          ·
            refine ⟨14303306411301806051450057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9535537607534537367633371 14303306411301806051450057)
            ·
              refine ⟨10727479808476354538587543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14303306411301806051450057 10727479808476354538587543)
              ·
                refine ⟨16091219712714531807881315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10727479808476354538587543 16091219712714531807881315)
                ·
                  refine ⟨24136829569071797711821973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16091219712714531807881315 24136829569071797711821973)
                  ·
                    refine ⟨1131413886050240517741655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24136829569071797711821973 1131413886050240517741655)
                    ·
                      rfl

theorem cell23_6610262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_6610262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6610262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6610262 prefixEnd_6610262 := by exact prefixLift 6610262
  have htrace : WordTrace (prefixWord ++ tailWord_6610262) baseStart_6610262 baseEnd_6610262 := by
    simpa [prefixWord, tailWord_6610262, baseEnd_6610262] using wordTrace_append hprefix tailTrace_6610262
  have hstable : (prefixWord ++ tailWord_6610262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6610262).length < 2 ^ (prefixWord ++ tailWord_6610262).sum := by decide
  have hdescent : baseEnd_6610262 < baseStart_6610262 := by decide
  rcases family_descends (prefixWord ++ tailWord_6610262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6610269 : List Nat := [1, 4, 5, 1, 1, 1, 1, 2, 3, 2, 2]
def baseStart_6610269 : Nat := 118140960795 + 6610269 * 2 ^ 59
def prefixEnd_6610269 : Nat := 4983230072969 + 3 ^ 40 * 6610269 * 2
def baseEnd_6610269 : Nat := 3394245252515303025837433

theorem tailTrace_6610269 : CollatzResearch.WordTrace tailWord_6610269 prefixEnd_6610269 3394245252515303025837433 := by
  unfold tailWord_6610269
  simp only [CollatzResearch.WordTrace]
  refine ⟨241096317289131831910481861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160730878192754554606987907 241096317289131831910481861)
  ·
    refine ⟨45205559491712218483215349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 241096317289131831910481861 45205559491712218483215349)
    ·
      refine ⟨4238021202348020482801439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 45205559491712218483215349 4238021202348020482801439)
      ·
        refine ⟨6357031803522030724202159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4238021202348020482801439 6357031803522030724202159)
        ·
          refine ⟨9535547705283046086303239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6357031803522030724202159 9535547705283046086303239)
          ·
            refine ⟨14303321557924569129454859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9535547705283046086303239 14303321557924569129454859)
            ·
              refine ⟨21454982336886853694182289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14303321557924569129454859 21454982336886853694182289)
              ·
                refine ⟨16091236752665140270636717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21454982336886853694182289 16091236752665140270636717)
                ·
                  refine ⟨6034213782249427601488769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16091236752665140270636717 6034213782249427601488769)
                  ·
                    refine ⟨4525660336687070701116577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6034213782249427601488769 4525660336687070701116577)
                    ·
                      refine ⟨3394245252515303025837433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4525660336687070701116577 3394245252515303025837433)
                      ·
                        rfl

theorem cell23_6610269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_6610269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6610269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6610269 prefixEnd_6610269 := by exact prefixLift 6610269
  have htrace : WordTrace (prefixWord ++ tailWord_6610269) baseStart_6610269 baseEnd_6610269 := by
    simpa [prefixWord, tailWord_6610269, baseEnd_6610269] using wordTrace_append hprefix tailTrace_6610269
  have hstable : (prefixWord ++ tailWord_6610269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6610269).length < 2 ^ (prefixWord ++ tailWord_6610269).sum := by decide
  have hdescent : baseEnd_6610269 < baseStart_6610269 := by decide
  rcases family_descends (prefixWord ++ tailWord_6610269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6610302 : List Nat := [4, 2, 3, 2, 1, 1, 1, 1, 4, 1, 3]
def baseStart_6610302 : Nat := 118140960795 + 6610302 * 2 ^ 59
def prefixEnd_6610302 : Nat := 4983230072969 + 3 ^ 40 * 6610302 * 2
def baseEnd_6610302 : Nat := 3394262197376901396724781

theorem tailTrace_6610302 : CollatzResearch.WordTrace tailWord_6610302 prefixEnd_6610302 3394262197376901396724781 := by
  unfold tailWord_6610302
  simp only [CollatzResearch.WordTrace]
  refine ⟨30137190112251534818304145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 160731680598674852364288773 30137190112251534818304145)
  ·
    refine ⟨22602892584188651113728109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30137190112251534818304145 22602892584188651113728109)
    ·
      refine ⟨8476084719070744167648041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22602892584188651113728109 8476084719070744167648041)
      ·
        refine ⟨6357063539303058125736031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8476084719070744167648041 6357063539303058125736031)
        ·
          refine ⟨9535595308954587188604047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6357063539303058125736031 9535595308954587188604047)
          ·
            refine ⟨14303392963431880782906071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9535595308954587188604047 14303392963431880782906071)
            ·
              refine ⟨21455089445147821174359107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14303392963431880782906071 21455089445147821174359107)
              ·
                refine ⟨32182634167721731761538661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21455089445147821174359107 32182634167721731761538661)
                ·
                  refine ⟨6034243906447824705288499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32182634167721731761538661 6034243906447824705288499)
                  ·
                    refine ⟨9051365859671737057932749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6034243906447824705288499 9051365859671737057932749)
                    ·
                      refine ⟨3394262197376901396724781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9051365859671737057932749 3394262197376901396724781)
                      ·
                        rfl

theorem cell23_6610302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_6610302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6610302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6610302 prefixEnd_6610302 := by exact prefixLift 6610302
  have htrace : WordTrace (prefixWord ++ tailWord_6610302) baseStart_6610302 baseEnd_6610302 := by
    simpa [prefixWord, tailWord_6610302, baseEnd_6610302] using wordTrace_append hprefix tailTrace_6610302
  have hstable : (prefixWord ++ tailWord_6610302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6610302).length < 2 ^ (prefixWord ++ tailWord_6610302).sum := by decide
  have hdescent : baseEnd_6610302 < baseStart_6610302 := by decide
  rcases family_descends (prefixWord ++ tailWord_6610302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6610370 : List Nat := [3, 5, 2, 1, 2, 1, 2, 1, 2, 1, 3]
def baseStart_6610370 : Nat := 118140960795 + 6610370 * 2 ^ 59
def prefixEnd_6610370 : Nat := 4983230072969 + 3 ^ 40 * 6610370 * 2
def baseEnd_6610370 : Nat := 3394297114061407130674469

theorem tailTrace_6610370 : CollatzResearch.WordTrace tailWord_6610370 prefixEnd_6610370 3394297114061407130674469 := by
  unfold tailWord_6610370
  simp only [CollatzResearch.WordTrace]
  refine ⟨60275000265441481539977141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160733334041177284106605709 60275000265441481539977141)
  ·
    refine ⟨5650781274885138894372857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 60275000265441481539977141 5650781274885138894372857)
    ·
      refine ⟨4238085956163854170779643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5650781274885138894372857 4238085956163854170779643)
      ·
        refine ⟨6357128934245781256169465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4238085956163854170779643 6357128934245781256169465)
        ·
          refine ⟨4767846700684335942127099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6357128934245781256169465 4767846700684335942127099)
          ·
            refine ⟨7151770051026503913190649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4767846700684335942127099 7151770051026503913190649)
            ·
              refine ⟨5363827538269877934892987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7151770051026503913190649 5363827538269877934892987)
              ·
                refine ⟨8045741307404816902339481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5363827538269877934892987 8045741307404816902339481)
                ·
                  refine ⟨6034305980553612676754611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8045741307404816902339481 6034305980553612676754611)
                  ·
                    refine ⟨9051458970830419015131917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6034305980553612676754611 9051458970830419015131917)
                    ·
                      refine ⟨3394297114061407130674469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9051458970830419015131917 3394297114061407130674469)
                      ·
                        rfl

theorem cell23_6610370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_6610370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6610370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6610370 prefixEnd_6610370 := by exact prefixLift 6610370
  have htrace : WordTrace (prefixWord ++ tailWord_6610370) baseStart_6610370 baseEnd_6610370 := by
    simpa [prefixWord, tailWord_6610370, baseEnd_6610370] using wordTrace_append hprefix tailTrace_6610370
  have hstable : (prefixWord ++ tailWord_6610370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6610370).length < 2 ^ (prefixWord ++ tailWord_6610370).sum := by decide
  have hdescent : baseEnd_6610370 < baseStart_6610370 := by decide
  rcases family_descends (prefixWord ++ tailWord_6610370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6610391 : List Nat := [1, 1, 3, 2, 1, 1, 1, 6, 3, 4]
def baseStart_6610391 : Nat := 118140960795 + 6610391 * 2 ^ 59
def prefixEnd_6610391 : Nat := 4983230072969 + 3 ^ 40 * 6610391 * 2
def baseEnd_6610391 : Nat := 1131435965718383849503957

theorem tailTrace_6610391 : CollatzResearch.WordTrace tailWord_6610391 prefixEnd_6610391 1131435965718383849503957 := by
  unfold tailWord_6610391
  simp only [CollatzResearch.WordTrace]
  refine ⟨241100766994689846746423027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160733844663126564497615351 241100766994689846746423027)
  ·
    refine ⟨361651150492034770119634541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241100766994689846746423027 361651150492034770119634541)
    ·
      refine ⟨135619181434513038794862953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 361651150492034770119634541 135619181434513038794862953)
      ·
        refine ⟨101714386075884779096147215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135619181434513038794862953 101714386075884779096147215)
        ·
          refine ⟨152571579113827168644220823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101714386075884779096147215 152571579113827168644220823)
          ·
            refine ⟨228857368670740752966331235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152571579113827168644220823 228857368670740752966331235)
            ·
              refine ⟨343286053006111129449496853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 228857368670740752966331235 343286053006111129449496853)
              ·
                refine ⟨16091533734661459192945165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 343286053006111129449496853 16091533734661459192945165)
                ·
                  refine ⟨6034325150498047197354437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16091533734661459192945165 6034325150498047197354437)
                  ·
                    refine ⟨1131435965718383849503957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6034325150498047197354437 1131435965718383849503957)
                    ·
                      rfl

theorem cell23_6610391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 6, 3, 4].length) (baseStart_6610391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6610391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6610391 prefixEnd_6610391 := by exact prefixLift 6610391
  have htrace : WordTrace (prefixWord ++ tailWord_6610391) baseStart_6610391 baseEnd_6610391 := by
    simpa [prefixWord, tailWord_6610391, baseEnd_6610391] using wordTrace_append hprefix tailTrace_6610391
  have hstable : (prefixWord ++ tailWord_6610391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6610391).length < 2 ^ (prefixWord ++ tailWord_6610391).sum := by decide
  have hdescent : baseEnd_6610391 < baseStart_6610391 := by decide
  rcases family_descends (prefixWord ++ tailWord_6610391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6610404 : List Nat := [2, 3, 1, 1, 1, 1, 1, 3, 10]
def baseStart_6610404 : Nat := 118140960795 + 6610404 * 2 ^ 59
def prefixEnd_6610404 : Nat := 4983230072969 + 3 ^ 40 * 6610404 * 2
def baseEnd_6610404 : Nat := 377146063600406666405479

theorem tailTrace_6610404 : CollatzResearch.WordTrace tailWord_6610404 prefixEnd_6610404 377146063600406666405479 := by
  unfold tailWord_6610404
  simp only [CollatzResearch.WordTrace]
  refine ⟨120550620571821374983323133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160734160762428499977764177 120550620571821374983323133)
  ·
    refine ⟨45206482714433015618746175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120550620571821374983323133 45206482714433015618746175)
    ·
      refine ⟨67809724071649523428119263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45206482714433015618746175 67809724071649523428119263)
      ·
        refine ⟨101714586107474285142178895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67809724071649523428119263 101714586107474285142178895)
        ·
          refine ⟨152571879161211427713268343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101714586107474285142178895 152571879161211427713268343)
          ·
            refine ⟨228857818741817141569902515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152571879161211427713268343 228857818741817141569902515)
            ·
              refine ⟨343286728112725712354853773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 228857818741817141569902515 343286728112725712354853773)
              ·
                refine ⟨128732523042272142133070165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 343286728112725712354853773 128732523042272142133070165)
                ·
                  refine ⟨377146063600406666405479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 128732523042272142133070165 377146063600406666405479)
                  ·
                    rfl

theorem cell23_6610404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 3, 10].length) (baseStart_6610404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6610404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6610404 prefixEnd_6610404 := by exact prefixLift 6610404
  have htrace : WordTrace (prefixWord ++ tailWord_6610404) baseStart_6610404 baseEnd_6610404 := by
    simpa [prefixWord, tailWord_6610404, baseEnd_6610404] using wordTrace_append hprefix tailTrace_6610404
  have hstable : (prefixWord ++ tailWord_6610404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6610404).length < 2 ^ (prefixWord ++ tailWord_6610404).sum := by decide
  have hdescent : baseEnd_6610404 < baseStart_6610404 := by decide
  rcases family_descends (prefixWord ++ tailWord_6610404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6610451 : List Nat := [1, 1, 1, 2, 1, 6, 2, 1, 3, 5]
def baseStart_6610451 : Nat := 118140960795 + 6610451 * 2 ^ 59
def prefixEnd_6610451 : Nat := 4983230072969 + 3 ^ 40 * 6610451 * 2
def baseEnd_6610451 : Nat := 1131446235331473771253865

theorem tailTrace_6610451 : CollatzResearch.WordTrace tailWord_6610451 prefixEnd_6610451 1131446235331473771253865 := by
  unfold tailWord_6610451
  simp only [CollatzResearch.WordTrace]
  refine ⟨241102955374472476993607207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160735303582981651329071471 241102955374472476993607207)
  ·
    refine ⟨361654433061708715490410811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241102955374472476993607207 361654433061708715490410811)
    ·
      refine ⟨542481649592563073235616217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 361654433061708715490410811 542481649592563073235616217)
      ·
        refine ⟨406861237194422304926712163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 542481649592563073235616217 406861237194422304926712163)
        ·
          refine ⟨610291855791633457390068245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 406861237194422304926712163 610291855791633457390068245)
          ·
            refine ⟨28607430740232818315159449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 610291855791633457390068245 28607430740232818315159449)
            ·
              refine ⟨21455573055174613736369587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28607430740232818315159449 21455573055174613736369587)
              ·
                refine ⟨32183359582761920604554381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21455573055174613736369587 32183359582761920604554381)
                ·
                  refine ⟨12068759843535720226707893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32183359582761920604554381 12068759843535720226707893)
                  ·
                    refine ⟨1131446235331473771253865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12068759843535720226707893 1131446235331473771253865)
                    ·
                      rfl

theorem cell23_6610451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 1, 3, 5].length) (baseStart_6610451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6610451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6610451 prefixEnd_6610451 := by exact prefixLift 6610451
  have htrace : WordTrace (prefixWord ++ tailWord_6610451) baseStart_6610451 baseEnd_6610451 := by
    simpa [prefixWord, tailWord_6610451, baseEnd_6610451] using wordTrace_append hprefix tailTrace_6610451
  have hstable : (prefixWord ++ tailWord_6610451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6610451).length < 2 ^ (prefixWord ++ tailWord_6610451).sum := by decide
  have hdescent : baseEnd_6610451 < baseStart_6610451 := by decide
  rcases family_descends (prefixWord ++ tailWord_6610451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6610472 : List Nat := [2, 1, 5, 2, 3, 1, 1, 2, 6]
def baseStart_6610472 : Nat := 118140960795 + 6610472 * 2 ^ 59
def prefixEnd_6610472 : Nat := 4983230072969 + 3 ^ 40 * 6610472 * 2
def baseEnd_6610472 : Nat := 377149943232018414622111

theorem tailTrace_6610472 : CollatzResearch.WordTrace tailWord_6610472 prefixEnd_6610472 377149943232018414622111 := by
  unfold tailWord_6610472
  simp only [CollatzResearch.WordTrace]
  refine ⟨120551860653698198790060835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160735814204930931720081113 120551860653698198790060835)
  ·
    refine ⟨180827790980547298185091253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120551860653698198790060835 180827790980547298185091253)
    ·
      refine ⟨16952605404426309204852305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 180827790980547298185091253 16952605404426309204852305)
      ·
        refine ⟨12714454053319731903639229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16952605404426309204852305 12714454053319731903639229)
        ·
          refine ⟨4767920269994899463864711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12714454053319731903639229 4767920269994899463864711)
          ·
            refine ⟨7151880404992349195797067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4767920269994899463864711 7151880404992349195797067)
            ·
              refine ⟨10727820607488523793695601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7151880404992349195797067 10727820607488523793695601)
              ·
                refine ⟨8045865455616392845271701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10727820607488523793695601 8045865455616392845271701)
                ·
                  refine ⟨377149943232018414622111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8045865455616392845271701 377149943232018414622111)
                  ·
                    rfl

theorem cell23_6610472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 1, 2, 6].length) (baseStart_6610472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6610472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6610472 prefixEnd_6610472 := by exact prefixLift 6610472
  have htrace : WordTrace (prefixWord ++ tailWord_6610472) baseStart_6610472 baseEnd_6610472 := by
    simpa [prefixWord, tailWord_6610472, baseEnd_6610472] using wordTrace_append hprefix tailTrace_6610472
  have hstable : (prefixWord ++ tailWord_6610472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6610472).length < 2 ^ (prefixWord ++ tailWord_6610472).sum := by decide
  have hdescent : baseEnd_6610472 < baseStart_6610472 := by decide
  rcases family_descends (prefixWord ++ tailWord_6610472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6610501 : List Nat := [1, 3, 1, 1, 1, 4, 3, 1, 1, 1, 6]
def baseStart_6610501 : Nat := 118140960795 + 6610501 * 2 ^ 59
def prefixEnd_6610501 : Nat := 4983230072969 + 3 ^ 40 * 6610501 * 2
def baseEnd_6610501 : Nat := 3394364380027146118136365

theorem tailTrace_6610501 : CollatzResearch.WordTrace tailWord_6610501 prefixEnd_6610501 3394364380027146118136365 := by
  unfold tailWord_6610501
  simp only [CollatzResearch.WordTrace]
  refine ⟨241104779024291335532927357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160736519349527557021951571 241104779024291335532927357)
  ·
    refine ⟨90414292134109250824847759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 241104779024291335532927357 90414292134109250824847759)
    ·
      refine ⟨135621438201163876237271639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90414292134109250824847759 135621438201163876237271639)
      ·
        refine ⟨203432157301745814355907459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135621438201163876237271639 203432157301745814355907459)
        ·
          refine ⟨305148235952618721533861189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203432157301745814355907459 305148235952618721533861189)
          ·
            refine ⟨57215294241116010287598973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 305148235952618721533861189 57215294241116010287598973)
            ·
              refine ⟨21455735340418503857849615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57215294241116010287598973 21455735340418503857849615)
              ·
                refine ⟨32183603010627755786774423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21455735340418503857849615 32183603010627755786774423)
                ·
                  refine ⟨48275404515941633680161635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32183603010627755786774423 48275404515941633680161635)
                  ·
                    refine ⟨72413106773912450520242453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48275404515941633680161635 72413106773912450520242453)
                    ·
                      refine ⟨3394364380027146118136365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72413106773912450520242453 3394364380027146118136365)
                      ·
                        rfl

theorem cell23_6610501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 1, 1, 1, 6].length) (baseStart_6610501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6610501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6610501 prefixEnd_6610501 := by exact prefixLift 6610501
  have htrace : WordTrace (prefixWord ++ tailWord_6610501) baseStart_6610501 baseEnd_6610501 := by
    simpa [prefixWord, tailWord_6610501, baseEnd_6610501] using wordTrace_append hprefix tailTrace_6610501
  have hstable : (prefixWord ++ tailWord_6610501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6610501).length < 2 ^ (prefixWord ++ tailWord_6610501).sum := by decide
  have hdescent : baseEnd_6610501 < baseStart_6610501 := by decide
  rcases family_descends (prefixWord ++ tailWord_6610501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6610549 : List Nat := [1, 3, 4, 2, 1, 3, 2, 1, 2, 4]
def baseStart_6610549 : Nat := 118140960795 + 6610549 * 2 ^ 59
def prefixEnd_6610549 : Nat := 4983230072969 + 3 ^ 40 * 6610549 * 2
def baseEnd_6610549 : Nat := 1131463009032853976778715

theorem tailTrace_6610549 : CollatzResearch.WordTrace tailWord_6610549 prefixEnd_6610549 1131463009032853976778715 := by
  unfold tailWord_6610549
  simp only [CollatzResearch.WordTrace]
  refine ⟨241106529728117439730674701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160737686485411626487116467 241106529728117439730674701)
  ·
    refine ⟨90414948648044039899003013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 241106529728117439730674701 90414948648044039899003013)
    ·
      refine ⟨16952802871508257481063065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90414948648044039899003013 16952802871508257481063065)
      ·
        refine ⟨12714602153631193110797299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16952802871508257481063065 12714602153631193110797299)
        ·
          refine ⟨19071903230446789666195949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12714602153631193110797299 19071903230446789666195949)
          ·
            refine ⟨7151963711417546124823481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19071903230446789666195949 7151963711417546124823481)
            ·
              refine ⟨5363972783563159593617611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7151963711417546124823481 5363972783563159593617611)
              ·
                refine ⟨8045959175344739390426417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5363972783563159593617611 8045959175344739390426417)
                ·
                  refine ⟨6034469381508554542819813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8045959175344739390426417 6034469381508554542819813)
                  ·
                    refine ⟨1131463009032853976778715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6034469381508554542819813 1131463009032853976778715)
                    ·
                      rfl

theorem cell23_6610549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 2, 1, 2, 4].length) (baseStart_6610549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6610549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6610549 prefixEnd_6610549 := by exact prefixLift 6610549
  have htrace : WordTrace (prefixWord ++ tailWord_6610549) baseStart_6610549 baseEnd_6610549 := by
    simpa [prefixWord, tailWord_6610549, baseEnd_6610549] using wordTrace_append hprefix tailTrace_6610549
  have hstable : (prefixWord ++ tailWord_6610549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6610549).length < 2 ^ (prefixWord ++ tailWord_6610549).sum := by decide
  have hdescent : baseEnd_6610549 < baseStart_6610549 := by decide
  rcases family_descends (prefixWord ++ tailWord_6610549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6610555 : List Nat := [1, 1, 1, 1, 1, 4, 5, 3, 2, 1, 3]
def baseStart_6610555 : Nat := 118140960795 + 6610555 * 2 ^ 59
def prefixEnd_6610555 : Nat := 4983230072969 + 3 ^ 40 * 6610555 * 2
def baseEnd_6610555 : Nat := 3394392107982488906861117

theorem tailTrace_6610555 : CollatzResearch.WordTrace tailWord_6610555 prefixEnd_6610555 3394392107982488906861117 := by
  unfold tailWord_6610555
  simp only [CollatzResearch.WordTrace]
  refine ⟨241106748566095702755393119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160737832377397135170262079 241106748566095702755393119)
  ·
    refine ⟨361660122849143554133089679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241106748566095702755393119 361660122849143554133089679)
    ·
      refine ⟨542490184273715331199634519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 361660122849143554133089679 542490184273715331199634519)
      ·
        refine ⟨813735276410572996799451779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 542490184273715331199634519 813735276410572996799451779)
        ·
          refine ⟨1220602914615859495199177669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 813735276410572996799451779 1220602914615859495199177669)
          ·
            refine ⟨228863046490473655349845813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1220602914615859495199177669 228863046490473655349845813)
            ·
              refine ⟨21455910608481905189048045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 228863046490473655349845813 21455910608481905189048045)
              ·
                refine ⟨8045966478180714445893017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21455910608481905189048045 8045966478180714445893017)
                ·
                  refine ⟨6034474858635535834419763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8045966478180714445893017 6034474858635535834419763)
                  ·
                    refine ⟨9051712287953303751629645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6034474858635535834419763 9051712287953303751629645)
                    ·
                      refine ⟨3394392107982488906861117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9051712287953303751629645 3394392107982488906861117)
                      ·
                        rfl

theorem cell23_6610555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 3, 2, 1, 3].length) (baseStart_6610555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6610555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6610555 prefixEnd_6610555 := by exact prefixLift 6610555
  have htrace : WordTrace (prefixWord ++ tailWord_6610555) baseStart_6610555 baseEnd_6610555 := by
    simpa [prefixWord, tailWord_6610555, baseEnd_6610555] using wordTrace_append hprefix tailTrace_6610555
  have hstable : (prefixWord ++ tailWord_6610555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6610555).length < 2 ^ (prefixWord ++ tailWord_6610555).sum := by decide
  have hdescent : baseEnd_6610555 < baseStart_6610555 := by decide
  rcases family_descends (prefixWord ++ tailWord_6610555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6610565 : List Nat := [1, 3, 1, 1, 4, 1, 3, 1, 3, 3, 2]
def baseStart_6610565 : Nat := 118140960795 + 6610565 * 2 ^ 59
def prefixEnd_6610565 : Nat := 4983230072969 + 3 ^ 40 * 6610565 * 2
def baseEnd_6610565 : Nat := 3394397242789033867736071

theorem tailTrace_6610565 : CollatzResearch.WordTrace tailWord_6610565 prefixEnd_6610565 3394397242789033867736071 := by
  unfold tailWord_6610565
  simp only [CollatzResearch.WordTrace]
  refine ⟨241107113296059474463257149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160738075530706316308838099 241107113296059474463257149)
  ·
    refine ⟨90415167486022302923721431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 241107113296059474463257149 90415167486022302923721431)
    ·
      refine ⟨135622751229033454385582147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90415167486022302923721431 135622751229033454385582147)
      ·
        refine ⟨203434126843550181578373221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135622751229033454385582147 203434126843550181578373221)
        ·
          refine ⟨38143898783165659045944979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 203434126843550181578373221 38143898783165659045944979)
          ·
            refine ⟨57215848174748488568917469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38143898783165659045944979 57215848174748488568917469)
            ·
              refine ⟨21455943065530683213344051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57215848174748488568917469 21455943065530683213344051)
              ·
                refine ⟨32183914598296024820016077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21455943065530683213344051 32183914598296024820016077)
                ·
                  refine ⟨12068967974361009307506029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32183914598296024820016077 12068967974361009307506029)
                  ·
                    refine ⟨4525862990385378490314761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12068967974361009307506029 4525862990385378490314761)
                    ·
                      refine ⟨3394397242789033867736071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4525862990385378490314761 3394397242789033867736071)
                      ·
                        rfl

theorem cell23_6610565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 1, 3, 3, 2].length) (baseStart_6610565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6610565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6610565 prefixEnd_6610565 := by exact prefixLift 6610565
  have htrace : WordTrace (prefixWord ++ tailWord_6610565) baseStart_6610565 baseEnd_6610565 := by
    simpa [prefixWord, tailWord_6610565, baseEnd_6610565] using wordTrace_append hprefix tailTrace_6610565
  have hstable : (prefixWord ++ tailWord_6610565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6610565).length < 2 ^ (prefixWord ++ tailWord_6610565).sum := by decide
  have hdescent : baseEnd_6610565 < baseStart_6610565 := by decide
  rcases family_descends (prefixWord ++ tailWord_6610565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6610618 : List Nat := [3, 1, 1, 1, 2, 5, 1, 2, 7]
def baseStart_6610618 : Nat := 118140960795 + 6610618 * 2 ^ 59
def prefixEnd_6610618 : Nat := 4983230072969 + 3 ^ 40 * 6610618 * 2
def baseEnd_6610618 : Nat := 377158273029302462263703

theorem tailTrace_6610618 : CollatzResearch.WordTrace tailWord_6610618 prefixEnd_6610618 377158273029302462263703 := by
  unfold tailWord_6610618
  simp only [CollatzResearch.WordTrace]
  refine ⟨60277261591216866128734127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160739364243244976343291005 60277261591216866128734127)
  ·
    refine ⟨90415892386825299193101191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60277261591216866128734127 90415892386825299193101191)
    ·
      refine ⟨135623838580237948789651787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90415892386825299193101191 135623838580237948789651787)
      ·
        refine ⟨203435757870356923184477681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135623838580237948789651787 203435757870356923184477681)
        ·
          refine ⟨152576818402767692388358261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 203435757870356923184477681 152576818402767692388358261)
          ·
            refine ⟨14304076725259471161408587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 152576818402767692388358261 14304076725259471161408587)
            ·
              refine ⟨21456115087889206742112881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14304076725259471161408587 21456115087889206742112881)
              ·
                refine ⟨16092086315916905056584661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21456115087889206742112881 16092086315916905056584661)
                ·
                  refine ⟨377158273029302462263703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16092086315916905056584661 377158273029302462263703)
                  ·
                    rfl

theorem cell23_6610618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 2, 7].length) (baseStart_6610618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6610618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6610618 prefixEnd_6610618 := by exact prefixLift 6610618
  have htrace : WordTrace (prefixWord ++ tailWord_6610618) baseStart_6610618 baseEnd_6610618 := by
    simpa [prefixWord, tailWord_6610618, baseEnd_6610618] using wordTrace_append hprefix tailTrace_6610618
  have hstable : (prefixWord ++ tailWord_6610618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6610618).length < 2 ^ (prefixWord ++ tailWord_6610618).sum := by decide
  have hdescent : baseEnd_6610618 < baseStart_6610618 := by decide
  rcases family_descends (prefixWord ++ tailWord_6610618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6610648 : List Nat := [2, 1, 2, 2, 3, 1, 2, 1, 4, 5]
def baseStart_6610648 : Nat := 118140960795 + 6610648 * 2 ^ 59
def prefixEnd_6610648 : Nat := 4983230072969 + 3 ^ 40 * 6610648 * 2
def baseEnd_6610648 : Nat := 1131479953894452347666063

theorem tailTrace_6610648 : CollatzResearch.WordTrace tailWord_6610648 prefixEnd_6610648 1131479953894452347666063 := by
  unfold tailWord_6610648
  simp only [CollatzResearch.WordTrace]
  refine ⟨120555070277379389819264299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160740093703172519759019065 120555070277379389819264299)
  ·
    refine ⟨180832605416069084728896449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120555070277379389819264299 180832605416069084728896449)
    ·
      refine ⟨135624454062051813546672337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180832605416069084728896449 135624454062051813546672337)
      ·
        refine ⟨101718340546538860160004253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135624454062051813546672337 101718340546538860160004253)
        ·
          refine ⟨38144377704952072560001595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101718340546538860160004253 38144377704952072560001595)
          ·
            refine ⟨57216566557428108840002393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38144377704952072560001595 57216566557428108840002393)
            ·
              refine ⟨42912424918071081630001795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57216566557428108840002393 42912424918071081630001795)
              ·
                refine ⟨64368637377106622445002693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42912424918071081630001795 64368637377106622445002693)
                ·
                  refine ⟨12069119508207491708438005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64368637377106622445002693 12069119508207491708438005)
                  ·
                    refine ⟨1131479953894452347666063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12069119508207491708438005 1131479953894452347666063)
                    ·
                      rfl

theorem cell23_6610648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 1, 4, 5].length) (baseStart_6610648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6610648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6610648 prefixEnd_6610648 := by exact prefixLift 6610648
  have htrace : WordTrace (prefixWord ++ tailWord_6610648) baseStart_6610648 baseEnd_6610648 := by
    simpa [prefixWord, tailWord_6610648, baseEnd_6610648] using wordTrace_append hprefix tailTrace_6610648
  have hstable : (prefixWord ++ tailWord_6610648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6610648).length < 2 ^ (prefixWord ++ tailWord_6610648).sum := by decide
  have hdescent : baseEnd_6610648 < baseStart_6610648 := by decide
  rcases family_descends (prefixWord ++ tailWord_6610648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6610651 : List Nat := [1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 8]
def baseStart_6610651 : Nat := 118140960795 + 6610651 * 2 ^ 59
def prefixEnd_6610651 : Nat := 4983230072969 + 3 ^ 40 * 6610651 * 2
def baseEnd_6610651 : Nat := 3394441402125320531260675

theorem tailTrace_6610651 : CollatzResearch.WordTrace tailWord_6610651 prefixEnd_6610651 3394441402125320531260675 := by
  unfold tailWord_6610651
  simp only [CollatzResearch.WordTrace]
  refine ⟨241110249973747911150887807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160740166649165274100591871 241110249973747911150887807)
  ·
    refine ⟨361665374960621866726331711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241110249973747911150887807 361665374960621866726331711)
    ·
      refine ⟨542498062440932800089497567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 361665374960621866726331711 542498062440932800089497567)
      ·
        refine ⟨813747093661399200134246351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 542498062440932800089497567 813747093661399200134246351)
        ·
          refine ⟨1220620640492098800201369527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 813747093661399200134246351 1220620640492098800201369527)
          ·
            refine ⟨1830930960738148200302054291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1220620640492098800201369527 1830930960738148200302054291)
            ·
              refine ⟨2746396441107222300453081437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1830930960738148200302054291 2746396441107222300453081437)
              ·
                refine ⟨1029898665415208362669905539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2746396441107222300453081437 1029898665415208362669905539)
                ·
                  refine ⟨1544847998122812544004858309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1029898665415208362669905539 1544847998122812544004858309)
                  ·
                    refine ⟨289658999648027352000910933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1544847998122812544004858309 289658999648027352000910933)
                    ·
                      refine ⟨3394441402125320531260675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 289658999648027352000910933 3394441402125320531260675)
                      ·
                        rfl

theorem cell23_6610651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 8].length) (baseStart_6610651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6610651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6610651 prefixEnd_6610651 := by exact prefixLift 6610651
  have htrace : WordTrace (prefixWord ++ tailWord_6610651) baseStart_6610651 baseEnd_6610651 := by
    simpa [prefixWord, tailWord_6610651, baseEnd_6610651] using wordTrace_append hprefix tailTrace_6610651
  have hstable : (prefixWord ++ tailWord_6610651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6610651).length < 2 ^ (prefixWord ++ tailWord_6610651).sum := by decide
  have hdescent : baseEnd_6610651 < baseStart_6610651 := by decide
  rcases family_descends (prefixWord ++ tailWord_6610651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6610652 : List Nat := [2, 2, 5, 1, 2, 1, 2, 1, 7]
def baseStart_6610652 : Nat := 118140960795 + 6610652 * 2 ^ 59
def prefixEnd_6610652 : Nat := 4983230072969 + 3 ^ 40 * 6610652 * 2
def baseEnd_6610652 : Nat := 377160212845108336372019

theorem tailTrace_6610652 : CollatzResearch.WordTrace tailWord_6610652 prefixEnd_6610652 377160212845108336372019 := by
  unfold tailWord_6610652
  simp only [CollatzResearch.WordTrace]
  refine ⟨120555143223372144160837105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160740190964496192214449473 120555143223372144160837105)
  ·
    refine ⟨90416357417529108120627829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120555143223372144160837105 90416357417529108120627829)
    ·
      refine ⟨8476533507893353886308859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 90416357417529108120627829 8476533507893353886308859)
      ·
        refine ⟨12714800261840030829463289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8476533507893353886308859 12714800261840030829463289)
        ·
          refine ⟨9536100196380023122097467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12714800261840030829463289 9536100196380023122097467)
          ·
            refine ⟨14304150294570034683146201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9536100196380023122097467 14304150294570034683146201)
            ·
              refine ⟨10728112720927526012359651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14304150294570034683146201 10728112720927526012359651)
              ·
                refine ⟨16092169081391289018539477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10728112720927526012359651 16092169081391289018539477)
                ·
                  refine ⟨377160212845108336372019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16092169081391289018539477 377160212845108336372019)
                  ·
                    rfl

theorem cell23_6610652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 2, 1, 7].length) (baseStart_6610652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6610652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6610652 prefixEnd_6610652 := by exact prefixLift 6610652
  have htrace : WordTrace (prefixWord ++ tailWord_6610652) baseStart_6610652 baseEnd_6610652 := by
    simpa [prefixWord, tailWord_6610652, baseEnd_6610652] using wordTrace_append hprefix tailTrace_6610652
  have hstable : (prefixWord ++ tailWord_6610652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6610652).length < 2 ^ (prefixWord ++ tailWord_6610652).sum := by decide
  have hdescent : baseEnd_6610652 < baseStart_6610652 := by decide
  rcases family_descends (prefixWord ++ tailWord_6610652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6610663 : List Nat := [1, 1, 5, 4, 1, 1, 3, 1, 2, 2, 2]
def baseStart_6610663 : Nat := 118140960795 + 6610663 * 2 ^ 59
def prefixEnd_6610663 : Nat := 4983230072969 + 3 ^ 40 * 6610663 * 2
def baseEnd_6610663 : Nat := 3394447563893174484310621

theorem tailTrace_6610663 : CollatzResearch.WordTrace tailWord_6610663 prefixEnd_6610663 3394447563893174484310621 := by
  unfold tailWord_6610663
  simp only [CollatzResearch.WordTrace]
  refine ⟨241110687649704437200324643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160740458433136291466883095 241110687649704437200324643)
  ·
    refine ⟨361666031474556655800486965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241110687649704437200324643 361666031474556655800486965)
    ·
      refine ⟨33906190450739686481295653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 361666031474556655800486965 33906190450739686481295653)
      ·
        refine ⟨6357410709513691215242935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33906190450739686481295653 6357410709513691215242935)
        ·
          refine ⟨9536116064270536822864403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6357410709513691215242935 9536116064270536822864403)
          ·
            refine ⟨14304174096405805234296605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9536116064270536822864403 14304174096405805234296605)
            ·
              refine ⟨5364065286152176962861227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14304174096405805234296605 5364065286152176962861227)
              ·
                refine ⟨8046097929228265444291841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5364065286152176962861227 8046097929228265444291841)
                ·
                  refine ⟨6034573446921199083218881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8046097929228265444291841 6034573446921199083218881)
                  ·
                    refine ⟨4525930085190899312414161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6034573446921199083218881 4525930085190899312414161)
                    ·
                      refine ⟨3394447563893174484310621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4525930085190899312414161 3394447563893174484310621)
                      ·
                        rfl

theorem cell23_6610663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_6610663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6610663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6610663 prefixEnd_6610663 := by exact prefixLift 6610663
  have htrace : WordTrace (prefixWord ++ tailWord_6610663) baseStart_6610663 baseEnd_6610663 := by
    simpa [prefixWord, tailWord_6610663, baseEnd_6610663] using wordTrace_append hprefix tailTrace_6610663
  have hstable : (prefixWord ++ tailWord_6610663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6610663).length < 2 ^ (prefixWord ++ tailWord_6610663).sum := by decide
  have hdescent : baseEnd_6610663 < baseStart_6610663 := by decide
  rcases family_descends (prefixWord ++ tailWord_6610663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6610668 : List Nat := [2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 4]
def baseStart_6610668 : Nat := 118140960795 + 6610668 * 2 ^ 59
def prefixEnd_6610668 : Nat := 4983230072969 + 3 ^ 40 * 6610668 * 2
def baseEnd_6610668 : Nat := 3394450131296446964748097

theorem tailTrace_6610668 : CollatzResearch.WordTrace tailWord_6610668 prefixEnd_6610668 3394450131296446964748097 := by
  unfold tailWord_6610668
  simp only [CollatzResearch.WordTrace]
  refine ⟨120555435007343161527128329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160740580009790882036171105 120555435007343161527128329)
  ·
    refine ⟨90416576255507371145346247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120555435007343161527128329 90416576255507371145346247)
    ·
      refine ⟨135624864383261056718019371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90416576255507371145346247 135624864383261056718019371)
      ·
        refine ⟨203437296574891585077029057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135624864383261056718019371 203437296574891585077029057)
        ·
          refine ⟨152577972431168688807771793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 203437296574891585077029057 152577972431168688807771793)
          ·
            refine ⟨114433479323376516605828845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152577972431168688807771793 114433479323376516605828845)
            ·
              refine ⟨42912554746266193727185817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 114433479323376516605828845 42912554746266193727185817)
              ·
                refine ⟨32184416059699645295389363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42912554746266193727185817 32184416059699645295389363)
                ·
                  refine ⟨48276624089549467943084045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32184416059699645295389363 48276624089549467943084045)
                  ·
                    refine ⟨18103734033581050478656517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48276624089549467943084045 18103734033581050478656517)
                    ·
                      refine ⟨3394450131296446964748097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18103734033581050478656517 3394450131296446964748097)
                      ·
                        rfl

theorem cell23_6610668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 4].length) (baseStart_6610668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6610668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6610668 prefixEnd_6610668 := by exact prefixLift 6610668
  have htrace : WordTrace (prefixWord ++ tailWord_6610668) baseStart_6610668 baseEnd_6610668 := by
    simpa [prefixWord, tailWord_6610668, baseEnd_6610668] using wordTrace_append hprefix tailTrace_6610668
  have hstable : (prefixWord ++ tailWord_6610668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6610668).length < 2 ^ (prefixWord ++ tailWord_6610668).sum := by decide
  have hdescent : baseEnd_6610668 < baseStart_6610668 := by decide
  rcases family_descends (prefixWord ++ tailWord_6610668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6610685 : List Nat := [1, 4, 1, 1, 1, 1, 2, 2, 4, 4, 2]
def baseStart_6610685 : Nat := 118140960795 + 6610685 * 2 ^ 59
def prefixEnd_6610685 : Nat := 4983230072969 + 3 ^ 40 * 6610685 * 2
def baseEnd_6610685 : Nat := 3394458860467573398235519

theorem tailTrace_6610685 : CollatzResearch.WordTrace tailWord_6610685 prefixEnd_6610685 3394458860467573398235519 := by
  unfold tailWord_6610685
  simp only [CollatzResearch.WordTrace]
  refine ⟨241111490055624734957625509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160740993370416489971750339 241111490055624734957625509)
  ·
    refine ⟨45208404385429637804554783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 241111490055624734957625509 45208404385429637804554783)
    ·
      refine ⟨67812606578144456706832175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45208404385429637804554783 67812606578144456706832175)
      ·
        refine ⟨101718909867216685060248263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67812606578144456706832175 101718909867216685060248263)
        ·
          refine ⟨152578364800825027590372395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101718909867216685060248263 152578364800825027590372395)
          ·
            refine ⟨228867547201237541385558593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152578364800825027590372395 228867547201237541385558593)
            ·
              refine ⟨171650660400928156039168945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 228867547201237541385558593 171650660400928156039168945)
              ·
                refine ⟨128737995300696117029376709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 171650660400928156039168945 128737995300696117029376709)
                ·
                  refine ⟨24138374118880521943008133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 128737995300696117029376709 24138374118880521943008133)
                  ·
                    refine ⟨4525945147290097864314025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24138374118880521943008133 4525945147290097864314025)
                    ·
                      refine ⟨3394458860467573398235519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4525945147290097864314025 3394458860467573398235519)
                      ·
                        rfl

theorem cell23_6610685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 2, 4, 4, 2].length) (baseStart_6610685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6610685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6610685 prefixEnd_6610685 := by exact prefixLift 6610685
  have htrace : WordTrace (prefixWord ++ tailWord_6610685) baseStart_6610685 baseEnd_6610685 := by
    simpa [prefixWord, tailWord_6610685, baseEnd_6610685] using wordTrace_append hprefix tailTrace_6610685
  have hstable : (prefixWord ++ tailWord_6610685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6610685).length < 2 ^ (prefixWord ++ tailWord_6610685).sum := by decide
  have hdescent : baseEnd_6610685 < baseStart_6610685 := by decide
  rcases family_descends (prefixWord ++ tailWord_6610685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6610686 : List Nat := [4, 2, 2, 1, 4, 1, 1, 3, 5]
def baseStart_6610686 : Nat := 118140960795 + 6610686 * 2 ^ 59
def prefixEnd_6610686 : Nat := 4983230072969 + 3 ^ 40 * 6610686 * 2
def baseEnd_6610686 : Nat := 377162152660914210480335

theorem tailTrace_6610686 : CollatzResearch.WordTrace tailWord_6610686 prefixEnd_6610686 377162152660914210480335 := by
  unfold tailWord_6610686
  simp only [CollatzResearch.WordTrace]
  refine ⟨30138940816077639016051489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 160741017685747408085607941 30138940816077639016051489)
  ·
    refine ⟨22604205612058229262038617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30138940816077639016051489 22604205612058229262038617)
    ·
      refine ⟨16953154209043671946528963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22604205612058229262038617 16953154209043671946528963)
      ·
        refine ⟨25429731313565507919793445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16953154209043671946528963 25429731313565507919793445)
        ·
          refine ⟨4768074621293532734961271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25429731313565507919793445 4768074621293532734961271)
          ·
            refine ⟨7152111931940299102441907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4768074621293532734961271 7152111931940299102441907)
            ·
              refine ⟨10728167897910448653662861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7152111931940299102441907 10728167897910448653662861)
              ·
                refine ⟨4023062961716418245123573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10728167897910448653662861 4023062961716418245123573)
                ·
                  refine ⟨377162152660914210480335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4023062961716418245123573 377162152660914210480335)
                  ·
                    rfl

theorem cell23_6610686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 4, 1, 1, 3, 5].length) (baseStart_6610686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6610686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6610686 prefixEnd_6610686 := by exact prefixLift 6610686
  have htrace : WordTrace (prefixWord ++ tailWord_6610686) baseStart_6610686 baseEnd_6610686 := by
    simpa [prefixWord, tailWord_6610686, baseEnd_6610686] using wordTrace_append hprefix tailTrace_6610686
  have hstable : (prefixWord ++ tailWord_6610686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6610686).length < 2 ^ (prefixWord ++ tailWord_6610686).sum := by decide
  have hdescent : baseEnd_6610686 < baseStart_6610686 := by decide
  rcases family_descends (prefixWord ++ tailWord_6610686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6610712 : List Nat := [2, 1, 2, 3, 1, 1, 2, 6, 1, 4]
def baseStart_6610712 : Nat := 118140960795 + 6610712 * 2 ^ 59
def prefixEnd_6610712 : Nat := 4983230072969 + 3 ^ 40 * 6610712 * 2
def baseEnd_6610712 : Nat := 1131490908148414930865965

theorem tailTrace_6610712 : CollatzResearch.WordTrace tailWord_6610712 prefixEnd_6610712 1131490908148414930865965 := by
  unfold tailWord_6610712
  simp only [CollatzResearch.WordTrace]
  refine ⟨120556237413263459284429195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160741649884351279045905593 120556237413263459284429195)
  ·
    refine ⟨180834356119895188926643793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120556237413263459284429195 180834356119895188926643793)
    ·
      refine ⟨135625767089921391694982845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180834356119895188926643793 135625767089921391694982845)
      ·
        refine ⟨50859662658720521885618567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135625767089921391694982845 50859662658720521885618567)
        ·
          refine ⟨76289493988080782828427851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50859662658720521885618567 76289493988080782828427851)
          ·
            refine ⟨114434240982121174242641777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76289493988080782828427851 114434240982121174242641777)
            ·
              refine ⟨85825680736590880681981333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114434240982121174242641777 85825680736590880681981333)
              ·
                refine ⟨4023078784527697531967875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 85825680736590880681981333 4023078784527697531967875)
                ·
                  refine ⟨6034618176791546297951813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4023078784527697531967875 6034618176791546297951813)
                  ·
                    refine ⟨1131490908148414930865965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6034618176791546297951813 1131490908148414930865965)
                    ·
                      rfl

theorem cell23_6610712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 6, 1, 4].length) (baseStart_6610712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6610712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6610712 prefixEnd_6610712 := by exact prefixLift 6610712
  have htrace : WordTrace (prefixWord ++ tailWord_6610712) baseStart_6610712 baseEnd_6610712 := by
    simpa [prefixWord, tailWord_6610712, baseEnd_6610712] using wordTrace_append hprefix tailTrace_6610712
  have hstable : (prefixWord ++ tailWord_6610712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6610712).length < 2 ^ (prefixWord ++ tailWord_6610712).sum := by decide
  have hdescent : baseEnd_6610712 < baseStart_6610712 := by decide
  rcases family_descends (prefixWord ++ tailWord_6610712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6610725 : List Nat := [1, 3, 1, 2, 3, 3, 1, 3, 6]
def baseStart_6610725 : Nat := 118140960795 + 6610725 * 2 ^ 59
def prefixEnd_6610725 : Nat := 4983230072969 + 3 ^ 40 * 6610725 * 2
def baseEnd_6610725 : Nat := 377164377743750360192815

theorem tailTrace_6610725 : CollatzResearch.WordTrace tailWord_6610725 prefixEnd_6610725 377164377743750360192815 := by
  unfold tailWord_6610725
  simp only [CollatzResearch.WordTrace]
  refine ⟨241112948975479821789081629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160741965983653214526054419 241112948975479821789081629)
  ·
    refine ⟨90417355865804933170905611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 241112948975479821789081629 90417355865804933170905611)
    ·
      refine ⟨135626033798707399756358417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90417355865804933170905611 135626033798707399756358417)
      ·
        refine ⟨101719525349030549817268813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135626033798707399756358417 101719525349030549817268813)
        ·
          refine ⟨38144822005886456181475805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101719525349030549817268813 38144822005886456181475805)
          ·
            refine ⟨14304308252207421068053427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38144822005886456181475805 14304308252207421068053427)
            ·
              refine ⟨21456462378311131602080141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14304308252207421068053427 21456462378311131602080141)
              ·
                refine ⟨8046173391866674350780053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21456462378311131602080141 8046173391866674350780053)
                ·
                  refine ⟨377164377743750360192815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8046173391866674350780053 377164377743750360192815)
                  ·
                    rfl

theorem cell23_6610725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 3, 6].length) (baseStart_6610725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6610725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6610725 prefixEnd_6610725 := by exact prefixLift 6610725
  have htrace : WordTrace (prefixWord ++ tailWord_6610725) baseStart_6610725 baseEnd_6610725 := by
    simpa [prefixWord, tailWord_6610725, baseEnd_6610725] using wordTrace_append hprefix tailTrace_6610725
  have hstable : (prefixWord ++ tailWord_6610725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6610725).length < 2 ^ (prefixWord ++ tailWord_6610725).sum := by decide
  have hdescent : baseEnd_6610725 < baseStart_6610725 := by decide
  rcases family_descends (prefixWord ++ tailWord_6610725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6610762 : List Nat := [3, 1, 2, 1, 1, 1, 3, 4, 2, 3, 2]
def baseStart_6610762 : Nat := 118140960795 + 6610762 * 2 ^ 59
def prefixEnd_6610762 : Nat := 4983230072969 + 3 ^ 40 * 6610762 * 2
def baseEnd_6610762 : Nat := 3394498398477969596972665

theorem tailTrace_6610762 : CollatzResearch.WordTrace tailWord_6610762 prefixEnd_6610762 3394498398477969596972665 := by
  unfold tailWord_6610762
  simp only [CollatzResearch.WordTrace]
  refine ⟨60278574619086444277044635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160742865650897184738785693 60278574619086444277044635)
  ·
    refine ⟨90417861928629666415566953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60278574619086444277044635 90417861928629666415566953)
    ·
      refine ⟨67813396446472249811675215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90417861928629666415566953 67813396446472249811675215)
      ·
        refine ⟨101720094669708374717512823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67813396446472249811675215 101720094669708374717512823)
        ·
          refine ⟨152580142004562562076269235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101720094669708374717512823 152580142004562562076269235)
          ·
            refine ⟨228870213006843843114403853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152580142004562562076269235 228870213006843843114403853)
            ·
              refine ⟨85826329877566441167901445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 228870213006843843114403853 85826329877566441167901445)
              ·
                refine ⟨16092436852043707718981521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 85826329877566441167901445 16092436852043707718981521)
                ·
                  refine ⟨12069327639032780789236141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16092436852043707718981521 12069327639032780789236141)
                  ·
                    refine ⟨4525997864637292795963553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12069327639032780789236141 4525997864637292795963553)
                    ·
                      refine ⟨3394498398477969596972665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4525997864637292795963553 3394498398477969596972665)
                      ·
                        rfl

theorem cell23_6610762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 4, 2, 3, 2].length) (baseStart_6610762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6610762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6610762 prefixEnd_6610762 := by exact prefixLift 6610762
  have htrace : WordTrace (prefixWord ++ tailWord_6610762) baseStart_6610762 baseEnd_6610762 := by
    simpa [prefixWord, tailWord_6610762, baseEnd_6610762] using wordTrace_append hprefix tailTrace_6610762
  have hstable : (prefixWord ++ tailWord_6610762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6610762).length < 2 ^ (prefixWord ++ tailWord_6610762).sum := by decide
  have hdescent : baseEnd_6610762 < baseStart_6610762 := by decide
  rcases family_descends (prefixWord ++ tailWord_6610762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6610768 : List Nat := [2, 1, 1, 1, 1, 4, 1, 1, 5, 6]
def baseStart_6610768 : Nat := 118140960795 + 6610768 * 2 ^ 59
def prefixEnd_6610768 : Nat := 4983230072969 + 3 ^ 40 * 6610768 * 2
def baseEnd_6610768 : Nat := 1131500493120632191165879

theorem tailTrace_6610768 : CollatzResearch.WordTrace tailWord_6610768 prefixEnd_6610768 1131500493120632191165879 := by
  unfold tailWord_6610768
  simp only [CollatzResearch.WordTrace]
  refine ⟨120557258657162020066448479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160743011542882693421931305 120557258657162020066448479)
  ·
    refine ⟨180835887985743030099672719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120557258657162020066448479 180835887985743030099672719)
    ·
      refine ⟨271253831978614545149509079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180835887985743030099672719 271253831978614545149509079)
      ·
        refine ⟨406880747967921817724263619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271253831978614545149509079 406880747967921817724263619)
        ·
          refine ⟨610321121951882726586395429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 406880747967921817724263619 610321121951882726586395429)
          ·
            refine ⟨114435210365978011234949143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 610321121951882726586395429 114435210365978011234949143)
            ·
              refine ⟨171652815548967016852423715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114435210365978011234949143 171652815548967016852423715)
              ·
                refine ⟨257479223323450525278635573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 171652815548967016852423715 257479223323450525278635573)
                ·
                  refine ⟨24138677186573486744872085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 257479223323450525278635573 24138677186573486744872085)
                  ·
                    refine ⟨1131500493120632191165879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24138677186573486744872085 1131500493120632191165879)
                    ·
                      rfl

theorem cell23_6610768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 5, 6].length) (baseStart_6610768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6610768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6610768 prefixEnd_6610768 := by exact prefixLift 6610768
  have htrace : WordTrace (prefixWord ++ tailWord_6610768) baseStart_6610768 baseEnd_6610768 := by
    simpa [prefixWord, tailWord_6610768, baseEnd_6610768] using wordTrace_append hprefix tailTrace_6610768
  have hstable : (prefixWord ++ tailWord_6610768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6610768).length < 2 ^ (prefixWord ++ tailWord_6610768).sum := by decide
  have hdescent : baseEnd_6610768 < baseStart_6610768 := by decide
  rcases family_descends (prefixWord ++ tailWord_6610768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6610785 : List Nat := [1, 2, 3, 1, 1, 1, 6, 1, 1, 6]
def baseStart_6610785 : Nat := 118140960795 + 6610785 * 2 ^ 59
def prefixEnd_6610785 : Nat := 4983230072969 + 3 ^ 40 * 6610785 * 2
def baseEnd_6610785 : Nat := 1131503402844341002328353

theorem tailTrace_6610785 : CollatzResearch.WordTrace tailWord_6610785 prefixEnd_6610785 1131503402844341002328353 := by
  unfold tailWord_6610785
  simp only [CollatzResearch.WordTrace]
  refine ⟨241115137355262452036265809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160743424903508301357510539 241115137355262452036265809)
  ·
    refine ⟨180836353016446839027199357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241115137355262452036265809 180836353016446839027199357)
    ·
      refine ⟨67813632381167564635199759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180836353016446839027199357 67813632381167564635199759)
      ·
        refine ⟨101720448571751346952799639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67813632381167564635199759 101720448571751346952799639)
        ·
          refine ⟨152580672857627020429199459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101720448571751346952799639 152580672857627020429199459)
          ·
            refine ⟨228871009286440530643799189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152580672857627020429199459 228871009286440530643799189)
            ·
              refine ⟨10728328560301899873928087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 228871009286440530643799189 10728328560301899873928087)
              ·
                refine ⟨16092492840452849810892131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10728328560301899873928087 16092492840452849810892131)
                ·
                  refine ⟨24138739260679274716338197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16092492840452849810892131 24138739260679274716338197)
                  ·
                    refine ⟨1131503402844341002328353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24138739260679274716338197 1131503402844341002328353)
                    ·
                      rfl

theorem cell23_6610785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 6, 1, 1, 6].length) (baseStart_6610785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6610785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6610785 prefixEnd_6610785 := by exact prefixLift 6610785
  have htrace : WordTrace (prefixWord ++ tailWord_6610785) baseStart_6610785 baseEnd_6610785 := by
    simpa [prefixWord, tailWord_6610785, baseEnd_6610785] using wordTrace_append hprefix tailTrace_6610785
  have hstable : (prefixWord ++ tailWord_6610785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6610785).length < 2 ^ (prefixWord ++ tailWord_6610785).sum := by decide
  have hdescent : baseEnd_6610785 < baseStart_6610785 := by decide
  rcases family_descends (prefixWord ++ tailWord_6610785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6610792 : List Nat := [2, 1, 4, 2, 1, 1, 2, 4, 1, 1, 4]
def baseStart_6610792 : Nat := 118140960795 + 6610792 * 2 ^ 59
def prefixEnd_6610792 : Nat := 4983230072969 + 3 ^ 40 * 6610792 * 2
def baseEnd_6610792 : Nat := 3394513802897604479597527

theorem tailTrace_6610792 : CollatzResearch.WordTrace tailWord_6610792 prefixEnd_6610792 3394513802897604479597527 := by
  unfold tailWord_6610792
  simp only [CollatzResearch.WordTrace]
  refine ⟨120557696333118546115885315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160743595110824728154513753 120557696333118546115885315)
  ·
    refine ⟨180836544499677819173827973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120557696333118546115885315 180836544499677819173827973)
    ·
      refine ⟨33906852093689591095092745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 180836544499677819173827973 33906852093689591095092745)
      ·
        refine ⟨25430139070267193321319559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33906852093689591095092745 25430139070267193321319559)
        ·
          refine ⟨38145208605400789981979339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25430139070267193321319559 38145208605400789981979339)
          ·
            refine ⟨57217812908101184972969009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38145208605400789981979339 57217812908101184972969009)
            ·
              refine ⟨42913359681075888729726757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57217812908101184972969009 42913359681075888729726757)
              ·
                refine ⟨8046254940201729136823767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42913359681075888729726757 8046254940201729136823767)
                ·
                  refine ⟨12069382410302593705235651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8046254940201729136823767 12069382410302593705235651)
                  ·
                    refine ⟨18104073615453890557853477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12069382410302593705235651 18104073615453890557853477)
                    ·
                      refine ⟨3394513802897604479597527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18104073615453890557853477 3394513802897604479597527)
                      ·
                        rfl

theorem cell23_6610792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 4, 1, 1, 4].length) (baseStart_6610792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6610792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6610792 prefixEnd_6610792 := by exact prefixLift 6610792
  have htrace : WordTrace (prefixWord ++ tailWord_6610792) baseStart_6610792 baseEnd_6610792 := by
    simpa [prefixWord, tailWord_6610792, baseEnd_6610792] using wordTrace_append hprefix tailTrace_6610792
  have hstable : (prefixWord ++ tailWord_6610792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6610792).length < 2 ^ (prefixWord ++ tailWord_6610792).sum := by decide
  have hdescent : baseEnd_6610792 < baseStart_6610792 := by decide
  rcases family_descends (prefixWord ++ tailWord_6610792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6610808 : List Nat := [2, 1, 2, 1, 1, 1, 1, 2, 1, 4, 7]
def baseStart_6610808 : Nat := 118140960795 + 6610808 * 2 ^ 59
def prefixEnd_6610808 : Nat := 4983230072969 + 3 ^ 40 * 6610808 * 2
def baseEnd_6610808 : Nat := 3394522018588076416997453

theorem tailTrace_6610808 : CollatzResearch.WordTrace tailWord_6610808 prefixEnd_6610808 3394522018588076416997453 := by
  unfold tailWord_6610808
  simp only [CollatzResearch.WordTrace]
  refine ⟨120557988117089563482176539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160743984156119417976235385 120557988117089563482176539)
  ·
    refine ⟨180836982175634345223264809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120557988117089563482176539 180836982175634345223264809)
    ·
      refine ⟨135627736631725758917448607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180836982175634345223264809 135627736631725758917448607)
      ·
        refine ⟨203441604947588638376172911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135627736631725758917448607 203441604947588638376172911)
        ·
          refine ⟨305162407421382957564259367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203441604947588638376172911 305162407421382957564259367)
          ·
            refine ⟨457743611132074436346389051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 305162407421382957564259367 457743611132074436346389051)
            ·
              refine ⟨686615416698111654519583577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 457743611132074436346389051 686615416698111654519583577)
              ·
                refine ⟨514961562523583740889687683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 686615416698111654519583577 514961562523583740889687683)
                ·
                  refine ⟨772442343785375611334531525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 514961562523583740889687683 772442343785375611334531525)
                  ·
                    refine ⟨144832939459757927125224661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 772442343785375611334531525 144832939459757927125224661)
                    ·
                      refine ⟨3394522018588076416997453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 144832939459757927125224661 3394522018588076416997453)
                      ·
                        rfl

theorem cell23_6610808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 1, 4, 7].length) (baseStart_6610808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6610808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6610808 prefixEnd_6610808 := by exact prefixLift 6610808
  have htrace : WordTrace (prefixWord ++ tailWord_6610808) baseStart_6610808 baseEnd_6610808 := by
    simpa [prefixWord, tailWord_6610808, baseEnd_6610808] using wordTrace_append hprefix tailTrace_6610808
  have hstable : (prefixWord ++ tailWord_6610808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6610808).length < 2 ^ (prefixWord ++ tailWord_6610808).sum := by decide
  have hdescent : baseEnd_6610808 < baseStart_6610808 := by decide
  rcases family_descends (prefixWord ++ tailWord_6610808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6610819 : List Nat := [1, 1, 1, 3, 4, 4, 1, 2, 2, 4]
def baseStart_6610819 : Nat := 118140960795 + 6610819 * 2 ^ 59
def prefixEnd_6610819 : Nat := 4983230072969 + 3 ^ 40 * 6610819 * 2
def baseEnd_6610819 : Nat := 1131509222291758624653301

theorem tailTrace_6610819 : CollatzResearch.WordTrace tailWord_6610819 prefixEnd_6610819 1131509222291758624653301 := by
  unfold tailWord_6610819
  simp only [CollatzResearch.WordTrace]
  refine ⟨241116377437139275843003511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160744251624759517228669007 241116377437139275843003511)
  ·
    refine ⟨361674566155708913764505267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241116377437139275843003511 361674566155708913764505267)
    ·
      refine ⟨542511849233563370646757901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 361674566155708913764505267 542511849233563370646757901)
      ·
        refine ⟨203441943462586263992534213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 542511849233563370646757901 203441943462586263992534213)
        ·
          refine ⟨38145364399234924498600165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 203441943462586263992534213 38145364399234924498600165)
          ·
            refine ⟨7152255824856548343487531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38145364399234924498600165 7152255824856548343487531)
            ·
              refine ⟨10728383737284822515231297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7152255824856548343487531 10728383737284822515231297)
              ·
                refine ⟨8046287802963616886423473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10728383737284822515231297 8046287802963616886423473)
                ·
                  refine ⟨6034715852222712664817605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8046287802963616886423473 6034715852222712664817605)
                  ·
                    refine ⟨1131509222291758624653301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6034715852222712664817605 1131509222291758624653301)
                    ·
                      rfl

theorem cell23_6610819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 1, 2, 2, 4].length) (baseStart_6610819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6610819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6610819 prefixEnd_6610819 := by exact prefixLift 6610819
  have htrace : WordTrace (prefixWord ++ tailWord_6610819) baseStart_6610819 baseEnd_6610819 := by
    simpa [prefixWord, tailWord_6610819, baseEnd_6610819] using wordTrace_append hprefix tailTrace_6610819
  have hstable : (prefixWord ++ tailWord_6610819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6610819).length < 2 ^ (prefixWord ++ tailWord_6610819).sum := by decide
  have hdescent : baseEnd_6610819 < baseStart_6610819 := by decide
  rcases family_descends (prefixWord ++ tailWord_6610819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6610836 : List Nat := [2, 4, 2, 1, 1, 3, 3, 1, 2, 4]
def baseStart_6610836 : Nat := 118140960795 + 6610836 * 2 ^ 59
def prefixEnd_6610836 : Nat := 4983230072969 + 3 ^ 40 * 6610836 * 2
def baseEnd_6610836 : Nat := 1131512132015467435815775

theorem tailTrace_6610836 : CollatzResearch.WordTrace tailWord_6610836 prefixEnd_6610836 1131512132015467435815775 := by
  unfold tailWord_6610836
  simp only [CollatzResearch.WordTrace]
  refine ⟨120558498739038843873186181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160744664985385125164248241 120558498739038843873186181)
  ·
    refine ⟨22604718513569783226222409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 120558498739038843873186181 22604718513569783226222409)
    ·
      refine ⟨16953538885177337419666807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22604718513569783226222409 16953538885177337419666807)
      ·
        refine ⟨25430308327766006129500211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16953538885177337419666807 25430308327766006129500211)
        ·
          refine ⟨38145462491649009194250317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25430308327766006129500211 38145462491649009194250317)
          ·
            refine ⟨14304548434368378447843869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38145462491649009194250317 14304548434368378447843869)
            ·
              refine ⟨5364205662888141917941451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14304548434368378447843869 5364205662888141917941451)
              ·
                refine ⟨8046308494332212876912177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5364205662888141917941451 8046308494332212876912177)
                ·
                  refine ⟨6034731370749159657684133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8046308494332212876912177 6034731370749159657684133)
                  ·
                    refine ⟨1131512132015467435815775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6034731370749159657684133 1131512132015467435815775)
                    ·
                      rfl

theorem cell23_6610836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 3, 1, 2, 4].length) (baseStart_6610836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6610836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6610836 prefixEnd_6610836 := by exact prefixLift 6610836
  have htrace : WordTrace (prefixWord ++ tailWord_6610836) baseStart_6610836 baseEnd_6610836 := by
    simpa [prefixWord, tailWord_6610836, baseEnd_6610836] using wordTrace_append hprefix tailTrace_6610836
  have hstable : (prefixWord ++ tailWord_6610836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6610836).length < 2 ^ (prefixWord ++ tailWord_6610836).sum := by decide
  have hdescent : baseEnd_6610836 < baseStart_6610836 := by decide
  rcases family_descends (prefixWord ++ tailWord_6610836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6610849 : List Nat := [1, 2, 3, 4, 2, 2, 2, 7]
def baseStart_6610849 : Nat := 118140960795 + 6610849 * 2 ^ 59
def prefixEnd_6610849 : Nat := 4983230072969 + 3 ^ 40 * 6610849 * 2
def baseEnd_6610849 : Nat := 125723817455367065058695

theorem tailTrace_6610849 : CollatzResearch.WordTrace tailWord_6610849 prefixEnd_6610849 125723817455367065058695 := by
  unfold tailWord_6610849
  simp only [CollatzResearch.WordTrace]
  refine ⟨241117471627030590966595601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160744981084687060644397067 241117471627030590966595601)
  ·
    refine ⟨180838103720272943224946701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241117471627030590966595601 180838103720272943224946701)
    ·
      refine ⟨67814288895102353709355013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180838103720272943224946701 67814288895102353709355013)
      ·
        refine ⟨12715179167831691320504065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67814288895102353709355013 12715179167831691320504065)
        ·
          refine ⟨9536384375873768490378049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12715179167831691320504065 9536384375873768490378049)
          ·
            refine ⟨7152288281905326367783537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9536384375873768490378049 7152288281905326367783537)
            ·
              refine ⟨5364216211428994775837653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7152288281905326367783537 5364216211428994775837653)
              ·
                refine ⟨125723817455367065058695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5364216211428994775837653 125723817455367065058695)
                ·
                  rfl

theorem cell23_6610849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 2, 7].length) (baseStart_6610849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6610849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6610849 prefixEnd_6610849 := by exact prefixLift 6610849
  have htrace : WordTrace (prefixWord ++ tailWord_6610849) baseStart_6610849 baseEnd_6610849 := by
    simpa [prefixWord, tailWord_6610849, baseEnd_6610849] using wordTrace_append hprefix tailTrace_6610849
  have hstable : (prefixWord ++ tailWord_6610849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6610849).length < 2 ^ (prefixWord ++ tailWord_6610849).sum := by decide
  have hdescent : baseEnd_6610849 < baseStart_6610849 := by decide
  rcases family_descends (prefixWord ++ tailWord_6610849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6610895 : List Nat := [1, 1, 2, 1, 1, 5, 2, 1, 1, 4, 4]
def baseStart_6610895 : Nat := 118140960795 + 6610895 * 2 ^ 59
def prefixEnd_6610895 : Nat := 4983230072969 + 3 ^ 40 * 6610895 * 2
def baseEnd_6610895 : Nat := 3394566691405017576609553

theorem tailTrace_6610895 : CollatzResearch.WordTrace tailWord_6610895 prefixEnd_6610895 3394566691405017576609553 := by
  unfold tailWord_6610895
  simp only [CollatzResearch.WordTrace]
  refine ⟨241119149384863940822770139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160746099589909293881846759 241119149384863940822770139)
  ·
    refine ⟨361678724077295911234155209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241119149384863940822770139 361678724077295911234155209)
    ·
      refine ⟨271259043057971933425616407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 361678724077295911234155209 271259043057971933425616407)
      ·
        refine ⟨406888564586957900138424611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271259043057971933425616407 406888564586957900138424611)
        ·
          refine ⟨610332846880436850207636917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 406888564586957900138424611 610332846880436850207636917)
          ·
            refine ⟨57218704395040954706965961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 610332846880436850207636917 57218704395040954706965961)
            ·
              refine ⟨42914028296280716030224471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57218704395040954706965961 42914028296280716030224471)
              ·
                refine ⟨64371042444421074045336707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42914028296280716030224471 64371042444421074045336707)
                ·
                  refine ⟨96556563666631611068005061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64371042444421074045336707 96556563666631611068005061)
                  ·
                    refine ⟨18104355687493427075250949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 96556563666631611068005061 18104355687493427075250949)
                    ·
                      refine ⟨3394566691405017576609553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18104355687493427075250949 3394566691405017576609553)
                      ·
                        rfl

theorem cell23_6610895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 1, 1, 4, 4].length) (baseStart_6610895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6610895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6610895 prefixEnd_6610895 := by exact prefixLift 6610895
  have htrace : WordTrace (prefixWord ++ tailWord_6610895) baseStart_6610895 baseEnd_6610895 := by
    simpa [prefixWord, tailWord_6610895, baseEnd_6610895] using wordTrace_append hprefix tailTrace_6610895
  have hstable : (prefixWord ++ tailWord_6610895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6610895).length < 2 ^ (prefixWord ++ tailWord_6610895).sum := by decide
  have hdescent : baseEnd_6610895 < baseStart_6610895 := by decide
  rcases family_descends (prefixWord ++ tailWord_6610895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6610939 : List Nat := [1, 1, 1, 1, 1, 3, 8, 2, 5]
def baseStart_6610939 : Nat := 118140960795 + 6610939 * 2 ^ 59
def prefixEnd_6610939 : Nat := 4983230072969 + 3 ^ 40 * 6610939 * 2
def baseEnd_6610939 : Nat := 377176587172646156051039

theorem tailTrace_6610939 : CollatzResearch.WordTrace tailWord_6610939 prefixEnd_6610939 377176587172646156051039 := by
  unfold tailWord_6610939
  simp only [CollatzResearch.WordTrace]
  refine ⟨241120754196704536337371871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160747169464469690891581247 241120754196704536337371871)
  ·
    refine ⟨361681131295056804506057807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241120754196704536337371871 361681131295056804506057807)
    ·
      refine ⟨542521696942585206759086711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 361681131295056804506057807 542521696942585206759086711)
      ·
        refine ⟨813782545413877810138630067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 542521696942585206759086711 813782545413877810138630067)
        ·
          refine ⟨1220673818120816715207945101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 813782545413877810138630067 1220673818120816715207945101)
          ·
            refine ⟨457752681795306268202979413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1220673818120816715207945101 457752681795306268202979413)
            ·
              refine ⟨5364289239788745330503665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 457752681795306268202979413 5364289239788745330503665)
              ·
                refine ⟨4023216929841558997877749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5364289239788745330503665 4023216929841558997877749)
                ·
                  refine ⟨377176587172646156051039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4023216929841558997877749 377176587172646156051039)
                  ·
                    rfl

theorem cell23_6610939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 8, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 8, 2, 5].length) (baseStart_6610939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6610939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6610939 prefixEnd_6610939 := by exact prefixLift 6610939
  have htrace : WordTrace (prefixWord ++ tailWord_6610939) baseStart_6610939 baseEnd_6610939 := by
    simpa [prefixWord, tailWord_6610939, baseEnd_6610939] using wordTrace_append hprefix tailTrace_6610939
  have hstable : (prefixWord ++ tailWord_6610939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6610939).length < 2 ^ (prefixWord ++ tailWord_6610939).sum := by decide
  have hdescent : baseEnd_6610939 < baseStart_6610939 := by decide
  rcases family_descends (prefixWord ++ tailWord_6610939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6611009 : List Nat := [1, 2, 5, 1, 2, 1, 1, 2, 1, 4, 3]
def baseStart_6611009 : Nat := 118140960795 + 6611009 * 2 ^ 59
def prefixEnd_6611009 : Nat := 4983230072969 + 3 ^ 40 * 6611009 * 2
def baseEnd_6611009 : Nat := 3394625228199630130584029

theorem tailTrace_6611009 : CollatzResearch.WordTrace tailWord_6611009 prefixEnd_6611009 3394625228199630130584029 := by
  unfold tailWord_6611009
  simp only [CollatzResearch.WordTrace]
  refine ⟨241123307306450938292420081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160748871537633958861613387 241123307306450938292420081)
  ·
    refine ⟨180842480479838203719315061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241123307306450938292420081 180842480479838203719315061)
    ·
      refine ⟨16953982544984831598685787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 180842480479838203719315061 16953982544984831598685787)
      ·
        refine ⟨25430973817477247398028681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16953982544984831598685787 25430973817477247398028681)
        ·
          refine ⟨19073230363107935548521511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25430973817477247398028681 19073230363107935548521511)
          ·
            refine ⟨28609845544661903322782267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19073230363107935548521511 28609845544661903322782267)
            ·
              refine ⟨42914768316992854984173401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28609845544661903322782267 42914768316992854984173401)
              ·
                refine ⟨32186076237744641238130051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42914768316992854984173401 32186076237744641238130051)
                ·
                  refine ⟨48279114356616961857195077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32186076237744641238130051 48279114356616961857195077)
                  ·
                    refine ⟨9052333941865680348224077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48279114356616961857195077 9052333941865680348224077)
                    ·
                      refine ⟨3394625228199630130584029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9052333941865680348224077 3394625228199630130584029)
                      ·
                        rfl

theorem cell23_6611009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 2, 1, 4, 3].length) (baseStart_6611009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6611009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6611009 prefixEnd_6611009 := by exact prefixLift 6611009
  have htrace : WordTrace (prefixWord ++ tailWord_6611009) baseStart_6611009 baseEnd_6611009 := by
    simpa [prefixWord, tailWord_6611009, baseEnd_6611009] using wordTrace_append hprefix tailTrace_6611009
  have hstable : (prefixWord ++ tailWord_6611009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6611009).length < 2 ^ (prefixWord ++ tailWord_6611009).sum := by decide
  have hdescent : baseEnd_6611009 < baseStart_6611009 := by decide
  rcases family_descends (prefixWord ++ tailWord_6611009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6611050 : List Nat := [3, 1, 3, 2, 3, 1, 3, 2, 1, 4]
def baseStart_6611050 : Nat := 118140960795 + 6611050 * 2 ^ 59
def prefixEnd_6611050 : Nat := 4983230072969 + 3 ^ 40 * 6611050 * 2
def baseEnd_6611050 : Nat := 1131548760302154823390447

theorem tailTrace_6611050 : CollatzResearch.WordTrace tailWord_6611050 prefixEnd_6611050 1131548760302154823390447 := by
  unfold tailWord_6611050
  simp only [CollatzResearch.WordTrace]
  refine ⟨60281200674825600573665651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160749868466201601529775069 60281200674825600573665651)
  ·
    refine ⟨90421801012238400860498477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60281200674825600573665651 90421801012238400860498477)
    ·
      refine ⟨33908175379589400322686929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90421801012238400860498477 33908175379589400322686929)
      ·
        refine ⟨25431131534692050242015197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33908175379589400322686929 25431131534692050242015197)
        ·
          refine ⟨9536674325509518840755699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25431131534692050242015197 9536674325509518840755699)
          ·
            refine ⟨14305011488264278261133549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9536674325509518840755699 14305011488264278261133549)
            ·
              refine ⟨5364379308099104347925081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14305011488264278261133549 5364379308099104347925081)
              ·
                refine ⟨4023284481074328260943811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5364379308099104347925081 4023284481074328260943811)
                ·
                  refine ⟨6034926721611492391415717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4023284481074328260943811 6034926721611492391415717)
                  ·
                    refine ⟨1131548760302154823390447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6034926721611492391415717 1131548760302154823390447)
                    ·
                      rfl

theorem cell23_6611050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 3, 2, 1, 4].length) (baseStart_6611050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6611050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6611050 prefixEnd_6611050 := by exact prefixLift 6611050
  have htrace : WordTrace (prefixWord ++ tailWord_6611050) baseStart_6611050 baseEnd_6611050 := by
    simpa [prefixWord, tailWord_6611050, baseEnd_6611050] using wordTrace_append hprefix tailTrace_6611050
  have hstable : (prefixWord ++ tailWord_6611050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6611050).length < 2 ^ (prefixWord ++ tailWord_6611050).sum := by decide
  have hdescent : baseEnd_6611050 < baseStart_6611050 := by decide
  rcases family_descends (prefixWord ++ tailWord_6611050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6611056 : List Nat := [2, 1, 1, 1, 5, 2, 3, 1, 3, 1, 3]
def baseStart_6611056 : Nat := 118140960795 + 6611056 * 2 ^ 59
def prefixEnd_6611056 : Nat := 4983230072969 + 3 ^ 40 * 6611056 * 2
def baseEnd_6611056 : Nat := 3394649361790391446696313

theorem tailTrace_6611056 : CollatzResearch.WordTrace tailWord_6611056 prefixEnd_6611056 3394649361790391446696313 := by
  unfold tailWord_6611056
  simp only [CollatzResearch.WordTrace]
  refine ⟨120562510768640332659690511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160750014358187110212920681 120562510768640332659690511)
  ·
    refine ⟨180843766152960498989535767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120562510768640332659690511 180843766152960498989535767)
    ·
      refine ⟨271265649229440748484303651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180843766152960498989535767 271265649229440748484303651)
      ·
        refine ⟨406898473844161122726455477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271265649229440748484303651 406898473844161122726455477)
        ·
          refine ⟨38146731922890105255605201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 406898473844161122726455477 38146731922890105255605201)
          ·
            refine ⟨28610048942167578941703901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38146731922890105255605201 28610048942167578941703901)
            ·
              refine ⟨10728768353312842103138963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28610048942167578941703901 10728768353312842103138963)
              ·
                refine ⟨16093152529969263154708445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10728768353312842103138963 16093152529969263154708445)
                ·
                  refine ⟨6034932198738473683015667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16093152529969263154708445 6034932198738473683015667)
                  ·
                    refine ⟨9052398298107710524523501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6034932198738473683015667 9052398298107710524523501)
                    ·
                      refine ⟨3394649361790391446696313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9052398298107710524523501 3394649361790391446696313)
                      ·
                        rfl

theorem cell23_6611056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 3, 1, 3, 1, 3].length) (baseStart_6611056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6611056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6611056 prefixEnd_6611056 := by exact prefixLift 6611056
  have htrace : WordTrace (prefixWord ++ tailWord_6611056) baseStart_6611056 baseEnd_6611056 := by
    simpa [prefixWord, tailWord_6611056, baseEnd_6611056] using wordTrace_append hprefix tailTrace_6611056
  have hstable : (prefixWord ++ tailWord_6611056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6611056).length < 2 ^ (prefixWord ++ tailWord_6611056).sum := by decide
  have hdescent : baseEnd_6611056 < baseStart_6611056 := by decide
  rcases family_descends (prefixWord ++ tailWord_6611056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6611072 : List Nat := [2, 1, 1, 2, 1, 3, 1, 5, 1, 6]
def baseStart_6611072 : Nat := 118140960795 + 6611072 * 2 ^ 59
def prefixEnd_6611072 : Nat := 4983230072969 + 3 ^ 40 * 6611072 * 2
def baseEnd_6611072 : Nat := 1131552525826954461365413

theorem tailTrace_6611072 : CollatzResearch.WordTrace tailWord_6611072 prefixEnd_6611072 1131552525826954461365413 := by
  unfold tailWord_6611072
  simp only [CollatzResearch.WordTrace]
  refine ⟨120562802552611350025981735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160750403403481800034642313 120562802552611350025981735)
  ·
    refine ⟨180844203828917025038972603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120562802552611350025981735 180844203828917025038972603)
    ·
      refine ⟨271266305743375537558458905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180844203828917025038972603 271266305743375537558458905)
      ·
        refine ⟨203449729307531653168844179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 271266305743375537558458905 203449729307531653168844179)
        ·
          refine ⟨305174593961297479753266269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203449729307531653168844179 305174593961297479753266269)
          ·
            refine ⟨114440472735486554907474851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 305174593961297479753266269 114440472735486554907474851)
            ·
              refine ⟨171660709103229832361212277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114440472735486554907474851 171660709103229832361212277)
              ·
                refine ⟨16093191478427796783863651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 171660709103229832361212277 16093191478427796783863651)
                ·
                  refine ⟨24139787217641695175795477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16093191478427796783863651 24139787217641695175795477)
                  ·
                    refine ⟨1131552525826954461365413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24139787217641695175795477 1131552525826954461365413)
                    ·
                      rfl

theorem cell23_6611072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 5, 1, 6].length) (baseStart_6611072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6611072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6611072 prefixEnd_6611072 := by exact prefixLift 6611072
  have htrace : WordTrace (prefixWord ++ tailWord_6611072) baseStart_6611072 baseEnd_6611072 := by
    simpa [prefixWord, tailWord_6611072, baseEnd_6611072] using wordTrace_append hprefix tailTrace_6611072
  have hstable : (prefixWord ++ tailWord_6611072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6611072).length < 2 ^ (prefixWord ++ tailWord_6611072).sum := by decide
  have hdescent : baseEnd_6611072 < baseStart_6611072 := by decide
  rcases family_descends (prefixWord ++ tailWord_6611072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6611079 : List Nat := [1, 1, 4, 2, 1, 1, 2, 1, 2, 6, 2]
def baseStart_6611079 : Nat := 118140960795 + 6611079 * 2 ^ 59
def prefixEnd_6611079 : Nat := 4983230072969 + 3 ^ 40 * 6611079 * 2
def baseEnd_6611079 : Nat := 3394661171845444856708707

theorem tailTrace_6611079 : CollatzResearch.WordTrace tailWord_6611079 prefixEnd_6611079 3394661171845444856708707 := by
  unfold tailWord_6611079
  simp only [CollatzResearch.WordTrace]
  refine ⟨241125860416197340247468291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160750573610798226831645527 241125860416197340247468291)
  ·
    refine ⟨361688790624296010371202437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241125860416197340247468291 361688790624296010371202437)
    ·
      refine ⟨67816648242055501944600457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 361688790624296010371202437 67816648242055501944600457)
      ·
        refine ⟨50862486181541626458450343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67816648242055501944600457 50862486181541626458450343)
        ·
          refine ⟨76293729272312439687675515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50862486181541626458450343 76293729272312439687675515)
          ·
            refine ⟨114440593908468659531513273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76293729272312439687675515 114440593908468659531513273)
            ·
              refine ⟨85830445431351494648634955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114440593908468659531513273 85830445431351494648634955)
              ·
                refine ⟨128745668147027241972952433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85830445431351494648634955 128745668147027241972952433)
                ·
                  refine ⟨96559251110270431479714325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 128745668147027241972952433 96559251110270431479714325)
                  ·
                    refine ⟨4526214895793926475611609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 96559251110270431479714325 4526214895793926475611609)
                    ·
                      refine ⟨3394661171845444856708707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4526214895793926475611609 3394661171845444856708707)
                      ·
                        rfl

theorem cell23_6611079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 1, 2, 6, 2].length) (baseStart_6611079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6611079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6611079 prefixEnd_6611079 := by exact prefixLift 6611079
  have htrace : WordTrace (prefixWord ++ tailWord_6611079) baseStart_6611079 baseEnd_6611079 := by
    simpa [prefixWord, tailWord_6611079, baseEnd_6611079] using wordTrace_append hprefix tailTrace_6611079
  have hstable : (prefixWord ++ tailWord_6611079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6611079).length < 2 ^ (prefixWord ++ tailWord_6611079).sum := by decide
  have hdescent : baseEnd_6611079 < baseStart_6611079 := by decide
  rcases family_descends (prefixWord ++ tailWord_6611079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6611146 : List Nat := [3, 1, 2, 1, 3, 1, 2, 2, 4, 1, 3]
def baseStart_6611146 : Nat := 118140960795 + 6611146 * 2 ^ 59
def prefixEnd_6611146 : Nat := 4983230072969 + 3 ^ 40 * 6611146 * 2
def baseEnd_6611146 : Nat := 3394695575049296094570899

theorem tailTrace_6611146 : CollatzResearch.WordTrace tailWord_6611146 prefixEnd_6611146 3394695575049296094570899 := by
  unfold tailWord_6611146
  simp only [CollatzResearch.WordTrace]
  refine ⟨60282076026738652672539323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160752202737969740460104861 60282076026738652672539323)
  ·
    refine ⟨90423114040107979008808985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60282076026738652672539323 90423114040107979008808985)
    ·
      refine ⟨67817335530080984256606739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90423114040107979008808985 67817335530080984256606739)
      ·
        refine ⟨101726003295121476384910109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67817335530080984256606739 101726003295121476384910109)
        ·
          refine ⟨38147251235670553644341291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101726003295121476384910109 38147251235670553644341291)
          ·
            refine ⟨57220876853505830466511937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38147251235670553644341291 57220876853505830466511937)
            ·
              refine ⟨42915657640129372849883953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57220876853505830466511937 42915657640129372849883953)
              ·
                refine ⟨32186743230097029637412965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42915657640129372849883953 32186743230097029637412965)
                ·
                  refine ⟨6035014355643193057014931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32186743230097029637412965 6035014355643193057014931)
                  ·
                    refine ⟨9052521533464789585522397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6035014355643193057014931 9052521533464789585522397)
                    ·
                      refine ⟨3394695575049296094570899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9052521533464789585522397 3394695575049296094570899)
                      ·
                        rfl

theorem cell23_6611146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 2, 4, 1, 3].length) (baseStart_6611146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6611146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6611146 prefixEnd_6611146 := by exact prefixLift 6611146
  have htrace : WordTrace (prefixWord ++ tailWord_6611146) baseStart_6611146 baseEnd_6611146 := by
    simpa [prefixWord, tailWord_6611146, baseEnd_6611146] using wordTrace_append hprefix tailTrace_6611146
  have hstable : (prefixWord ++ tailWord_6611146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6611146).length < 2 ^ (prefixWord ++ tailWord_6611146).sum := by decide
  have hdescent : baseEnd_6611146 < baseStart_6611146 := by decide
  rcases family_descends (prefixWord ++ tailWord_6611146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6611150 : List Nat := [4, 1, 1, 1, 4, 3, 2, 1, 1, 2, 3]
def baseStart_6611150 : Nat := 118140960795 + 6611150 * 2 ^ 59
def prefixEnd_6611150 : Nat := 4983230072969 + 3 ^ 40 * 6611150 * 2
def baseEnd_6611150 : Nat := 3394697628971914078920881

theorem tailTrace_6611150 : CollatzResearch.WordTrace tailWord_6611150 prefixEnd_6611150 3394697628971914078920881 := by
  unfold tailWord_6611150
  simp only [CollatzResearch.WordTrace]
  refine ⟨30141056249867514921662863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 160752299999293412915535269 30141056249867514921662863)
  ·
    refine ⟨45211584374801272382494295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30141056249867514921662863 45211584374801272382494295)
    ·
      refine ⟨67817376562201908573741443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45211584374801272382494295 67817376562201908573741443)
      ·
        refine ⟨101726064843302862860612165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67817376562201908573741443 101726064843302862860612165)
        ·
          refine ⟨19073637158119286786364781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 101726064843302862860612165 19073637158119286786364781)
          ·
            refine ⟨7152613934294732544886793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19073637158119286786364781 7152613934294732544886793)
            ·
              refine ⟨5364460450721049408665095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7152613934294732544886793 5364460450721049408665095)
              ·
                refine ⟨8046690676081574112997643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5364460450721049408665095 8046690676081574112997643)
                ·
                  refine ⟨12070036014122361169496465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8046690676081574112997643 12070036014122361169496465)
                  ·
                    refine ⟨9052527010591770877122349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12070036014122361169496465 9052527010591770877122349)
                    ·
                      refine ⟨3394697628971914078920881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9052527010591770877122349 3394697628971914078920881)
                      ·
                        rfl

theorem cell23_6611150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 2, 1, 1, 2, 3].length) (baseStart_6611150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6611150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6611150 prefixEnd_6611150 := by exact prefixLift 6611150
  have htrace : WordTrace (prefixWord ++ tailWord_6611150) baseStart_6611150 baseEnd_6611150 := by
    simpa [prefixWord, tailWord_6611150, baseEnd_6611150] using wordTrace_append hprefix tailTrace_6611150
  have hstable : (prefixWord ++ tailWord_6611150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6611150).length < 2 ^ (prefixWord ++ tailWord_6611150).sum := by decide
  have hdescent : baseEnd_6611150 < baseStart_6611150 := by decide
  rcases family_descends (prefixWord ++ tailWord_6611150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6611219 : List Nat := [1, 1, 1, 2, 1, 3, 1, 3, 4, 3, 3]
def baseStart_6611219 : Nat := 118140960795 + 6611219 * 2 ^ 59
def prefixEnd_6611219 : Nat := 4983230072969 + 3 ^ 40 * 6611219 * 2
def baseEnd_6611219 : Nat := 3394733059137074308958063

theorem tailTrace_6611219 : CollatzResearch.WordTrace tailWord_6611219 prefixEnd_6611219 3394733059137074308958063 := by
  unfold tailWord_6611219
  simp only [CollatzResearch.WordTrace]
  refine ⟨241130966635690144157564711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160753977757126762771709807 241130966635690144157564711)
  ·
    refine ⟨361696449953535216236347067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241130966635690144157564711 361696449953535216236347067)
    ·
      refine ⟨542544674930302824354520601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 361696449953535216236347067 542544674930302824354520601)
      ·
        refine ⟨406908506197727118265890451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 542544674930302824354520601 406908506197727118265890451)
        ·
          refine ⟨610362759296590677398835677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 406908506197727118265890451 610362759296590677398835677)
          ·
            refine ⟨228886034736221504024563379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 610362759296590677398835677 228886034736221504024563379)
            ·
              refine ⟨343329052104332256036845069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 228886034736221504024563379 343329052104332256036845069)
              ·
                refine ⟨128748394539124596013816901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 343329052104332256036845069 128748394539124596013816901)
                ·
                  refine ⟨24140323976085861752590669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 128748394539124596013816901 24140323976085861752590669)
                  ·
                    refine ⟨9052621491032198157221501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24140323976085861752590669 9052621491032198157221501)
                    ·
                      refine ⟨3394733059137074308958063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9052621491032198157221501 3394733059137074308958063)
                      ·
                        rfl

theorem cell23_6611219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 3, 4, 3, 3].length) (baseStart_6611219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6611219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6611219 prefixEnd_6611219 := by exact prefixLift 6611219
  have htrace : WordTrace (prefixWord ++ tailWord_6611219) baseStart_6611219 baseEnd_6611219 := by
    simpa [prefixWord, tailWord_6611219, baseEnd_6611219] using wordTrace_append hprefix tailTrace_6611219
  have hstable : (prefixWord ++ tailWord_6611219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6611219).length < 2 ^ (prefixWord ++ tailWord_6611219).sum := by decide
  have hdescent : baseEnd_6611219 < baseStart_6611219 := by decide
  rcases family_descends (prefixWord ++ tailWord_6611219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6611276 : List Nat := [2, 2, 1, 3, 2, 1, 1, 4, 2, 1, 4]
def baseStart_6611276 : Nat := 118140960795 + 6611276 * 2 ^ 59
def prefixEnd_6611276 : Nat := 4983230072969 + 3 ^ 40 * 6611276 * 2
def baseEnd_6611276 : Nat := 3394762327534380585945301

theorem tailTrace_6611276 : CollatzResearch.WordTrace tailWord_6611276 prefixEnd_6611276 3394762327534380585945301 := by
  unfold tailWord_6611276
  simp only [CollatzResearch.WordTrace]
  refine ⟨120566522798241821446194841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160755363730989095261593121 120566522798241821446194841)
  ·
    refine ⟨90424892098681366084646131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120566522798241821446194841 90424892098681366084646131)
    ·
      refine ⟨135637338148022049126969197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90424892098681366084646131 135637338148022049126969197)
      ·
        refine ⟨50864001805508268422613449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135637338148022049126969197 50864001805508268422613449)
        ·
          refine ⟨38148001354131201316960087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50864001805508268422613449 38148001354131201316960087)
          ·
            refine ⟨57222002031196801975440131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38148001354131201316960087 57222002031196801975440131)
            ·
              refine ⟨85833003046795202963160197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57222002031196801975440131 85833003046795202963160197)
              ·
                refine ⟨16093688071274100555592537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 85833003046795202963160197 16093688071274100555592537)
                ·
                  refine ⟨12070266053455575416694403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16093688071274100555592537 12070266053455575416694403)
                  ·
                    refine ⟨18105399080183363125041605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12070266053455575416694403 18105399080183363125041605)
                    ·
                      refine ⟨3394762327534380585945301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18105399080183363125041605 3394762327534380585945301)
                      ·
                        rfl

theorem cell23_6611276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 4, 2, 1, 4].length) (baseStart_6611276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6611276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6611276 prefixEnd_6611276 := by exact prefixLift 6611276
  have htrace : WordTrace (prefixWord ++ tailWord_6611276) baseStart_6611276 baseEnd_6611276 := by
    simpa [prefixWord, tailWord_6611276, baseEnd_6611276] using wordTrace_append hprefix tailTrace_6611276
  have hstable : (prefixWord ++ tailWord_6611276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6611276).length < 2 ^ (prefixWord ++ tailWord_6611276).sum := by decide
  have hdescent : baseEnd_6611276 < baseStart_6611276 := by decide
  rcases family_descends (prefixWord ++ tailWord_6611276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6611289 : List Nat := [1, 2, 1, 2, 2, 2, 1, 2, 2, 4, 4]
def baseStart_6611289 : Nat := 118140960795 + 6611289 * 2 ^ 59
def prefixEnd_6611289 : Nat := 4983230072969 + 3 ^ 40 * 6611289 * 2
def baseEnd_6611289 : Nat := 3394769002782889035082741

theorem tailTrace_6611289 : CollatzResearch.WordTrace tailWord_6611289 prefixEnd_6611289 3394769002782889035082741 := by
  unfold tailWord_6611289
  simp only [CollatzResearch.WordTrace]
  refine ⟨241133519745436546112612921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160755679830291030741741947 241133519745436546112612921)
  ·
    refine ⟨180850139809077409584459691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241133519745436546112612921 180850139809077409584459691)
    ·
      refine ⟨271275209713616114376689537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180850139809077409584459691 271275209713616114376689537)
      ·
        refine ⟨203456407285212085782517153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 271275209713616114376689537 203456407285212085782517153)
        ·
          refine ⟨152592305463909064336887865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 203456407285212085782517153 152592305463909064336887865)
          ·
            refine ⟨114444229097931798252665899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152592305463909064336887865 114444229097931798252665899)
            ·
              refine ⟨171666343646897697378998849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114444229097931798252665899 171666343646897697378998849)
              ·
                refine ⟨128749757735173273034249137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 171666343646897697378998849 128749757735173273034249137)
                ·
                  refine ⟨96562318301379954775686853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 128749757735173273034249137 96562318301379954775686853)
                  ·
                    refine ⟨18105434681508741520441285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 96562318301379954775686853 18105434681508741520441285)
                    ·
                      refine ⟨3394769002782889035082741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18105434681508741520441285 3394769002782889035082741)
                      ·
                        rfl

theorem cell23_6611289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 2, 4, 4].length) (baseStart_6611289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6611289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6611289 prefixEnd_6611289 := by exact prefixLift 6611289
  have htrace : WordTrace (prefixWord ++ tailWord_6611289) baseStart_6611289 baseEnd_6611289 := by
    simpa [prefixWord, tailWord_6611289, baseEnd_6611289] using wordTrace_append hprefix tailTrace_6611289
  have hstable : (prefixWord ++ tailWord_6611289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6611289).length < 2 ^ (prefixWord ++ tailWord_6611289).sum := by decide
  have hdescent : baseEnd_6611289 < baseStart_6611289 := by decide
  rcases family_descends (prefixWord ++ tailWord_6611289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6611303 : List Nat := [1, 1, 5, 1, 3, 2, 1, 2, 3, 4]
def baseStart_6611303 : Nat := 118140960795 + 6611303 * 2 ^ 59
def prefixEnd_6611303 : Nat := 4983230072969 + 3 ^ 40 * 6611303 * 2
def baseEnd_6611303 : Nat := 1131592063837350660102559

theorem tailTrace_6611303 : CollatzResearch.WordTrace tailWord_6611303 prefixEnd_6611303 1131592063837350660102559 := by
  unfold tailWord_6611303
  simp only [CollatzResearch.WordTrace]
  refine ⟨241134030367385826503622563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160756020244923884335748375 241134030367385826503622563)
  ·
    refine ⟨361701045551078739755433845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241134030367385826503622563 361701045551078739755433845)
    ·
      refine ⟨33909473020413631852071923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 361701045551078739755433845 33909473020413631852071923)
      ·
        refine ⟨50864209530620447778107885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33909473020413631852071923 50864209530620447778107885)
        ·
          refine ⟨19074078573982667916790457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50864209530620447778107885 19074078573982667916790457)
          ·
            refine ⟨14305558930487000937592843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19074078573982667916790457 14305558930487000937592843)
            ·
              refine ⟨21458338395730501406389265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14305558930487000937592843 21458338395730501406389265)
              ·
                refine ⟨16093753796797876054791949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21458338395730501406389265 16093753796797876054791949)
                ·
                  refine ⟨6035157673799203520546981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16093753796797876054791949 6035157673799203520546981)
                  ·
                    refine ⟨1131592063837350660102559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6035157673799203520546981 1131592063837350660102559)
                    ·
                      rfl

theorem cell23_6611303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 2, 3, 4].length) (baseStart_6611303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6611303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6611303 prefixEnd_6611303 := by exact prefixLift 6611303
  have htrace : WordTrace (prefixWord ++ tailWord_6611303) baseStart_6611303 baseEnd_6611303 := by
    simpa [prefixWord, tailWord_6611303, baseEnd_6611303] using wordTrace_append hprefix tailTrace_6611303
  have hstable : (prefixWord ++ tailWord_6611303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6611303).length < 2 ^ (prefixWord ++ tailWord_6611303).sum := by decide
  have hdescent : baseEnd_6611303 < baseStart_6611303 := by decide
  rcases family_descends (prefixWord ++ tailWord_6611303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6611363 : List Nat := [1, 1, 1, 4, 1, 5, 2, 2, 1, 5]
def baseStart_6611363 : Nat := 118140960795 + 6611363 * 2 ^ 59
def prefixEnd_6611363 : Nat := 4983230072969 + 3 ^ 40 * 6611363 * 2
def baseEnd_6611363 : Nat := 1131602333450440581852467

theorem tailTrace_6611363 : CollatzResearch.WordTrace tailWord_6611363 prefixEnd_6611363 1131602333450440581852467 := by
  unfold tailWord_6611363
  simp only [CollatzResearch.WordTrace]
  refine ⟨241136218747168456750806743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160757479164778971167204495 241136218747168456750806743)
  ·
    refine ⟨361704328120752685126210115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241136218747168456750806743 361704328120752685126210115)
    ·
      refine ⟨542556492181129027689315173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 361704328120752685126210115 542556492181129027689315173)
      ·
        refine ⟨101729342283961692691746595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 542556492181129027689315173 101729342283961692691746595)
        ·
          refine ⟨152594013425942539037619893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101729342283961692691746595 152594013425942539037619893)
          ·
            refine ⟨14305688758682113034776865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 152594013425942539037619893 14305688758682113034776865)
            ·
              refine ⟨10729266569011584776082649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14305688758682113034776865 10729266569011584776082649)
              ·
                refine ⟨8046949926758688582061987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10729266569011584776082649 8046949926758688582061987)
                ·
                  refine ⟨12070424890138032873092981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8046949926758688582061987 12070424890138032873092981)
                  ·
                    refine ⟨1131602333450440581852467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12070424890138032873092981 1131602333450440581852467)
                    ·
                      rfl

theorem cell23_6611363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 2, 2, 1, 5].length) (baseStart_6611363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6611363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6611363 prefixEnd_6611363 := by exact prefixLift 6611363
  have htrace : WordTrace (prefixWord ++ tailWord_6611363) baseStart_6611363 baseEnd_6611363 := by
    simpa [prefixWord, tailWord_6611363, baseEnd_6611363] using wordTrace_append hprefix tailTrace_6611363
  have hstable : (prefixWord ++ tailWord_6611363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6611363).length < 2 ^ (prefixWord ++ tailWord_6611363).sum := by decide
  have hdescent : baseEnd_6611363 < baseStart_6611363 := by decide
  rcases family_descends (prefixWord ++ tailWord_6611363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6611377 : List Nat := [1, 2, 2, 4, 1, 2, 3, 3, 1, 1, 3]
def baseStart_6611377 : Nat := 118140960795 + 6611377 * 2 ^ 59
def prefixEnd_6611377 : Nat := 4983230072969 + 3 ^ 40 * 6611377 * 2
def baseEnd_6611377 : Nat := 3394814189080484690782337

theorem tailTrace_6611377 : CollatzResearch.WordTrace tailWord_6611377 prefixEnd_6611377 3394814189080484690782337 := by
  unfold tailWord_6611377
  simp only [CollatzResearch.WordTrace]
  refine ⟨241136729369117737141816385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160757819579411824761210923 241136729369117737141816385)
  ·
    refine ⟨180852547026838302856362289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241136729369117737141816385 180852547026838302856362289)
    ·
      refine ⟨135639410270128727142271717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180852547026838302856362289 135639410270128727142271717)
      ·
        refine ⟨25432389425649136339175947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 135639410270128727142271717 25432389425649136339175947)
        ·
          refine ⟨38148584138473704508763921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25432389425649136339175947 38148584138473704508763921)
          ·
            refine ⟨28611438103855278381572941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38148584138473704508763921 28611438103855278381572941)
            ·
              refine ⟨10729289288945729393089853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28611438103855278381572941 10729289288945729393089853)
              ·
                refine ⟨4023483483354648522408695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10729289288945729393089853 4023483483354648522408695)
                ·
                  refine ⟨6035225225031972783613043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4023483483354648522408695 6035225225031972783613043)
                  ·
                    refine ⟨9052837837547959175419565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6035225225031972783613043 9052837837547959175419565)
                    ·
                      refine ⟨3394814189080484690782337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9052837837547959175419565 3394814189080484690782337)
                      ·
                        rfl

theorem cell23_6611377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 3, 3, 1, 1, 3].length) (baseStart_6611377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6611377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6611377 prefixEnd_6611377 := by exact prefixLift 6611377
  have htrace : WordTrace (prefixWord ++ tailWord_6611377) baseStart_6611377 baseEnd_6611377 := by
    simpa [prefixWord, tailWord_6611377, baseEnd_6611377] using wordTrace_append hprefix tailTrace_6611377
  have hstable : (prefixWord ++ tailWord_6611377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6611377).length < 2 ^ (prefixWord ++ tailWord_6611377).sum := by decide
  have hdescent : baseEnd_6611377 < baseStart_6611377 := by decide
  rcases family_descends (prefixWord ++ tailWord_6611377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6611383 : List Nat := [1, 1, 3, 1, 3, 3, 2, 3, 1, 1, 4]
def baseStart_6611383 : Nat := 118140960795 + 6611383 * 2 ^ 59
def prefixEnd_6611383 : Nat := 4983230072969 + 3 ^ 40 * 6611383 * 2
def baseEnd_6611383 : Nat := 3394817269964411667307309

theorem tailTrace_6611383 : CollatzResearch.WordTrace tailWord_6611383 prefixEnd_6611383 3394817269964411667307309 := by
  unfold tailWord_6611383
  simp only [CollatzResearch.WordTrace]
  refine ⟨241136948207096000166534803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160757965471397333444356535 241136948207096000166534803)
  ·
    refine ⟨361705422310644000249802205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241136948207096000166534803 361705422310644000249802205)
    ·
      refine ⟨135639533366491500093675827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 361705422310644000249802205 135639533366491500093675827)
      ·
        refine ⟨203459300049737250140513741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135639533366491500093675827 203459300049737250140513741)
        ·
          refine ⟨76297237518651468802692653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 203459300049737250140513741 76297237518651468802692653)
          ·
            refine ⟨28611464069494300801009745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76297237518651468802692653 28611464069494300801009745)
            ·
              refine ⟨21458598052120725600757309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28611464069494300801009745 21458598052120725600757309)
              ·
                refine ⟨8046974269545272100283991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21458598052120725600757309 8046974269545272100283991)
                ·
                  refine ⟨12070461404317908150425987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8046974269545272100283991 12070461404317908150425987)
                  ·
                    refine ⟨18105692106476862225638981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12070461404317908150425987 18105692106476862225638981)
                    ·
                      refine ⟨3394817269964411667307309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18105692106476862225638981 3394817269964411667307309)
                      ·
                        rfl

theorem cell23_6611383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 3, 1, 1, 4].length) (baseStart_6611383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6611383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6611383 prefixEnd_6611383 := by exact prefixLift 6611383
  have htrace : WordTrace (prefixWord ++ tailWord_6611383) baseStart_6611383 baseEnd_6611383 := by
    simpa [prefixWord, tailWord_6611383, baseEnd_6611383] using wordTrace_append hprefix tailTrace_6611383
  have hstable : (prefixWord ++ tailWord_6611383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6611383).length < 2 ^ (prefixWord ++ tailWord_6611383).sum := by decide
  have hdescent : baseEnd_6611383 < baseStart_6611383 := by decide
  rcases family_descends (prefixWord ++ tailWord_6611383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6611433 : List Nat := [1, 2, 1, 1, 1, 2, 1, 6, 4, 1, 3]
def baseStart_6611433 : Nat := 118140960795 + 6611433 * 2 ^ 59
def prefixEnd_6611433 : Nat := 4983230072969 + 3 ^ 40 * 6611433 * 2
def baseEnd_6611433 : Nat := 3394842943997136471682079

theorem tailTrace_6611433 : CollatzResearch.WordTrace tailWord_6611433 prefixEnd_6611433 3394842943997136471682079 := by
  unfold tailWord_6611433
  simp only [CollatzResearch.WordTrace]
  refine ⟨241138771856914858705854953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160759181237943239137236635 241138771856914858705854953)
  ·
    refine ⟨180854078892686144029391215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241138771856914858705854953 180854078892686144029391215)
    ·
      refine ⟨271281118339029216044086823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180854078892686144029391215 271281118339029216044086823)
      ·
        refine ⟨406921677508543824066130235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271281118339029216044086823 406921677508543824066130235)
        ·
          refine ⟨610382516262815736099195353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 406921677508543824066130235 610382516262815736099195353)
          ·
            refine ⟨457786887197111802074396515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 610382516262815736099195353 457786887197111802074396515)
            ·
              refine ⟨686680330795667703111594773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 457786887197111802074396515 686680330795667703111594773)
              ·
                refine ⟨32188140506046923583356005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 686680330795667703111594773 32188140506046923583356005)
                ·
                  refine ⟨6035276344883798171879251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32188140506046923583356005 6035276344883798171879251)
                  ·
                    refine ⟨9052914517325697257818877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6035276344883798171879251 9052914517325697257818877)
                    ·
                      refine ⟨3394842943997136471682079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9052914517325697257818877 3394842943997136471682079)
                      ·
                        rfl

theorem cell23_6611433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 6, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 6, 4, 1, 3].length) (baseStart_6611433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6611433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6611433 prefixEnd_6611433 := by exact prefixLift 6611433
  have htrace : WordTrace (prefixWord ++ tailWord_6611433) baseStart_6611433 baseEnd_6611433 := by
    simpa [prefixWord, tailWord_6611433, baseEnd_6611433] using wordTrace_append hprefix tailTrace_6611433
  have hstable : (prefixWord ++ tailWord_6611433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6611433).length < 2 ^ (prefixWord ++ tailWord_6611433).sum := by decide
  have hdescent : baseEnd_6611433 < baseStart_6611433 := by decide
  rcases family_descends (prefixWord ++ tailWord_6611433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6611501 : List Nat := [1, 5, 4, 1, 1, 1, 1, 1, 4, 1, 3]
def baseStart_6611501 : Nat := 118140960795 + 6611501 * 2 ^ 59
def prefixEnd_6611501 : Nat := 4983230072969 + 3 ^ 40 * 6611501 * 2
def baseEnd_6611501 : Nat := 3394877860681642205631767

theorem tailTrace_6611501 : CollatzResearch.WordTrace tailWord_6611501 prefixEnd_6611501 3394877860681642205631767 := by
  unfold tailWord_6611501
  simp only [CollatzResearch.WordTrace]
  refine ⟨241141252020668506319330357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160760834680445670879553571 241141252020668506319330357)
  ·
    refine ⟨22606992376937672467437221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 241141252020668506319330357 22606992376937672467437221)
    ·
      refine ⟨4238811070675813587644479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22606992376937672467437221 4238811070675813587644479)
      ·
        refine ⟨6358216606013720381466719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4238811070675813587644479 6358216606013720381466719)
        ·
          refine ⟨9537324909020580572200079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6358216606013720381466719 9537324909020580572200079)
          ·
            refine ⟨14305987363530870858300119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9537324909020580572200079 14305987363530870858300119)
            ·
              refine ⟨21458981045296306287450179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14305987363530870858300119 21458981045296306287450179)
              ·
                refine ⟨32188471567944459431175269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21458981045296306287450179 32188471567944459431175269)
                ·
                  refine ⟨6035338418989586143345363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32188471567944459431175269 6035338418989586143345363)
                  ·
                    refine ⟨9053007628484379215018045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6035338418989586143345363 9053007628484379215018045)
                    ·
                      refine ⟨3394877860681642205631767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9053007628484379215018045 3394877860681642205631767)
                      ·
                        rfl

theorem cell23_6611501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_6611501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6611501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6611501 prefixEnd_6611501 := by exact prefixLift 6611501
  have htrace : WordTrace (prefixWord ++ tailWord_6611501) baseStart_6611501 baseEnd_6611501 := by
    simpa [prefixWord, tailWord_6611501, baseEnd_6611501] using wordTrace_append hprefix tailTrace_6611501
  have hstable : (prefixWord ++ tailWord_6611501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6611501).length < 2 ^ (prefixWord ++ tailWord_6611501).sum := by decide
  have hdescent : baseEnd_6611501 < baseStart_6611501 := by decide
  rcases family_descends (prefixWord ++ tailWord_6611501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6611513 : List Nat := [1, 2, 1, 5, 1, 1, 4, 1, 7]
def baseStart_6611513 : Nat := 118140960795 + 6611513 * 2 ^ 59
def prefixEnd_6611513 : Nat := 4983230072969 + 3 ^ 40 * 6611513 * 2
def baseEnd_6611513 : Nat := 377209335827721795409079

theorem tailTrace_6611513 : CollatzResearch.WordTrace tailWord_6611513 prefixEnd_6611513 377209335827721795409079 := by
  unfold tailWord_6611513
  simp only [CollatzResearch.WordTrace]
  refine ⟨241141689696625032368767193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160761126464416688245844795 241141689696625032368767193)
  ·
    refine ⟨180856267272468774276575395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241141689696625032368767193 180856267272468774276575395)
    ·
      refine ⟨271284400908703161414863093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180856267272468774276575395 271284400908703161414863093)
      ·
        refine ⟨25432912585190921382643415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 271284400908703161414863093 25432912585190921382643415)
        ·
          refine ⟨38149368877786382073965123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25432912585190921382643415 38149368877786382073965123)
          ·
            refine ⟨57224053316679573110947685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38149368877786382073965123 57224053316679573110947685)
            ·
              refine ⟨10729509996877419958302691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57224053316679573110947685 10729509996877419958302691)
              ·
                refine ⟨16094264995316129937454037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10729509996877419958302691 16094264995316129937454037)
                ·
                  refine ⟨377209335827721795409079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16094264995316129937454037 377209335827721795409079)
                  ·
                    rfl

theorem cell23_6611513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 4, 1, 7].length) (baseStart_6611513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6611513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6611513 prefixEnd_6611513 := by exact prefixLift 6611513
  have htrace : WordTrace (prefixWord ++ tailWord_6611513) baseStart_6611513 baseEnd_6611513 := by
    simpa [prefixWord, tailWord_6611513, baseEnd_6611513] using wordTrace_append hprefix tailTrace_6611513
  have hstable : (prefixWord ++ tailWord_6611513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6611513).length < 2 ^ (prefixWord ++ tailWord_6611513).sum := by decide
  have hdescent : baseEnd_6611513 < baseStart_6611513 := by decide
  rcases family_descends (prefixWord ++ tailWord_6611513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6611536 : List Nat := [2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 7]
def baseStart_6611536 : Nat := 118140960795 + 6611536 * 2 ^ 59
def prefixEnd_6611536 : Nat := 4983230072969 + 3 ^ 40 * 6611536 * 2
def baseEnd_6611536 : Nat := 3394895832504549568694105

theorem tailTrace_6611536 : CollatzResearch.WordTrace tailWord_6611536 prefixEnd_6611536 3394895832504549568694105 := by
  unfold tailWord_6611536
  simp only [CollatzResearch.WordTrace]
  refine ⟨120571264287770853648427231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160761685717027804864569641 120571264287770853648427231)
  ·
    refine ⟨180856896431656280472640847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120571264287770853648427231 180856896431656280472640847)
    ·
      refine ⟨271285344647484420708961271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180856896431656280472640847 271285344647484420708961271)
      ·
        refine ⟨406928016971226631063441907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271285344647484420708961271 406928016971226631063441907)
        ·
          refine ⟨610392025456839946595162861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 406928016971226631063441907 610392025456839946595162861)
          ·
            refine ⟨228897009546314979973186073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 610392025456839946595162861 228897009546314979973186073)
            ·
              refine ⟨171672757159736234979889555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 228897009546314979973186073 171672757159736234979889555)
              ·
                refine ⟨257509135739604352469834333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 171672757159736234979889555 257509135739604352469834333)
                ·
                  refine ⟨96565925902351632176187875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 257509135739604352469834333 96565925902351632176187875)
                  ·
                    refine ⟨144848888853527448264281813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 96565925902351632176187875 144848888853527448264281813)
                    ·
                      refine ⟨3394895832504549568694105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 144848888853527448264281813 3394895832504549568694105)
                      ·
                        rfl

theorem cell23_6611536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 7].length) (baseStart_6611536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6611536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6611536 prefixEnd_6611536 := by exact prefixLift 6611536
  have htrace : WordTrace (prefixWord ++ tailWord_6611536) baseStart_6611536 baseEnd_6611536 := by
    simpa [prefixWord, tailWord_6611536, baseEnd_6611536] using wordTrace_append hprefix tailTrace_6611536
  have hstable : (prefixWord ++ tailWord_6611536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6611536).length < 2 ^ (prefixWord ++ tailWord_6611536).sum := by decide
  have hdescent : baseEnd_6611536 < baseStart_6611536 := by decide
  rcases family_descends (prefixWord ++ tailWord_6611536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6611543 : List Nat := [1, 1, 3, 2, 2, 2, 2, 3, 2, 5]
def baseStart_6611543 : Nat := 118140960795 + 6611543 * 2 ^ 59
def prefixEnd_6611543 : Nat := 4983230072969 + 3 ^ 40 * 6611543 * 2
def baseEnd_6611543 : Nat := 1131633142289710347102191

theorem tailTrace_6611543 : CollatzResearch.WordTrace tailWord_6611543 prefixEnd_6611543 1131633142289710347102191 := by
  unfold tailWord_6611543
  simp only [CollatzResearch.WordTrace]
  refine ⟨241142783886516347492359283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160761855924344231661572855 241142783886516347492359283)
  ·
    refine ⟨361714175829774521238538925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241142783886516347492359283 361714175829774521238538925)
    ·
      refine ⟨135642815936165445464452097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 361714175829774521238538925 135642815936165445464452097)
      ·
        refine ⟨101732111952124084098339073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135642815936165445464452097 101732111952124084098339073)
        ·
          refine ⟨76299083964093063073754305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101732111952124084098339073 76299083964093063073754305)
          ·
            refine ⟨57224312973069797305315729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76299083964093063073754305 57224312973069797305315729)
            ·
              refine ⟨42918234729802347978986797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57224312973069797305315729 42918234729802347978986797)
              ·
                refine ⟨16094338023675880492120049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42918234729802347978986797 16094338023675880492120049)
                ·
                  refine ⟨12070753517756910369090037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16094338023675880492120049 12070753517756910369090037)
                  ·
                    refine ⟨1131633142289710347102191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12070753517756910369090037 1131633142289710347102191)
                    ·
                      rfl

theorem cell23_6611543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 3, 2, 5].length) (baseStart_6611543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6611543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6611543 prefixEnd_6611543 := by exact prefixLift 6611543
  have htrace : WordTrace (prefixWord ++ tailWord_6611543) baseStart_6611543 baseEnd_6611543 := by
    simpa [prefixWord, tailWord_6611543, baseEnd_6611543] using wordTrace_append hprefix tailTrace_6611543
  have hstable : (prefixWord ++ tailWord_6611543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6611543).length < 2 ^ (prefixWord ++ tailWord_6611543).sum := by decide
  have hdescent : baseEnd_6611543 < baseStart_6611543 := by decide
  rcases family_descends (prefixWord ++ tailWord_6611543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6611570 : List Nat := [3, 2, 1, 2, 4, 1, 1, 1, 1, 2, 5]
def baseStart_6611570 : Nat := 118140960795 + 6611570 * 2 ^ 59
def prefixEnd_6611570 : Nat := 4983230072969 + 3 ^ 40 * 6611570 * 2
def baseEnd_6611570 : Nat := 3394913290846802435668949

theorem tailTrace_6611570 : CollatzResearch.WordTrace tailWord_6611570 prefixEnd_6611570 3394913290846802435668949 := by
  unfold tailWord_6611570
  simp only [CollatzResearch.WordTrace]
  refine ⟨60285942164354632775898041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160762512438279020735728109 60285942164354632775898041)
  ·
    refine ⟨45214456623265974581923531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60285942164354632775898041 45214456623265974581923531)
    ·
      refine ⟨67821684934898961872885297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45214456623265974581923531 67821684934898961872885297)
      ·
        refine ⟨50866263701174221404663973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67821684934898961872885297 50866263701174221404663973)
        ·
          refine ⟨9537424443970166513374495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50866263701174221404663973 9537424443970166513374495)
          ·
            refine ⟨14306136665955249770061743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9537424443970166513374495 14306136665955249770061743)
            ·
              refine ⟨21459204998932874655092615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14306136665955249770061743 21459204998932874655092615)
              ·
                refine ⟨32188807498399311982638923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21459204998932874655092615 32188807498399311982638923)
                ·
                  refine ⟨48283211247598967973958385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32188807498399311982638923 48283211247598967973958385)
                  ·
                    refine ⟨36212408435699225980468789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48283211247598967973958385 36212408435699225980468789)
                    ·
                      refine ⟨3394913290846802435668949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36212408435699225980468789 3394913290846802435668949)
                      ·
                        rfl

theorem cell23_6611570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 1, 1, 2, 5].length) (baseStart_6611570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6611570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6611570 prefixEnd_6611570 := by exact prefixLift 6611570
  have htrace : WordTrace (prefixWord ++ tailWord_6611570) baseStart_6611570 baseEnd_6611570 := by
    simpa [prefixWord, tailWord_6611570, baseEnd_6611570] using wordTrace_append hprefix tailTrace_6611570
  have hstable : (prefixWord ++ tailWord_6611570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6611570).length < 2 ^ (prefixWord ++ tailWord_6611570).sum := by decide
  have hdescent : baseEnd_6611570 < baseStart_6611570 := by decide
  rcases family_descends (prefixWord ++ tailWord_6611570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6611580 : List Nat := [2, 2, 2, 1, 1, 2, 2, 3, 2, 4, 2]
def baseStart_6611580 : Nat := 118140960795 + 6611580 * 2 ^ 59
def prefixEnd_6611580 : Nat := 4983230072969 + 3 ^ 40 * 6611580 * 2
def baseEnd_6611580 : Nat := 3394918425653347396543903

theorem tailTrace_6611580 : CollatzResearch.WordTrace tailWord_6611580 prefixEnd_6611580 3394918425653347396543903 := by
  unfold tailWord_6611580
  simp only [CollatzResearch.WordTrace]
  refine ⟨120572066693691151405728097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160762755591588201874304129 120572066693691151405728097)
  ·
    refine ⟨90429050020268363554296073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120572066693691151405728097 90429050020268363554296073)
    ·
      refine ⟨67821787515201272665722055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90429050020268363554296073 67821787515201272665722055)
      ·
        refine ⟨101732681272801908998583083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67821787515201272665722055 101732681272801908998583083)
        ·
          refine ⟨152599021909202863497874625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101732681272801908998583083 152599021909202863497874625)
          ·
            refine ⟨114449266431902147623405969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152599021909202863497874625 114449266431902147623405969)
            ·
              refine ⟨85836949823926610717554477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114449266431902147623405969 85836949823926610717554477)
              ·
                refine ⟨32188856183972479019082929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85836949823926610717554477 32188856183972479019082929)
                ·
                  refine ⟨24141642137979359264312197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32188856183972479019082929 24141642137979359264312197)
                  ·
                    refine ⟨4526557900871129862058537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24141642137979359264312197 4526557900871129862058537)
                    ·
                      refine ⟨3394918425653347396543903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4526557900871129862058537 3394918425653347396543903)
                      ·
                        rfl

theorem cell23_6611580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 3, 2, 4, 2].length) (baseStart_6611580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6611580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6611580 prefixEnd_6611580 := by exact prefixLift 6611580
  have htrace : WordTrace (prefixWord ++ tailWord_6611580) baseStart_6611580 baseEnd_6611580 := by
    simpa [prefixWord, tailWord_6611580, baseEnd_6611580] using wordTrace_append hprefix tailTrace_6611580
  have hstable : (prefixWord ++ tailWord_6611580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6611580).length < 2 ^ (prefixWord ++ tailWord_6611580).sum := by decide
  have hdescent : baseEnd_6611580 < baseStart_6611580 := by decide
  rcases family_descends (prefixWord ++ tailWord_6611580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6611583 : List Nat := [1, 1, 2, 2, 1, 1, 1, 6, 1, 4, 3]
def baseStart_6611583 : Nat := 118140960795 + 6611583 * 2 ^ 59
def prefixEnd_6611583 : Nat := 4983230072969 + 3 ^ 40 * 6611583 * 2
def baseEnd_6611583 : Nat := 3394919966095310884806389

theorem tailTrace_6611583 : CollatzResearch.WordTrace tailWord_6611583 prefixEnd_6611583 3394919966095310884806389 := by
  unfold tailWord_6611583
  simp only [CollatzResearch.WordTrace]
  refine ⟨241144242806371434323815403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160762828537580956215876935 241144242806371434323815403)
  ·
    refine ⟨361716364209557151485723105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241144242806371434323815403 361716364209557151485723105)
    ·
      refine ⟨271287273157167863614292329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 361716364209557151485723105 271287273157167863614292329)
      ·
        refine ⟨203465454867875897710719247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 271287273157167863614292329 203465454867875897710719247)
        ·
          refine ⟨305198182301813846566078871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203465454867875897710719247 305198182301813846566078871)
          ·
            refine ⟨457797273452720769849118307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 305198182301813846566078871 457797273452720769849118307)
            ·
              refine ⟨686695910179081154773677461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 457797273452720769849118307 686695910179081154773677461)
              ·
                refine ⟨32188870789644429130016131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 686695910179081154773677461 32188870789644429130016131)
                ·
                  refine ⟨48283306184466643695024197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32188870789644429130016131 48283306184466643695024197)
                  ·
                    refine ⟨9053119909587495692817037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48283306184466643695024197 9053119909587495692817037)
                    ·
                      refine ⟨3394919966095310884806389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9053119909587495692817037 3394919966095310884806389)
                      ·
                        rfl

theorem cell23_6611583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 6, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 6, 1, 4, 3].length) (baseStart_6611583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6611583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6611583 prefixEnd_6611583 := by exact prefixLift 6611583
  have htrace : WordTrace (prefixWord ++ tailWord_6611583) baseStart_6611583 baseEnd_6611583 := by
    simpa [prefixWord, tailWord_6611583, baseEnd_6611583] using wordTrace_append hprefix tailTrace_6611583
  have hstable : (prefixWord ++ tailWord_6611583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6611583).length < 2 ^ (prefixWord ++ tailWord_6611583).sum := by decide
  have hdescent : baseEnd_6611583 < baseStart_6611583 := by decide
  rcases family_descends (prefixWord ++ tailWord_6611583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6611607 : List Nat := [1, 1, 3, 3, 2, 1, 2, 5, 1, 4]
def baseStart_6611607 : Nat := 118140960795 + 6611607 * 2 ^ 59
def prefixEnd_6611607 : Nat := 4983230072969 + 3 ^ 40 * 6611607 * 2
def baseEnd_6611607 : Nat := 1131644096543672930302093

theorem tailTrace_6611607 : CollatzResearch.WordTrace tailWord_6611607 prefixEnd_6611607 1131644096543672930302093 := by
  unfold tailWord_6611607
  simp only [CollatzResearch.WordTrace]
  refine ⟨241145118158284486422689075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160763412105522990948459383 241145118158284486422689075)
  ·
    refine ⟨361717677237426729634033613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241145118158284486422689075 361717677237426729634033613)
    ·
      refine ⟨135644128964035023612762605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 361717677237426729634033613 135644128964035023612762605)
      ·
        refine ⟨50866548361513133854785977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135644128964035023612762605 50866548361513133854785977)
        ·
          refine ⟨38149911271134850391089483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50866548361513133854785977 38149911271134850391089483)
          ·
            refine ⟨57224866906702275586634225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38149911271134850391089483 57224866906702275586634225)
            ·
              refine ⟨42918650180026706689975669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57224866906702275586634225 42918650180026706689975669)
              ·
                refine ⟨4023623454377503752185219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42918650180026706689975669 4023623454377503752185219)
                ·
                  refine ⟨6035435181566255628277829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4023623454377503752185219 6035435181566255628277829)
                  ·
                    refine ⟨1131644096543672930302093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6035435181566255628277829 1131644096543672930302093)
                    ·
                      rfl

theorem cell23_6611607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 5, 1, 4].length) (baseStart_6611607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6611607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6611607 prefixEnd_6611607 := by exact prefixLift 6611607
  have htrace : WordTrace (prefixWord ++ tailWord_6611607) baseStart_6611607 baseEnd_6611607 := by
    simpa [prefixWord, tailWord_6611607, baseEnd_6611607] using wordTrace_append hprefix tailTrace_6611607
  have hstable : (prefixWord ++ tailWord_6611607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6611607).length < 2 ^ (prefixWord ++ tailWord_6611607).sum := by decide
  have hdescent : baseEnd_6611607 < baseStart_6611607 := by decide
  rcases family_descends (prefixWord ++ tailWord_6611607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6611620 : List Nat := [2, 3, 1, 2, 2, 1, 4, 2, 6]
def baseStart_6611620 : Nat := 118140960795 + 6611620 * 2 ^ 59
def prefixEnd_6611620 : Nat := 4983230072969 + 3 ^ 40 * 6611620 * 2
def baseEnd_6611620 : Nat := 377215440542169693338191

theorem tailTrace_6611620 : CollatzResearch.WordTrace tailWord_6611620 prefixEnd_6611620 377215440542169693338191 := by
  unfold tailWord_6611620
  simp only [CollatzResearch.WordTrace]
  refine ⟨120572796153618694821456157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160763728204824926428608209 120572796153618694821456157)
  ·
    refine ⟨45214798557607010558046059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120572796153618694821456157 45214798557607010558046059)
    ·
      refine ⟨67822197836410515837069089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45214798557607010558046059 67822197836410515837069089)
      ·
        refine ⟨50866648377307886877801817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67822197836410515837069089 50866648377307886877801817)
        ·
          refine ⟨38149986282980915158351363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50866648377307886877801817 38149986282980915158351363)
          ·
            refine ⟨57224979424471372737527045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38149986282980915158351363 57224979424471372737527045)
            ·
              refine ⟨10729683642088382388286321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57224979424471372737527045 10729683642088382388286321)
              ·
                refine ⟨8047262731566286791214741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10729683642088382388286321 8047262731566286791214741)
                ·
                  refine ⟨377215440542169693338191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8047262731566286791214741 377215440542169693338191)
                  ·
                    rfl

theorem cell23_6611620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 4, 2, 6].length) (baseStart_6611620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6611620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6611620 prefixEnd_6611620 := by exact prefixLift 6611620
  have htrace : WordTrace (prefixWord ++ tailWord_6611620) baseStart_6611620 baseEnd_6611620 := by
    simpa [prefixWord, tailWord_6611620, baseEnd_6611620] using wordTrace_append hprefix tailTrace_6611620
  have hstable : (prefixWord ++ tailWord_6611620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6611620).length < 2 ^ (prefixWord ++ tailWord_6611620).sum := by decide
  have hdescent : baseEnd_6611620 < baseStart_6611620 := by decide
  rcases family_descends (prefixWord ++ tailWord_6611620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6611647 : List Nat := [1, 1, 2, 2, 2, 5, 1, 2, 3, 1, 3]
def baseStart_6611647 : Nat := 118140960795 + 6611647 * 2 ^ 59
def prefixEnd_6611647 : Nat := 4983230072969 + 3 ^ 40 * 6611647 * 2
def baseEnd_6611647 : Nat := 3394952828857198634406095

theorem tailTrace_6611647 : CollatzResearch.WordTrace tailWord_6611647 prefixEnd_6611647 3394952828857198634406095 := by
  unfold tailWord_6611647
  simp only [CollatzResearch.WordTrace]
  refine ⟨241146577078139573254145195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160764384718759715502763463 241146577078139573254145195)
  ·
    refine ⟨361719865617209359881217793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241146577078139573254145195 361719865617209359881217793)
    ·
      refine ⟨271289899212907019910913345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 361719865617209359881217793 271289899212907019910913345)
      ·
        refine ⟨203467424409680264933185009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 271289899212907019910913345 203467424409680264933185009)
        ·
          refine ⟨152600568307260198699888757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 203467424409680264933185009 152600568307260198699888757)
          ·
            refine ⟨14306303278805643628114571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 152600568307260198699888757 14306303278805643628114571)
            ·
              refine ⟨21459454918208465442171857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14306303278805643628114571 21459454918208465442171857)
              ·
                refine ⟨16094591188656349081628893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21459454918208465442171857 16094591188656349081628893)
                ·
                  refine ⟨6035471695746130905610835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16094591188656349081628893 6035471695746130905610835)
                  ·
                    refine ⟨9053207543619196358416253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6035471695746130905610835 9053207543619196358416253)
                    ·
                      refine ⟨3394952828857198634406095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9053207543619196358416253 3394952828857198634406095)
                      ·
                        rfl

theorem cell23_6611647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 2, 3, 1, 3].length) (baseStart_6611647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6611647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6611647 prefixEnd_6611647 := by exact prefixLift 6611647
  have htrace : WordTrace (prefixWord ++ tailWord_6611647) baseStart_6611647 baseEnd_6611647 := by
    simpa [prefixWord, tailWord_6611647, baseEnd_6611647] using wordTrace_append hprefix tailTrace_6611647
  have hstable : (prefixWord ++ tailWord_6611647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6611647).length < 2 ^ (prefixWord ++ tailWord_6611647).sum := by decide
  have hdescent : baseEnd_6611647 < baseStart_6611647 := by decide
  rcases family_descends (prefixWord ++ tailWord_6611647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6611721 : List Nat := [1, 2, 1, 1, 3, 2, 5, 3, 1, 2, 2]
def baseStart_6611721 : Nat := 118140960795 + 6611721 * 2 ^ 59
def prefixEnd_6611721 : Nat := 4983230072969 + 3 ^ 40 * 6611721 * 2
def baseEnd_6611721 : Nat := 3394990826425631344880755

theorem tailTrace_6611721 : CollatzResearch.WordTrace tailWord_6611721 prefixEnd_6611721 3394990826425631344880755 := by
  unfold tailWord_6611721
  simp only [CollatzResearch.WordTrace]
  refine ⟨241149276079871483892339017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160766184053247655928226011 241149276079871483892339017)
  ·
    refine ⟨180861957059903612919254263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241149276079871483892339017 180861957059903612919254263)
    ·
      refine ⟨271292935589855419378881395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180861957059903612919254263 271292935589855419378881395)
      ·
        refine ⟨406939403384783129068322093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271292935589855419378881395 406939403384783129068322093)
        ·
          refine ⟨152602276269293673400620785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 406939403384783129068322093 152602276269293673400620785)
          ·
            refine ⟨114451707201970255050465589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152602276269293673400620785 114451707201970255050465589)
            ·
              refine ⟨10729847550184711410981149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 114451707201970255050465589 10729847550184711410981149)
              ·
                refine ⟨4023692831319266779117931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10729847550184711410981149 4023692831319266779117931)
                ·
                  refine ⟨6035539246978900168676897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4023692831319266779117931 6035539246978900168676897)
                  ·
                    refine ⟨4526654435234175126507673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6035539246978900168676897 4526654435234175126507673)
                    ·
                      refine ⟨3394990826425631344880755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4526654435234175126507673 3394990826425631344880755)
                      ·
                        rfl

theorem cell23_6611721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 5, 3, 1, 2, 2].length) (baseStart_6611721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6611721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6611721 prefixEnd_6611721 := by exact prefixLift 6611721
  have htrace : WordTrace (prefixWord ++ tailWord_6611721) baseStart_6611721 baseEnd_6611721 := by
    simpa [prefixWord, tailWord_6611721, baseEnd_6611721] using wordTrace_append hprefix tailTrace_6611721
  have hstable : (prefixWord ++ tailWord_6611721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6611721).length < 2 ^ (prefixWord ++ tailWord_6611721).sum := by decide
  have hdescent : baseEnd_6611721 < baseStart_6611721 := by decide
  rcases family_descends (prefixWord ++ tailWord_6611721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6611723 : List Nat := [1, 1, 1, 1, 5, 1, 1, 2, 1, 9]
def baseStart_6611723 : Nat := 118140960795 + 6611723 * 2 ^ 59
def prefixEnd_6611723 : Nat := 4983230072969 + 3 ^ 40 * 6611723 * 2
def baseEnd_6611723 : Nat := 1131663951128980112351915

theorem tailTrace_6611723 : CollatzResearch.WordTrace tailWord_6611723 prefixEnd_6611723 1131663951128980112351915 := by
  unfold tailWord_6611723
  simp only [CollatzResearch.WordTrace]
  refine ⟨241149349025864238233911823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160766232683909492155941215 241149349025864238233911823)
  ·
    refine ⟨361724023538796357350867735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241149349025864238233911823 361724023538796357350867735)
    ·
      refine ⟨542586035308194536026301603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 361724023538796357350867735 542586035308194536026301603)
      ·
        refine ⟨813879052962291804039452405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 542586035308194536026301603 813879052962291804039452405)
        ·
          refine ⟨76301161215214856628698663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 813879052962291804039452405 76301161215214856628698663)
          ·
            refine ⟨114451741822822284943047995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76301161215214856628698663 114451741822822284943047995)
            ·
              refine ⟨171677612734233427414571993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114451741822822284943047995 171677612734233427414571993)
              ·
                refine ⟨128758209550675070560928995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 171677612734233427414571993 128758209550675070560928995)
                ·
                  refine ⟨193137314326012605841393493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 128758209550675070560928995 193137314326012605841393493)
                  ·
                    refine ⟨1131663951128980112351915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 193137314326012605841393493 1131663951128980112351915)
                    ·
                      rfl

theorem cell23_6611723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 2, 1, 9].length) (baseStart_6611723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6611723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6611723 prefixEnd_6611723 := by exact prefixLift 6611723
  have htrace : WordTrace (prefixWord ++ tailWord_6611723) baseStart_6611723 baseEnd_6611723 := by
    simpa [prefixWord, tailWord_6611723, baseEnd_6611723] using wordTrace_append hprefix tailTrace_6611723
  have hstable : (prefixWord ++ tailWord_6611723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6611723).length < 2 ^ (prefixWord ++ tailWord_6611723).sum := by decide
  have hdescent : baseEnd_6611723 < baseStart_6611723 := by decide
  rcases family_descends (prefixWord ++ tailWord_6611723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6611738 : List Nat := [3, 1, 1, 3, 2, 1, 5, 2, 1, 2, 2]
def baseStart_6611738 : Nat := 118140960795 + 6611738 * 2 ^ 59
def prefixEnd_6611738 : Nat := 4983230072969 + 3 ^ 40 * 6611738 * 2
def baseEnd_6611738 : Nat := 3394999555596757778368177

theorem tailTrace_6611738 : CollatzResearch.WordTrace tailWord_6611738 prefixEnd_6611738 3394999555596757778368177 := by
  unfold tailWord_6611738
  simp only [CollatzResearch.WordTrace]
  refine ⟨60287474030202473948926967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160766597413873263863805245 60287474030202473948926967)
  ·
    refine ⟨90431211045303710923390451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60287474030202473948926967 90431211045303710923390451)
    ·
      refine ⟨135646816567955566385085677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90431211045303710923390451 135646816567955566385085677)
      ·
        refine ⟨50867556212983337394407129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135646816567955566385085677 50867556212983337394407129)
        ·
          refine ⟨38150667159737503045805347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50867556212983337394407129 38150667159737503045805347)
          ·
            refine ⟨57226000739606254568708021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38150667159737503045805347 57226000739606254568708021)
            ·
              refine ⟨5364937569338086365816377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57226000739606254568708021 5364937569338086365816377)
              ·
                refine ⟨4023703177003564774362283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5364937569338086365816377 4023703177003564774362283)
                ·
                  refine ⟨6035554765505347161543425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4023703177003564774362283 6035554765505347161543425)
                  ·
                    refine ⟨4526666074129010371157569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6035554765505347161543425 4526666074129010371157569)
                    ·
                      refine ⟨3394999555596757778368177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4526666074129010371157569 3394999555596757778368177)
                      ·
                        rfl

theorem cell23_6611738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 5, 2, 1, 2, 2].length) (baseStart_6611738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6611738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6611738 prefixEnd_6611738 := by exact prefixLift 6611738
  have htrace : WordTrace (prefixWord ++ tailWord_6611738) baseStart_6611738 baseEnd_6611738 := by
    simpa [prefixWord, tailWord_6611738, baseEnd_6611738] using wordTrace_append hprefix tailTrace_6611738
  have hstable : (prefixWord ++ tailWord_6611738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6611738).length < 2 ^ (prefixWord ++ tailWord_6611738).sum := by decide
  have hdescent : baseEnd_6611738 < baseStart_6611738 := by decide
  rcases family_descends (prefixWord ++ tailWord_6611738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6611747 : List Nat := [1, 1, 1, 4, 2, 1, 1, 4, 3, 3, 2]
def baseStart_6611747 : Nat := 118140960795 + 6611747 * 2 ^ 59
def prefixEnd_6611747 : Nat := 4983230072969 + 3 ^ 40 * 6611747 * 2
def baseEnd_6611747 : Nat := 3395004176922648243155635

theorem tailTrace_6611747 : CollatzResearch.WordTrace tailWord_6611747 prefixEnd_6611747 3395004176922648243155635 := by
  unfold tailWord_6611747
  simp only [CollatzResearch.WordTrace]
  refine ⟨241150224377777290332785495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160766816251851526888523663 241150224377777290332785495)
  ·
    refine ⟨361725336566665935499178243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241150224377777290332785495 361725336566665935499178243)
    ·
      refine ⟨542588004849998903248767365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 361725336566665935499178243 542588004849998903248767365)
      ·
        refine ⟨101735250909374794359143881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 542588004849998903248767365 101735250909374794359143881)
        ·
          refine ⟨76301438182031095769357911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101735250909374794359143881 76301438182031095769357911)
          ·
            refine ⟨114452157273046643654036867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76301438182031095769357911 114452157273046643654036867)
            ·
              refine ⟨171678235909569965481055301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114452157273046643654036867 171678235909569965481055301)
              ·
                refine ⟨32189669233044368527697869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 171678235909569965481055301 32189669233044368527697869)
                ·
                  refine ⟨12071125962391638197886701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32189669233044368527697869 12071125962391638197886701)
                  ·
                    refine ⟨4526672235896864324207513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12071125962391638197886701 4526672235896864324207513)
                    ·
                      refine ⟨3395004176922648243155635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4526672235896864324207513 3395004176922648243155635)
                      ·
                        rfl

theorem cell23_6611747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 4, 3, 3, 2].length) (baseStart_6611747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6611747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6611747 prefixEnd_6611747 := by exact prefixLift 6611747
  have htrace : WordTrace (prefixWord ++ tailWord_6611747) baseStart_6611747 baseEnd_6611747 := by
    simpa [prefixWord, tailWord_6611747, baseEnd_6611747] using wordTrace_append hprefix tailTrace_6611747
  have hstable : (prefixWord ++ tailWord_6611747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6611747).length < 2 ^ (prefixWord ++ tailWord_6611747).sum := by decide
  have hdescent : baseEnd_6611747 < baseStart_6611747 := by decide
  rcases family_descends (prefixWord ++ tailWord_6611747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6611748 : List Nat := [2, 3, 1, 3, 4, 1, 2, 1, 2, 4]
def baseStart_6611748 : Nat := 118140960795 + 6611748 * 2 ^ 59
def prefixEnd_6611748 : Nat := 4983230072969 + 3 ^ 40 * 6611748 * 2
def baseEnd_6611748 : Nat := 1131668230134434246414377

theorem tailTrace_6611748 : CollatzResearch.WordTrace tailWord_6611748 prefixEnd_6611748 1131668230134434246414377 := by
  unfold tailWord_6611748
  simp only [CollatzResearch.WordTrace]
  refine ⟨120575130425386833751785949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160766840567182445002381265 120575130425386833751785949)
  ·
    refine ⟨45215673909520062656919731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120575130425386833751785949 45215673909520062656919731)
    ·
      refine ⟨67823510864280093985379597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45215673909520062656919731 67823510864280093985379597)
      ·
        refine ⟨25433816574105035244517349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67823510864280093985379597 25433816574105035244517349)
        ·
          refine ⟨4768840607644694108347003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25433816574105035244517349 4768840607644694108347003)
          ·
            refine ⟨7153260911467041162520505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4768840607644694108347003 7153260911467041162520505)
            ·
              refine ⟨5364945683600280871890379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7153260911467041162520505 5364945683600280871890379)
              ·
                refine ⟨8047418525400421307835569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5364945683600280871890379 8047418525400421307835569)
                ·
                  refine ⟨6035563894050315980876677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8047418525400421307835569 6035563894050315980876677)
                  ·
                    refine ⟨1131668230134434246414377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6035563894050315980876677 1131668230134434246414377)
                    ·
                      rfl

theorem cell23_6611748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 2, 1, 2, 4].length) (baseStart_6611748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6611748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6611748 prefixEnd_6611748 := by exact prefixLift 6611748
  have htrace : WordTrace (prefixWord ++ tailWord_6611748) baseStart_6611748 baseEnd_6611748 := by
    simpa [prefixWord, tailWord_6611748, baseEnd_6611748] using wordTrace_append hprefix tailTrace_6611748
  have hstable : (prefixWord ++ tailWord_6611748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6611748).length < 2 ^ (prefixWord ++ tailWord_6611748).sum := by decide
  have hdescent : baseEnd_6611748 < baseStart_6611748 := by decide
  rcases family_descends (prefixWord ++ tailWord_6611748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6611789 : List Nat := [1, 6, 1, 2, 3, 1, 2, 2, 1, 2, 2]
def baseStart_6611789 : Nat := 118140960795 + 6611789 * 2 ^ 59
def prefixEnd_6611789 : Nat := 4983230072969 + 3 ^ 40 * 6611789 * 2
def baseEnd_6611789 : Nat := 3395025743110137078830443

theorem tailTrace_6611789 : CollatzResearch.WordTrace tailWord_6611789 prefixEnd_6611789 3395025743110137078830443 := by
  unfold tailWord_6611789
  simp only [CollatzResearch.WordTrace]
  refine ⟨241151756243625131505814421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160767837495750087670542947 241151756243625131505814421)
  ·
    refine ⟨11303988573919928039335051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 241151756243625131505814421 11303988573919928039335051)
    ·
      refine ⟨16955982860879892059002577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11303988573919928039335051 16955982860879892059002577)
      ·
        refine ⟨12716987145659919044251933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16955982860879892059002577 12716987145659919044251933)
        ·
          refine ⟨4768870179622469641594475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12716987145659919044251933 4768870179622469641594475)
          ·
            refine ⟨7153305269433704462391713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4768870179622469641594475 7153305269433704462391713)
            ·
              refine ⟨5364978952075278346793785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7153305269433704462391713 5364978952075278346793785)
              ·
                refine ⟨4023734214056458760095339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5364978952075278346793785 4023734214056458760095339)
                ·
                  refine ⟨6035601321084688140143009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4023734214056458760095339 6035601321084688140143009)
                  ·
                    refine ⟨4526700990813516105107257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6035601321084688140143009 4526700990813516105107257)
                    ·
                      refine ⟨3395025743110137078830443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4526700990813516105107257 3395025743110137078830443)
                      ·
                        rfl

theorem cell23_6611789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 2, 2, 1, 2, 2].length) (baseStart_6611789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6611789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6611789 prefixEnd_6611789 := by exact prefixLift 6611789
  have htrace : WordTrace (prefixWord ++ tailWord_6611789) baseStart_6611789 baseEnd_6611789 := by
    simpa [prefixWord, tailWord_6611789, baseEnd_6611789] using wordTrace_append hprefix tailTrace_6611789
  have hstable : (prefixWord ++ tailWord_6611789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6611789).length < 2 ^ (prefixWord ++ tailWord_6611789).sum := by decide
  have hdescent : baseEnd_6611789 < baseStart_6611789 := by decide
  rcases family_descends (prefixWord ++ tailWord_6611789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6611790 : List Nat := [4, 1, 1, 1, 1, 1, 1, 2, 3, 4, 4]
def baseStart_6611790 : Nat := 118140960795 + 6611790 * 2 ^ 59
def prefixEnd_6611790 : Nat := 4983230072969 + 3 ^ 40 * 6611790 * 2
def baseEnd_6611790 : Nat := 3395026256590791574917937

theorem tailTrace_6611790 : CollatzResearch.WordTrace tailWord_6611790 prefixEnd_6611790 3395026256590791574917937 := by
  unfold tailWord_6611790
  simp only [CollatzResearch.WordTrace]
  refine ⟨30143974089577688584575103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 160767861811081005784400549 30143974089577688584575103)
  ·
    refine ⟨45215961134366532876862655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30143974089577688584575103 45215961134366532876862655)
    ·
      refine ⟨67823941701549799315293983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45215961134366532876862655 67823941701549799315293983)
      ·
        refine ⟨101735912552324698972940975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67823941701549799315293983 101735912552324698972940975)
        ·
          refine ⟨152603868828487048459411463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101735912552324698972940975 152603868828487048459411463)
          ·
            refine ⟨228905803242730572689117195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152603868828487048459411463 228905803242730572689117195)
            ·
              refine ⟨343358704864095859033675793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 228905803242730572689117195 343358704864095859033675793)
              ·
                refine ⟨257519028648071894275256845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 343358704864095859033675793 257519028648071894275256845)
                ·
                  refine ⟨96569635743026960353221317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 257519028648071894275256845 96569635743026960353221317)
                  ·
                    refine ⟨18106806701817555066228997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 96569635743026960353221317 18106806701817555066228997)
                    ·
                      refine ⟨3395026256590791574917937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18106806701817555066228997 3395026256590791574917937)
                      ·
                        rfl

theorem cell23_6611790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 3, 4, 4].length) (baseStart_6611790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6611790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6611790 prefixEnd_6611790 := by exact prefixLift 6611790
  have htrace : WordTrace (prefixWord ++ tailWord_6611790) baseStart_6611790 baseEnd_6611790 := by
    simpa [prefixWord, tailWord_6611790, baseEnd_6611790] using wordTrace_append hprefix tailTrace_6611790
  have hstable : (prefixWord ++ tailWord_6611790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6611790).length < 2 ^ (prefixWord ++ tailWord_6611790).sum := by decide
  have hdescent : baseEnd_6611790 < baseStart_6611790 := by decide
  rcases family_descends (prefixWord ++ tailWord_6611790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6611811 : List Nat := [1, 1, 1, 5, 3, 1, 2, 3, 2, 2, 2]
def baseStart_6611811 : Nat := 118140960795 + 6611811 * 2 ^ 59
def prefixEnd_6611811 : Nat := 4983230072969 + 3 ^ 40 * 6611811 * 2
def baseEnd_6611811 : Nat := 3395037039684535992755341

theorem tailTrace_6611811 : CollatzResearch.WordTrace tailWord_6611811 prefixEnd_6611811 3395037039684535992755341 := by
  unfold tailWord_6611811
  simp only [CollatzResearch.WordTrace]
  refine ⟨241152558649545429263115287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160768372433030286175410191 241152558649545429263115287)
  ·
    refine ⟨361728837974318143894672931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241152558649545429263115287 361728837974318143894672931)
    ·
      refine ⟨542593256961477215842009397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 361728837974318143894672931 542593256961477215842009397)
      ·
        refine ⟨50868117840138488985188381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 542593256961477215842009397 50868117840138488985188381)
        ·
          refine ⟨19075544190051933369445643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50868117840138488985188381 19075544190051933369445643)
          ·
            refine ⟨28613316285077900054168465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19075544190051933369445643 28613316285077900054168465)
            ·
              refine ⟨21459987213808425040626349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28613316285077900054168465 21459987213808425040626349)
              ·
                refine ⟨8047495205178159390234881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21459987213808425040626349 8047495205178159390234881)
                ·
                  refine ⟨6035621403883619542676161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8047495205178159390234881 6035621403883619542676161)
                  ·
                    refine ⟨4526716052912714657007121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6035621403883619542676161 4526716052912714657007121)
                    ·
                      refine ⟨3395037039684535992755341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4526716052912714657007121 3395037039684535992755341)
                      ·
                        rfl

theorem cell23_6611811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 3, 2, 2, 2].length) (baseStart_6611811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6611811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6611811 prefixEnd_6611811 := by exact prefixLift 6611811
  have htrace : WordTrace (prefixWord ++ tailWord_6611811) baseStart_6611811 baseEnd_6611811 := by
    simpa [prefixWord, tailWord_6611811, baseEnd_6611811] using wordTrace_append hprefix tailTrace_6611811
  have hstable : (prefixWord ++ tailWord_6611811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6611811).length < 2 ^ (prefixWord ++ tailWord_6611811).sum := by decide
  have hdescent : baseEnd_6611811 < baseStart_6611811 := by decide
  rcases family_descends (prefixWord ++ tailWord_6611811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6611840 : List Nat := [2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 5]
def baseStart_6611840 : Nat := 118140960795 + 6611840 * 2 ^ 59
def prefixEnd_6611840 : Nat := 4983230072969 + 3 ^ 40 * 6611840 * 2
def baseEnd_6611840 : Nat := 3395051930623516379292707

theorem tailTrace_6611840 : CollatzResearch.WordTrace tailWord_6611840 prefixEnd_6611840 3395051930623516379292707 := by
  unfold tailWord_6611840
  simp only [CollatzResearch.WordTrace]
  refine ⟨120576808183220183607960487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160769077577626911477280649 120576808183220183607960487)
  ·
    refine ⟨180865212274830275411940731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120576808183220183607960487 180865212274830275411940731)
    ·
      refine ⟨271297818412245413117911097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180865212274830275411940731 271297818412245413117911097)
      ·
        refine ⟨203473363809184059838433323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 271297818412245413117911097 203473363809184059838433323)
        ·
          refine ⟨305210045713776089757649985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203473363809184059838433323 305210045713776089757649985)
          ·
            refine ⟨228907534285332067318237489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 305210045713776089757649985 228907534285332067318237489)
            ·
              refine ⟨171680650713999050488678117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 228907534285332067318237489 171680650713999050488678117)
              ·
                refine ⟨32190122008874821966627147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 171680650713999050488678117 32190122008874821966627147)
                ·
                  refine ⟨48285183013312232949940721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32190122008874821966627147 48285183013312232949940721)
                  ·
                    refine ⟨36213887259984174712455541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48285183013312232949940721 36213887259984174712455541)
                    ·
                      refine ⟨3395051930623516379292707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36213887259984174712455541 3395051930623516379292707)
                      ·
                        rfl

theorem cell23_6611840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 5].length) (baseStart_6611840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6611840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6611840 prefixEnd_6611840 := by exact prefixLift 6611840
  have htrace : WordTrace (prefixWord ++ tailWord_6611840) baseStart_6611840 baseEnd_6611840 := by
    simpa [prefixWord, tailWord_6611840, baseEnd_6611840] using wordTrace_append hprefix tailTrace_6611840
  have hstable : (prefixWord ++ tailWord_6611840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6611840).length < 2 ^ (prefixWord ++ tailWord_6611840).sum := by decide
  have hdescent : baseEnd_6611840 < baseStart_6611840 := by decide
  rcases family_descends (prefixWord ++ tailWord_6611840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6611885 : List Nat := [1, 5, 2, 3, 2, 1, 1, 3, 5]
def baseStart_6611885 : Nat := 118140960795 + 6611885 * 2 ^ 59
def prefixEnd_6611885 : Nat := 4983230072969 + 3 ^ 40 * 6611885 * 2
def baseEnd_6611885 : Nat := 377230559694774300358889

theorem tailTrace_6611885 : CollatzResearch.WordTrace tailWord_6611885 prefixEnd_6611885 377230559694774300358889 := by
  unfold tailWord_6611885
  simp only [CollatzResearch.WordTrace]
  refine ⟨241155257651277339901309109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160770171767518226600872739 241155257651277339901309109)
  ·
    refine ⟨22608305404807250615747729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 241155257651277339901309109 22608305404807250615747729)
    ·
      refine ⟨16956229053605437961810797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22608305404807250615747729 16956229053605437961810797)
      ·
        refine ⟨6358585895102039235679049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16956229053605437961810797 6358585895102039235679049)
        ·
          refine ⟨4768939421326529426759287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6358585895102039235679049 4768939421326529426759287)
          ·
            refine ⟨7153409131989794140138931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4768939421326529426759287 7153409131989794140138931)
            ·
              refine ⟨10730113697984691210208397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7153409131989794140138931 10730113697984691210208397)
              ·
                refine ⟨4023792636744259203828149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10730113697984691210208397 4023792636744259203828149)
                ·
                  refine ⟨377230559694774300358889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4023792636744259203828149 377230559694774300358889)
                  ·
                    rfl

theorem cell23_6611885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 2, 1, 1, 3, 5].length) (baseStart_6611885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6611885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6611885 prefixEnd_6611885 := by exact prefixLift 6611885
  have htrace : WordTrace (prefixWord ++ tailWord_6611885) baseStart_6611885 baseEnd_6611885 := by
    simpa [prefixWord, tailWord_6611885, baseEnd_6611885] using wordTrace_append hprefix tailTrace_6611885
  have hstable : (prefixWord ++ tailWord_6611885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6611885).length < 2 ^ (prefixWord ++ tailWord_6611885).sum := by decide
  have hdescent : baseEnd_6611885 < baseStart_6611885 := by decide
  rcases family_descends (prefixWord ++ tailWord_6611885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6611904 : List Nat := [2, 1, 1, 2, 3, 4, 1, 2, 2, 2, 3]
def baseStart_6611904 : Nat := 118140960795 + 6611904 * 2 ^ 59
def prefixEnd_6611904 : Nat := 4983230072969 + 3 ^ 40 * 6611904 * 2
def baseEnd_6611904 : Nat := 3395084793385404128892413

theorem tailTrace_6611904 : CollatzResearch.WordTrace tailWord_6611904 prefixEnd_6611904 3395084793385404128892413 := by
  unfold tailWord_6611904
  simp only [CollatzResearch.WordTrace]
  refine ⟨120577975319104253073125383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160770633758805670764167177 120577975319104253073125383)
  ·
    refine ⟨180866962978656379609688075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120577975319104253073125383 180866962978656379609688075)
    ·
      refine ⟨271300444467984569414532113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180866962978656379609688075 271300444467984569414532113)
      ·
        refine ⟨203475333350988427060899085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 271300444467984569414532113 203475333350988427060899085)
        ·
          refine ⟨76303250006620660147837157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 203475333350988427060899085 76303250006620660147837157)
          ·
            refine ⟨14306859376241373777719467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76303250006620660147837157 14306859376241373777719467)
            ·
              refine ⟨21460289064362060666579201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14306859376241373777719467 21460289064362060666579201)
              ·
                refine ⟨16095216798271545499934401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21460289064362060666579201 16095216798271545499934401)
                ·
                  refine ⟨12071412598703659124950801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16095216798271545499934401 12071412598703659124950801)
                  ·
                    refine ⟨9053559449027744343713101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12071412598703659124950801 9053559449027744343713101)
                    ·
                      refine ⟨3395084793385404128892413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9053559449027744343713101 3395084793385404128892413)
                      ·
                        rfl

theorem cell23_6611904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 2, 2, 2, 3].length) (baseStart_6611904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6611904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6611904 prefixEnd_6611904 := by exact prefixLift 6611904
  have htrace : WordTrace (prefixWord ++ tailWord_6611904) baseStart_6611904 baseEnd_6611904 := by
    simpa [prefixWord, tailWord_6611904, baseEnd_6611904] using wordTrace_append hprefix tailTrace_6611904
  have hstable : (prefixWord ++ tailWord_6611904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6611904).length < 2 ^ (prefixWord ++ tailWord_6611904).sum := by decide
  have hdescent : baseEnd_6611904 < baseStart_6611904 := by decide
  rcases family_descends (prefixWord ++ tailWord_6611904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6611920 : List Nat := [2, 1, 1, 1, 1, 2, 3, 1, 2, 9]
def baseStart_6611920 : Nat := 118140960795 + 6611920 * 2 ^ 59
def prefixEnd_6611920 : Nat := 4983230072969 + 3 ^ 40 * 6611920 * 2
def baseEnd_6611920 : Nat := 1131697669691958688764113

theorem tailTrace_6611920 : CollatzResearch.WordTrace tailWord_6611920 prefixEnd_6611920 1131697669691958688764113 := by
  unfold tailWord_6611920
  simp only [CollatzResearch.WordTrace]
  refine ⟨120578267103075270439416607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160771022804100360585888809 120578267103075270439416607)
  ·
    refine ⟨180867400654612905659124911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120578267103075270439416607 180867400654612905659124911)
    ·
      refine ⟨271301100981919358488687367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180867400654612905659124911 271301100981919358488687367)
      ·
        refine ⟨406951651472879037733031051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271301100981919358488687367 406951651472879037733031051)
        ·
          refine ⟨610427477209318556599546577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 406951651472879037733031051 610427477209318556599546577)
          ·
            refine ⟨457820607906988917449659933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 610427477209318556599546577 457820607906988917449659933)
            ·
              refine ⟨171682727965120844043622475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 457820607906988917449659933 171682727965120844043622475)
              ·
                refine ⟨257524091947681266065433713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 171682727965120844043622475 257524091947681266065433713)
                ·
                  refine ⟨193143068960760949549075285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 257524091947681266065433713 193143068960760949549075285)
                  ·
                    refine ⟨1131697669691958688764113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 193143068960760949549075285 1131697669691958688764113)
                    ·
                      rfl

theorem cell23_6611920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 2, 9].length) (baseStart_6611920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6611920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6611920 prefixEnd_6611920 := by exact prefixLift 6611920
  have htrace : WordTrace (prefixWord ++ tailWord_6611920) baseStart_6611920 baseEnd_6611920 := by
    simpa [prefixWord, tailWord_6611920, baseEnd_6611920] using wordTrace_append hprefix tailTrace_6611920
  have hstable : (prefixWord ++ tailWord_6611920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6611920).length < 2 ^ (prefixWord ++ tailWord_6611920).sum := by decide
  have hdescent : baseEnd_6611920 < baseStart_6611920 := by decide
  rcases family_descends (prefixWord ++ tailWord_6611920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6611924 : List Nat := [2, 4, 1, 2, 1, 3, 1, 3, 6]
def baseStart_6611924 : Nat := 118140960795 + 6611924 * 2 ^ 59
def prefixEnd_6611924 : Nat := 4983230072969 + 3 ^ 40 * 6611924 * 2
def baseEnd_6611924 : Nat := 377232784777610450071369

theorem tailTrace_6611924 : CollatzResearch.WordTrace tailWord_6611924 prefixEnd_6611924 377232784777610450071369 := by
  unfold tailWord_6611924
  simp only [CollatzResearch.WordTrace]
  refine ⟨120578340049068024780989413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160771120065424033041319217 120578340049068024780989413)
  ·
    refine ⟨22608438759200254646435515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 120578340049068024780989413 22608438759200254646435515)
    ·
      refine ⟨33912658138800381969653273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22608438759200254646435515 33912658138800381969653273)
      ·
        refine ⟨25434493604100286477239955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33912658138800381969653273 25434493604100286477239955)
        ·
          refine ⟨38151740406150429715859933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25434493604100286477239955 38151740406150429715859933)
          ·
            refine ⟨14306902652306411143447475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38151740406150429715859933 14306902652306411143447475)
            ·
              refine ⟨21460353978459616715171213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14306902652306411143447475 21460353978459616715171213)
              ·
                refine ⟨8047632741922356268189205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21460353978459616715171213 8047632741922356268189205)
                ·
                  refine ⟨377232784777610450071369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8047632741922356268189205 377232784777610450071369)
                  ·
                    rfl

theorem cell23_6611924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 3, 6].length) (baseStart_6611924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6611924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6611924 prefixEnd_6611924 := by exact prefixLift 6611924
  have htrace : WordTrace (prefixWord ++ tailWord_6611924) baseStart_6611924 baseEnd_6611924 := by
    simpa [prefixWord, tailWord_6611924, baseEnd_6611924] using wordTrace_append hprefix tailTrace_6611924
  have hstable : (prefixWord ++ tailWord_6611924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6611924).length < 2 ^ (prefixWord ++ tailWord_6611924).sum := by decide
  have hdescent : baseEnd_6611924 < baseStart_6611924 := by decide
  rcases family_descends (prefixWord ++ tailWord_6611924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6611938 : List Nat := [3, 3, 3, 1, 1, 2, 2, 1, 2, 2, 3]
def baseStart_6611938 : Nat := 118140960795 + 6611938 * 2 ^ 59
def prefixEnd_6611938 : Nat := 4983230072969 + 3 ^ 40 * 6611938 * 2
def baseEnd_6611938 : Nat := 3395102251727656995867257

theorem tailTrace_6611938 : CollatzResearch.WordTrace tailWord_6611938 prefixEnd_6611938 3395102251727656995867257 := by
  unfold tailWord_6611938
  simp only [CollatzResearch.WordTrace]
  refine ⟨60289297680021332488247117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160771460480056886635325645 60289297680021332488247117)
  ·
    refine ⟨22608486630007999683092669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60289297680021332488247117 22608486630007999683092669)
    ·
      refine ⟨8478182486252999881159751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22608486630007999683092669 8478182486252999881159751)
      ·
        refine ⟨12717273729379499821739627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8478182486252999881159751 12717273729379499821739627)
        ·
          refine ⟨19075910594069249732609441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12717273729379499821739627 19075910594069249732609441)
          ·
            refine ⟨14306932945551937299457081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19075910594069249732609441 14306932945551937299457081)
            ·
              refine ⟨10730199709163952974592811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14306932945551937299457081 10730199709163952974592811)
              ·
                refine ⟨16095299563745929461889217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10730199709163952974592811 16095299563745929461889217)
                ·
                  refine ⟨12071474672809447096416913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16095299563745929461889217 12071474672809447096416913)
                  ·
                    refine ⟨9053606004607085322312685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12071474672809447096416913 9053606004607085322312685)
                    ·
                      refine ⟨3395102251727656995867257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9053606004607085322312685 3395102251727656995867257)
                      ·
                        rfl

theorem cell23_6611938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_6611938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6611938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6611938 prefixEnd_6611938 := by exact prefixLift 6611938
  have htrace : WordTrace (prefixWord ++ tailWord_6611938) baseStart_6611938 baseEnd_6611938 := by
    simpa [prefixWord, tailWord_6611938, baseEnd_6611938] using wordTrace_append hprefix tailTrace_6611938
  have hstable : (prefixWord ++ tailWord_6611938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6611938).length < 2 ^ (prefixWord ++ tailWord_6611938).sum := by decide
  have hdescent : baseEnd_6611938 < baseStart_6611938 := by decide
  rcases family_descends (prefixWord ++ tailWord_6611938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6611944 : List Nat := [2, 1, 4, 1, 1, 1, 2, 3, 1, 5, 2]
def baseStart_6611944 : Nat := 118140960795 + 6611944 * 2 ^ 59
def prefixEnd_6611944 : Nat := 4983230072969 + 3 ^ 40 * 6611944 * 2
def baseEnd_6611944 : Nat := 3395105332611583972392229

theorem tailTrace_6611944 : CollatzResearch.WordTrace tailWord_6611944 prefixEnd_6611944 3395105332611583972392229 := by
  unfold tailWord_6611944
  simp only [CollatzResearch.WordTrace]
  refine ⟨120578704779031796488853443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160771606372042395318471257 120578704779031796488853443)
  ·
    refine ⟨180868057168547694733280165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120578704779031796488853443 180868057168547694733280165)
    ·
      refine ⟨33912760719102692762490031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 180868057168547694733280165 33912760719102692762490031)
      ·
        refine ⟨50869141078654039143735047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33912760719102692762490031 50869141078654039143735047)
        ·
          refine ⟨76303711617981058715602571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50869141078654039143735047 76303711617981058715602571)
          ·
            refine ⟨114455567426971588073403857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76303711617981058715602571 114455567426971588073403857)
            ·
              refine ⟨85841675570228691055052893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114455567426971588073403857 85841675570228691055052893)
              ·
                refine ⟨32190628338835759145644835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85841675570228691055052893 32190628338835759145644835)
                ·
                  refine ⟨48285942508253638718467253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32190628338835759145644835 48285942508253638718467253)
                  ·
                    refine ⟨4526807110148778629856305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48285942508253638718467253 4526807110148778629856305)
                    ·
                      refine ⟨3395105332611583972392229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4526807110148778629856305 3395105332611583972392229)
                      ·
                        rfl

theorem cell23_6611944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 3, 1, 5, 2].length) (baseStart_6611944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6611944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6611944 prefixEnd_6611944 := by exact prefixLift 6611944
  have htrace : WordTrace (prefixWord ++ tailWord_6611944) baseStart_6611944 baseEnd_6611944 := by
    simpa [prefixWord, tailWord_6611944, baseEnd_6611944] using wordTrace_append hprefix tailTrace_6611944
  have hstable : (prefixWord ++ tailWord_6611944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6611944).length < 2 ^ (prefixWord ++ tailWord_6611944).sum := by decide
  have hdescent : baseEnd_6611944 < baseStart_6611944 := by decide
  rcases family_descends (prefixWord ++ tailWord_6611944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6611977 : List Nat := [1, 2, 1, 1, 3, 1, 1, 6, 1, 1, 5]
def baseStart_6611977 : Nat := 118140960795 + 6611977 * 2 ^ 59
def prefixEnd_6611977 : Nat := 4983230072969 + 3 ^ 40 * 6611977 * 2
def baseEnd_6611977 : Nat := 3395122277473182343279577

theorem tailTrace_6611977 : CollatzResearch.WordTrace tailWord_6611977 prefixEnd_6611977 3395122277473182343279577 := by
  unfold tailWord_6611977
  simp only [CollatzResearch.WordTrace]
  refine ⟨241158613166944039613658185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160772408777962693075772123 241158613166944039613658185)
  ·
    refine ⟨180868959875208029710243639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241158613166944039613658185 180868959875208029710243639)
    ·
      refine ⟨271303439812812044565365459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180868959875208029710243639 271303439812812044565365459)
      ·
        refine ⟨406955159719218066848048189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271303439812812044565365459 406955159719218066848048189)
        ·
          refine ⟨152608184894706775068018071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 406955159719218066848048189 152608184894706775068018071)
          ·
            refine ⟨228912277342060162602027107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152608184894706775068018071 228912277342060162602027107)
            ·
              refine ⟨343368416013090243903040661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 228912277342060162602027107 343368416013090243903040661)
              ·
                refine ⟨16095394500613605182955031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 343368416013090243903040661 16095394500613605182955031)
                ·
                  refine ⟨24143091750920407774432547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16095394500613605182955031 24143091750920407774432547)
                  ·
                    refine ⟨36214637626380611661648821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24143091750920407774432547 36214637626380611661648821)
                    ·
                      refine ⟨3395122277473182343279577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36214637626380611661648821 3395122277473182343279577)
                      ·
                        rfl

theorem cell23_6611977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 6, 1, 1, 5].length) (baseStart_6611977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6611977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6611977 prefixEnd_6611977 := by exact prefixLift 6611977
  have htrace : WordTrace (prefixWord ++ tailWord_6611977) baseStart_6611977 baseEnd_6611977 := by
    simpa [prefixWord, tailWord_6611977, baseEnd_6611977] using wordTrace_append hprefix tailTrace_6611977
  have hstable : (prefixWord ++ tailWord_6611977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6611977).length < 2 ^ (prefixWord ++ tailWord_6611977).sum := by decide
  have hdescent : baseEnd_6611977 < baseStart_6611977 := by decide
  rcases family_descends (prefixWord ++ tailWord_6611977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6611994 : List Nat := [3, 1, 1, 3, 1, 2, 1, 3, 3, 2, 3]
def baseStart_6611994 : Nat := 118140960795 + 6611994 * 2 ^ 59
def prefixEnd_6611994 : Nat := 4983230072969 + 3 ^ 40 * 6611994 * 2
def baseEnd_6611994 : Nat := 3395131006644308776766999

theorem tailTrace_6611994 : CollatzResearch.WordTrace tailWord_6611994 prefixEnd_6611994 3395131006644308776766999 := by
  unfold tailWord_6611994
  simp only [CollatzResearch.WordTrace]
  refine ⟨60289808301970612879256759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160772822138588301011351357 60289808301970612879256759)
  ·
    refine ⟨90434712452955919318885139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60289808301970612879256759 90434712452955919318885139)
    ·
      refine ⟨135652068679433878978327709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90434712452955919318885139 135652068679433878978327709)
      ·
        refine ⟨50869525754787704616872891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135652068679433878978327709 50869525754787704616872891)
        ·
          refine ⟨76304288632181556925309337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50869525754787704616872891 76304288632181556925309337)
          ·
            refine ⟨57228216474136167693982003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76304288632181556925309337 57228216474136167693982003)
            ·
              refine ⟨85842324711204251540973005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57228216474136167693982003 85842324711204251540973005)
              ·
                refine ⟨32190871766701594327864877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85842324711204251540973005 32190871766701594327864877)
                ·
                  refine ⟨12071576912513097872949329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32190871766701594327864877 12071576912513097872949329)
                  ·
                    refine ⟨9053682684384823404711997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12071576912513097872949329 9053682684384823404711997)
                    ·
                      refine ⟨3395131006644308776766999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9053682684384823404711997 3395131006644308776766999)
                      ·
                        rfl

theorem cell23_6611994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 3, 3, 2, 3].length) (baseStart_6611994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6611994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6611994 prefixEnd_6611994 := by exact prefixLift 6611994
  have htrace : WordTrace (prefixWord ++ tailWord_6611994) baseStart_6611994 baseEnd_6611994 := by
    simpa [prefixWord, tailWord_6611994, baseEnd_6611994] using wordTrace_append hprefix tailTrace_6611994
  have hstable : (prefixWord ++ tailWord_6611994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6611994).length < 2 ^ (prefixWord ++ tailWord_6611994).sum := by decide
  have hdescent : baseEnd_6611994 < baseStart_6611994 := by decide
  rcases family_descends (prefixWord ++ tailWord_6611994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6612025 : List Nat := [1, 2, 1, 5, 2, 1, 2, 4, 1, 2, 2]
def baseStart_6612025 : Nat := 118140960795 + 6612025 * 2 ^ 59
def prefixEnd_6612025 : Nat := 4983230072969 + 3 ^ 40 * 6612025 * 2
def baseEnd_6612025 : Nat := 3395146924544598155479357

theorem tailTrace_6612025 : CollatzResearch.WordTrace tailWord_6612025 prefixEnd_6612025 3395146924544598155479357 := by
  unfold tailWord_6612025
  simp only [CollatzResearch.WordTrace]
  refine ⟨241160363870770143811405529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160773575913846762540937019 241160363870770143811405529)
  ·
    refine ⟨180870272903077607858554147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241160363870770143811405529 180870272903077607858554147)
    ·
      refine ⟨271305409354616411787831221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180870272903077607858554147 271305409354616411787831221)
      ·
        refine ⟨25434882126995288605109177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 271305409354616411787831221 25434882126995288605109177)
        ·
          refine ⟨19076161595246466453831883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25434882126995288605109177 19076161595246466453831883)
          ·
            refine ⟨28614242392869699680747825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19076161595246466453831883 28614242392869699680747825)
            ·
              refine ⟨21460681794652274760560869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28614242392869699680747825 21460681794652274760560869)
              ·
                refine ⟨4023877836497301517605163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21460681794652274760560869 4023877836497301517605163)
                ·
                  refine ⟨6035816754745952276407745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4023877836497301517605163 6035816754745952276407745)
                  ·
                    refine ⟨4526862566059464207305809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6035816754745952276407745 4526862566059464207305809)
                    ·
                      refine ⟨3395146924544598155479357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4526862566059464207305809 3395146924544598155479357)
                      ·
                        rfl

theorem cell23_6612025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 4, 1, 2, 2].length) (baseStart_6612025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6612025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6612025 prefixEnd_6612025 := by exact prefixLift 6612025
  have htrace : WordTrace (prefixWord ++ tailWord_6612025) baseStart_6612025 baseEnd_6612025 := by
    simpa [prefixWord, tailWord_6612025, baseEnd_6612025] using wordTrace_append hprefix tailTrace_6612025
  have hstable : (prefixWord ++ tailWord_6612025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6612025).length < 2 ^ (prefixWord ++ tailWord_6612025).sum := by decide
  have hdescent : baseEnd_6612025 < baseStart_6612025 := by decide
  rcases family_descends (prefixWord ++ tailWord_6612025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6612038 : List Nat := [6, 1, 1, 1, 1, 2, 3, 1, 1, 2, 4]
def baseStart_6612038 : Nat := 118140960795 + 6612038 * 2 ^ 59
def prefixEnd_6612038 : Nat := 4983230072969 + 3 ^ 40 * 6612038 * 2
def baseEnd_6612038 : Nat := 3395153599793106604616797

theorem tailTrace_6612038 : CollatzResearch.WordTrace tailWord_6612038 prefixEnd_6612038 3395153599793106604616797 := by
  unfold tailWord_6612038
  simp only [CollatzResearch.WordTrace]
  refine ⟨7536276188116345219738399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 160773892013148698021085845 7536276188116345219738399)
  ·
    refine ⟨11304414282174517829607599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7536276188116345219738399 11304414282174517829607599)
    ·
      refine ⟨16956621423261776744411399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11304414282174517829607599 16956621423261776744411399)
      ·
        refine ⟨25434932134892665116617099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16956621423261776744411399 25434932134892665116617099)
        ·
          refine ⟨38152398202338997674925649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25434932134892665116617099 38152398202338997674925649)
          ·
            refine ⟨28614298651754248256194237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38152398202338997674925649 28614298651754248256194237)
            ·
              refine ⟨10730361994407843096072839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28614298651754248256194237 10730361994407843096072839)
              ·
                refine ⟨16095542991611764644109259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10730361994407843096072839 16095542991611764644109259)
                ·
                  refine ⟨24143314487417646966163889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16095542991611764644109259 24143314487417646966163889)
                  ·
                    refine ⟨18107485865563235224622917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24143314487417646966163889 18107485865563235224622917)
                    ·
                      refine ⟨3395153599793106604616797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18107485865563235224622917 3395153599793106604616797)
                      ·
                        rfl

theorem cell23_6612038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 3, 1, 1, 2, 4].length) (baseStart_6612038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6612038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6612038 prefixEnd_6612038 := by exact prefixLift 6612038
  have htrace : WordTrace (prefixWord ++ tailWord_6612038) baseStart_6612038 baseEnd_6612038 := by
    simpa [prefixWord, tailWord_6612038, baseEnd_6612038] using wordTrace_append hprefix tailTrace_6612038
  have hstable : (prefixWord ++ tailWord_6612038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6612038).length < 2 ^ (prefixWord ++ tailWord_6612038).sum := by decide
  have hdescent : baseEnd_6612038 < baseStart_6612038 := by decide
  rcases family_descends (prefixWord ++ tailWord_6612038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6612051 : List Nat := [1, 1, 1, 2, 1, 1, 2, 8, 1, 3, 2]
def baseStart_6612051 : Nat := 118140960795 + 6612051 * 2 ^ 59
def prefixEnd_6612051 : Nat := 4983230072969 + 3 ^ 40 * 6612051 * 2
def baseEnd_6612051 : Nat := 3395160275041615053754237

theorem tailTrace_6612051 : CollatzResearch.WordTrace tailWord_6612051 prefixEnd_6612051 3395160275041615053754237 := by
  unfold tailWord_6612051
  simp only [CollatzResearch.WordTrace]
  refine ⟨241161312168675950251852007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160774208112450633501234671 241161312168675950251852007)
  ·
    refine ⟨361741968253013925377778011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241161312168675950251852007 361741968253013925377778011)
    ·
      refine ⟨542612952379520888066667017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 361741968253013925377778011 542612952379520888066667017)
      ·
        refine ⟨406959714284640666050000263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 542612952379520888066667017 406959714284640666050000263)
        ·
          refine ⟨610439571426960999075000395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 406959714284640666050000263 610439571426960999075000395)
          ·
            refine ⟨915659357140441498612500593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 610439571426960999075000395 915659357140441498612500593)
            ·
              refine ⟨686744517855331123959375445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 915659357140441498612500593 686744517855331123959375445)
              ·
                refine ⟨8047787318617161608898931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 686744517855331123959375445 8047787318617161608898931)
                ·
                  refine ⟨12071680977925742413348397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8047787318617161608898931 12071680977925742413348397)
                  ·
                    refine ⟨4526880366722153405005649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12071680977925742413348397 4526880366722153405005649)
                    ·
                      refine ⟨3395160275041615053754237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4526880366722153405005649 3395160275041615053754237)
                      ·
                        rfl

theorem cell23_6612051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 8, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 8, 1, 3, 2].length) (baseStart_6612051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6612051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6612051 prefixEnd_6612051 := by exact prefixLift 6612051
  have htrace : WordTrace (prefixWord ++ tailWord_6612051) baseStart_6612051 baseEnd_6612051 := by
    simpa [prefixWord, tailWord_6612051, baseEnd_6612051] using wordTrace_append hprefix tailTrace_6612051
  have hstable : (prefixWord ++ tailWord_6612051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6612051).length < 2 ^ (prefixWord ++ tailWord_6612051).sum := by decide
  have hdescent : baseEnd_6612051 < baseStart_6612051 := by decide
  rcases family_descends (prefixWord ++ tailWord_6612051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6612057 : List Nat := [1, 2, 1, 2, 2, 1, 2, 2, 4, 6]
def baseStart_6612057 : Nat := 118140960795 + 6612057 * 2 ^ 59
def prefixEnd_6612057 : Nat := 4983230072969 + 3 ^ 40 * 6612057 * 2
def baseEnd_6612057 : Nat := 1131721118641847343426403

theorem tailTrace_6612057 : CollatzResearch.WordTrace tailWord_6612057 prefixEnd_6612057 1131721118641847343426403 := by
  unfold tailWord_6612057
  simp only [CollatzResearch.WordTrace]
  refine ⟨241161531006654213276570425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160774354004436142184380283 241161531006654213276570425)
  ·
    refine ⟨180871148254990659957427819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241161531006654213276570425 180871148254990659957427819)
    ·
      refine ⟨271306722382485989936141729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180871148254990659957427819 271306722382485989936141729)
      ·
        refine ⟨203480041786864492452106297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 271306722382485989936141729 203480041786864492452106297)
        ·
          refine ⟨152610031340148369339079723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 203480041786864492452106297 152610031340148369339079723)
          ·
            refine ⟨228915047010222554008619585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152610031340148369339079723 228915047010222554008619585)
            ·
              refine ⟨171686285257666915506464689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 228915047010222554008619585 171686285257666915506464689)
              ·
                refine ⟨128764713943250186629848517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 171686285257666915506464689 128764713943250186629848517)
                ·
                  refine ⟨24143383864359409993096597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 128764713943250186629848517 24143383864359409993096597)
                  ·
                    refine ⟨1131721118641847343426403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24143383864359409993096597 1131721118641847343426403)
                    ·
                      rfl

theorem cell23_6612057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 2, 4, 6].length) (baseStart_6612057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6612057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6612057 prefixEnd_6612057 := by exact prefixLift 6612057
  have htrace : WordTrace (prefixWord ++ tailWord_6612057) baseStart_6612057 baseEnd_6612057 := by
    simpa [prefixWord, tailWord_6612057, baseEnd_6612057] using wordTrace_append hprefix tailTrace_6612057
  have hstable : (prefixWord ++ tailWord_6612057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6612057).length < 2 ^ (prefixWord ++ tailWord_6612057).sum := by decide
  have hdescent : baseEnd_6612057 < baseStart_6612057 := by decide
  rcases family_descends (prefixWord ++ tailWord_6612057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6612107 : List Nat := [1, 1, 1, 1, 4, 1, 1, 2, 2, 1, 8]
def baseStart_6612107 : Nat := 118140960795 + 6612107 * 2 ^ 59
def prefixEnd_6612107 : Nat := 4983230072969 + 3 ^ 40 * 6612107 * 2
def baseEnd_6612107 : Nat := 3395189029958266834653979

theorem tailTrace_6612107 : CollatzResearch.WordTrace tailWord_6612107 prefixEnd_6612107 3395189029958266834653979 := by
  unfold tailWord_6612107
  simp only [CollatzResearch.WordTrace]
  refine ⟨241163354656473071815890575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160775569770982047877260383 241163354656473071815890575)
  ·
    refine ⟨361745031984709607723835863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241163354656473071815890575 361745031984709607723835863)
    ·
      refine ⟨542617547977064411585753795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 361745031984709607723835863 542617547977064411585753795)
      ·
        refine ⟨813926321965596617378630693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 542617547977064411585753795 813926321965596617378630693)
        ·
          refine ⟨152611185368549365758493255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 813926321965596617378630693 152611185368549365758493255)
          ·
            refine ⟨228916778052824048637739883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152611185368549365758493255 228916778052824048637739883)
            ·
              refine ⟨343375167079236072956609825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 228916778052824048637739883 343375167079236072956609825)
              ·
                refine ⟨257531375309427054717457369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 343375167079236072956609825 257531375309427054717457369)
                ·
                  refine ⟨193148531482070291038093027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 257531375309427054717457369 193148531482070291038093027)
                  ·
                    refine ⟨289722797223105436557139541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 193148531482070291038093027 289722797223105436557139541)
                    ·
                      refine ⟨3395189029958266834653979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 289722797223105436557139541 3395189029958266834653979)
                      ·
                        rfl

theorem cell23_6612107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 2, 1, 8].length) (baseStart_6612107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6612107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6612107 prefixEnd_6612107 := by exact prefixLift 6612107
  have htrace : WordTrace (prefixWord ++ tailWord_6612107) baseStart_6612107 baseEnd_6612107 := by
    simpa [prefixWord, tailWord_6612107, baseEnd_6612107] using wordTrace_append hprefix tailTrace_6612107
  have hstable : (prefixWord ++ tailWord_6612107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6612107).length < 2 ^ (prefixWord ++ tailWord_6612107).sum := by decide
  have hdescent : baseEnd_6612107 < baseStart_6612107 := by decide
  rcases family_descends (prefixWord ++ tailWord_6612107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6612154 : List Nat := [3, 1, 1, 1, 2, 2, 1, 4, 1, 3, 4]
def baseStart_6612154 : Nat := 118140960795 + 6612154 * 2 ^ 59
def prefixEnd_6612154 : Nat := 4983230072969 + 3 ^ 40 * 6612154 * 2
def baseEnd_6612154 : Nat := 3395213163549028150766263

theorem tailTrace_6612154 : CollatzResearch.WordTrace tailWord_6612154 prefixEnd_6612154 3395213163549028150766263 := by
  unfold tailWord_6612154
  simp only [CollatzResearch.WordTrace]
  refine ⟨60291267221825699710712879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160776712591535199228567677 60291267221825699710712879)
  ·
    refine ⟨90436900832738549566069319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60291267221825699710712879 90436900832738549566069319)
    ·
      refine ⟨135655351249107824349103979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90436900832738549566069319 135655351249107824349103979)
      ·
        refine ⟨203483026873661736523655969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135655351249107824349103979 203483026873661736523655969)
        ·
          refine ⟨152612270155246302392741977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 203483026873661736523655969 152612270155246302392741977)
          ·
            refine ⟨114459202616434726794556483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152612270155246302392741977 114459202616434726794556483)
            ·
              refine ⟨171688803924652090191834725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114459202616434726794556483 171688803924652090191834725)
              ·
                refine ⟨32191650735872266910969011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 171688803924652090191834725 32191650735872266910969011)
                ·
                  refine ⟨48287476103808400366453517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32191650735872266910969011 48287476103808400366453517)
                  ·
                    refine ⟨18107803538928150137420069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48287476103808400366453517 18107803538928150137420069)
                    ·
                      refine ⟨3395213163549028150766263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18107803538928150137420069 3395213163549028150766263)
                      ·
                        rfl

theorem cell23_6612154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 4, 1, 3, 4].length) (baseStart_6612154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6612154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6612154 prefixEnd_6612154 := by exact prefixLift 6612154
  have htrace : WordTrace (prefixWord ++ tailWord_6612154) baseStart_6612154 baseEnd_6612154 := by
    simpa [prefixWord, tailWord_6612154, baseEnd_6612154] using wordTrace_append hprefix tailTrace_6612154
  have hstable : (prefixWord ++ tailWord_6612154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6612154).length < 2 ^ (prefixWord ++ tailWord_6612154).sum := by decide
  have hdescent : baseEnd_6612154 < baseStart_6612154 := by decide
  rcases family_descends (prefixWord ++ tailWord_6612154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6612191 : List Nat := [1, 1, 2, 3, 2, 1, 2, 4, 2, 2, 3]
def baseStart_6612191 : Nat := 118140960795 + 6612191 * 2 ^ 59
def prefixEnd_6612191 : Nat := 4983230072969 + 3 ^ 40 * 6612191 * 2
def baseEnd_6612191 : Nat := 3395232162333244506003593

theorem tailTrace_6612191 : CollatzResearch.WordTrace tailWord_6612191 prefixEnd_6612191 3395232162333244506003593 := by
  unfold tailWord_6612191
  simp only [CollatzResearch.WordTrace]
  refine ⟨241166418388168754161948427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160777612258779169441298951 241166418388168754161948427)
  ·
    refine ⟨361749627582253131242922641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241166418388168754161948427 361749627582253131242922641)
    ·
      refine ⟨271312220686689848432191981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 361749627582253131242922641 271312220686689848432191981)
      ·
        refine ⟨101742082757508693162071993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 271312220686689848432191981 101742082757508693162071993)
        ·
          refine ⟨76306562068131519871553995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101742082757508693162071993 76306562068131519871553995)
          ·
            refine ⟨114459843102197279807330993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76306562068131519871553995 114459843102197279807330993)
            ·
              refine ⟨85844882326647959855498245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114459843102197279807330993 85844882326647959855498245)
              ·
                refine ⟨16095915436246492472905921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 85844882326647959855498245 16095915436246492472905921)
                ·
                  refine ⟨12071936577184869354679441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16095915436246492472905921 12071936577184869354679441)
                  ·
                    refine ⟨9053952432888652016009581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12071936577184869354679441 9053952432888652016009581)
                    ·
                      refine ⟨3395232162333244506003593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9053952432888652016009581 3395232162333244506003593)
                      ·
                        rfl

theorem cell23_6612191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 4, 2, 2, 3].length) (baseStart_6612191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6612191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6612191 prefixEnd_6612191 := by exact prefixLift 6612191
  have htrace : WordTrace (prefixWord ++ tailWord_6612191) baseStart_6612191 baseEnd_6612191 := by
    simpa [prefixWord, tailWord_6612191, baseEnd_6612191] using wordTrace_append hprefix tailTrace_6612191
  have hstable : (prefixWord ++ tailWord_6612191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6612191).length < 2 ^ (prefixWord ++ tailWord_6612191).sum := by decide
  have hdescent : baseEnd_6612191 < baseStart_6612191 := by decide
  rcases family_descends (prefixWord ++ tailWord_6612191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6612232 : List Nat := [2, 1, 3, 2, 4, 2, 1, 3, 1, 4]
def baseStart_6612232 : Nat := 118140960795 + 6612232 * 2 ^ 59
def prefixEnd_6612232 : Nat := 4983230072969 + 3 ^ 40 * 6612232 * 2
def baseEnd_6612232 : Nat := 1131751071680026281863635

theorem tailTrace_6612232 : CollatzResearch.WordTrace tailWord_6612232 prefixEnd_6612232 1131751071680026281863635 := by
  unfold tailWord_6612232
  simp only [CollatzResearch.WordTrace]
  refine ⟨120583956890510109082095475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160778609187346812109460633 120583956890510109082095475)
  ·
    refine ⟨180875935335765163623143213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120583956890510109082095475 180875935335765163623143213)
    ·
      refine ⟨67828475750911936358678705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180875935335765163623143213 67828475750911936358678705)
      ·
        refine ⟨50871356813183952269009029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67828475750911936358678705 50871356813183952269009029)
        ·
          refine ⟨9538379402471991050439193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50871356813183952269009029 9538379402471991050439193)
          ·
            refine ⟨7153784551853993287829395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9538379402471991050439193 7153784551853993287829395)
            ·
              refine ⟨10730676827780989931744093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7153784551853993287829395 10730676827780989931744093)
              ·
                refine ⟨4024003810417871224404035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10730676827780989931744093 4024003810417871224404035)
                ·
                  refine ⟨6036005715626806836606053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4024003810417871224404035 6036005715626806836606053)
                  ·
                    refine ⟨1131751071680026281863635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6036005715626806836606053 1131751071680026281863635)
                    ·
                      rfl

theorem cell23_6612232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 1, 3, 1, 4].length) (baseStart_6612232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6612232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6612232 prefixEnd_6612232 := by exact prefixLift 6612232
  have htrace : WordTrace (prefixWord ++ tailWord_6612232) baseStart_6612232 baseEnd_6612232 := by
    simpa [prefixWord, tailWord_6612232, baseEnd_6612232] using wordTrace_append hprefix tailTrace_6612232
  have hstable : (prefixWord ++ tailWord_6612232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6612232).length < 2 ^ (prefixWord ++ tailWord_6612232).sum := by decide
  have hdescent : baseEnd_6612232 < baseStart_6612232 := by decide
  rcases family_descends (prefixWord ++ tailWord_6612232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6612241 : List Nat := [1, 2, 2, 1, 1, 4, 1, 5, 1, 5]
def baseStart_6612241 : Nat := 118140960795 + 6612241 * 2 ^ 59
def prefixEnd_6612241 : Nat := 4983230072969 + 3 ^ 40 * 6612241 * 2
def baseEnd_6612241 : Nat := 1131752612121989770126121

theorem tailTrace_6612241 : CollatzResearch.WordTrace tailWord_6612241 prefixEnd_6612241 1131752612121989770126121 := by
  unfold tailWord_6612241
  simp only [CollatzResearch.WordTrace]
  refine ⟨241168242037987612701268577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160778828025325075134179051 241168242037987612701268577)
  ·
    refine ⟨180876181528490709525951433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241168242037987612701268577 180876181528490709525951433)
    ·
      refine ⟨135657136146368032144463575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180876181528490709525951433 135657136146368032144463575)
      ·
        refine ⟨203485704219552048216695363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135657136146368032144463575 203485704219552048216695363)
        ·
          refine ⟨305228556329328072325043045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203485704219552048216695363 305228556329328072325043045)
          ·
            refine ⟨57230354311749013560945571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 305228556329328072325043045 57230354311749013560945571)
            ·
              refine ⟨85845531467623520341418357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57230354311749013560945571 85845531467623520341418357)
              ·
                refine ⟨8048018575089705032007971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 85845531467623520341418357 8048018575089705032007971)
                ·
                  refine ⟨12072027862634557548011957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8048018575089705032007971 12072027862634557548011957)
                  ·
                    refine ⟨1131752612121989770126121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12072027862634557548011957 1131752612121989770126121)
                    ·
                      rfl

theorem cell23_6612241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 5].length) (baseStart_6612241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6612241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6612241 prefixEnd_6612241 := by exact prefixLift 6612241
  have htrace : WordTrace (prefixWord ++ tailWord_6612241) baseStart_6612241 baseEnd_6612241 := by
    simpa [prefixWord, tailWord_6612241, baseEnd_6612241] using wordTrace_append hprefix tailTrace_6612241
  have hstable : (prefixWord ++ tailWord_6612241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6612241).length < 2 ^ (prefixWord ++ tailWord_6612241).sum := by decide
  have hdescent : baseEnd_6612241 < baseStart_6612241 := by decide
  rcases family_descends (prefixWord ++ tailWord_6612241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6612242 : List Nat := [3, 2, 4, 2, 1, 1, 1, 2, 2, 2, 3]
def baseStart_6612242 : Nat := 118140960795 + 6612242 * 2 ^ 59
def prefixEnd_6612242 : Nat := 4983230072969 + 3 ^ 40 * 6612242 * 2
def baseEnd_6612242 : Nat := 3395258349846623806465859

theorem tailTrace_6612242 : CollatzResearch.WordTrace tailWord_6612242 prefixEnd_6612242 3395258349846623806465859 := by
  unfold tailWord_6612242
  simp only [CollatzResearch.WordTrace]
  refine ⟨60292069627745997468013745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160778852340655993248036653 60292069627745997468013745)
  ·
    refine ⟨45219052220809498101010309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60292069627745997468013745 45219052220809498101010309)
    ·
      refine ⟨8478572291401780893939433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45219052220809498101010309 8478572291401780893939433)
      ·
        refine ⟨6358929218551335670454575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8478572291401780893939433 6358929218551335670454575)
        ·
          refine ⟨9538393827827003505681863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6358929218551335670454575 9538393827827003505681863)
          ·
            refine ⟨14307590741740505258522795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9538393827827003505681863 14307590741740505258522795)
            ·
              refine ⟨21461386112610757887784193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14307590741740505258522795 21461386112610757887784193)
              ·
                refine ⟨16096039584458068415838145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21461386112610757887784193 16096039584458068415838145)
                ·
                  refine ⟨12072029688343551311878609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16096039584458068415838145 12072029688343551311878609)
                  ·
                    refine ⟨9054022266257663483908957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12072029688343551311878609 9054022266257663483908957)
                    ·
                      refine ⟨3395258349846623806465859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9054022266257663483908957 3395258349846623806465859)
                      ·
                        rfl

theorem cell23_6612242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_6612242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6612242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6612242 prefixEnd_6612242 := by exact prefixLift 6612242
  have htrace : WordTrace (prefixWord ++ tailWord_6612242) baseStart_6612242 baseEnd_6612242 := by
    simpa [prefixWord, tailWord_6612242, baseEnd_6612242] using wordTrace_append hprefix tailTrace_6612242
  have hstable : (prefixWord ++ tailWord_6612242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6612242).length < 2 ^ (prefixWord ++ tailWord_6612242).sum := by decide
  have hdescent : baseEnd_6612242 < baseStart_6612242 := by decide
  rcases family_descends (prefixWord ++ tailWord_6612242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6612248 : List Nat := [2, 1, 2, 3, 1, 3, 1, 1, 4, 3, 2]
def baseStart_6612248 : Nat := 118140960795 + 6612248 * 2 ^ 59
def prefixEnd_6612248 : Nat := 4983230072969 + 3 ^ 40 * 6612248 * 2
def baseEnd_6612248 : Nat := 3395261430730550782990831

theorem tailTrace_6612248 : CollatzResearch.WordTrace tailWord_6612248 prefixEnd_6612248 3395261430730550782990831 := by
  unfold tailWord_6612248
  simp only [CollatzResearch.WordTrace]
  refine ⟨120584248674481126448386699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160778998232641501931182265 120584248674481126448386699)
  ·
    refine ⟨180876373011721689672580049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120584248674481126448386699 180876373011721689672580049)
    ·
      refine ⟨135657279758791267254435037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180876373011721689672580049 135657279758791267254435037)
      ·
        refine ⟨50871479909546725220413139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135657279758791267254435037 50871479909546725220413139)
        ·
          refine ⟨76307219864320087830619709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50871479909546725220413139 76307219864320087830619709)
          ·
            refine ⟨28615207449120032936482391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76307219864320087830619709 28615207449120032936482391)
            ·
              refine ⟨42922811173680049404723587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28615207449120032936482391 42922811173680049404723587)
              ·
                refine ⟨64384216760520074107085381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42922811173680049404723587 64384216760520074107085381)
                ·
                  refine ⟨12072040642597513895078509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64384216760520074107085381 12072040642597513895078509)
                  ·
                    refine ⟨4527015240974067710654441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12072040642597513895078509 4527015240974067710654441)
                    ·
                      refine ⟨3395261430730550782990831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4527015240974067710654441 3395261430730550782990831)
                      ·
                        rfl

theorem cell23_6612248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 1, 4, 3, 2].length) (baseStart_6612248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6612248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6612248 prefixEnd_6612248 := by exact prefixLift 6612248
  have htrace : WordTrace (prefixWord ++ tailWord_6612248) baseStart_6612248 baseEnd_6612248 := by
    simpa [prefixWord, tailWord_6612248, baseEnd_6612248] using wordTrace_append hprefix tailTrace_6612248
  have hstable : (prefixWord ++ tailWord_6612248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6612248).length < 2 ^ (prefixWord ++ tailWord_6612248).sum := by decide
  have hdescent : baseEnd_6612248 < baseStart_6612248 := by decide
  rcases family_descends (prefixWord ++ tailWord_6612248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6612292 : List Nat := [2, 3, 4, 1, 1, 2, 3, 1, 1, 5]
def baseStart_6612292 : Nat := 118140960795 + 6612292 * 2 ^ 59
def prefixEnd_6612292 : Nat := 4983230072969 + 3 ^ 40 * 6612292 * 2
def baseEnd_6612292 : Nat := 1131761341293116203613543

theorem tailTrace_6612292 : CollatzResearch.WordTrace tailWord_6612292 prefixEnd_6612292 1131761341293116203613543 := by
  unfold tailWord_6612292
  simp only [CollatzResearch.WordTrace]
  refine ⟨120585051080401424205687565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160780068107201898940916753 120585051080401424205687565)
  ·
    refine ⟨45219394155150534077132837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120585051080401424205687565 45219394155150534077132837)
    ·
      refine ⟨8478636404090725139462407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45219394155150534077132837 8478636404090725139462407)
      ·
        refine ⟨12717954606136087709193611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8478636404090725139462407 12717954606136087709193611)
        ·
          refine ⟨19076931909204131563790417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12717954606136087709193611 19076931909204131563790417)
          ·
            refine ⟨14307698931903098672842813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19076931909204131563790417 14307698931903098672842813)
            ·
              refine ⟨5365387099463662002316055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14307698931903098672842813 5365387099463662002316055)
              ·
                refine ⟨8048080649195493003474083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5365387099463662002316055 8048080649195493003474083)
                ·
                  refine ⟨12072120973793239505211125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8048080649195493003474083 12072120973793239505211125)
                  ·
                    refine ⟨1131761341293116203613543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12072120973793239505211125 1131761341293116203613543)
                    ·
                      rfl

theorem cell23_6612292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_6612292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6612292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6612292 prefixEnd_6612292 := by exact prefixLift 6612292
  have htrace : WordTrace (prefixWord ++ tailWord_6612292) baseStart_6612292 baseEnd_6612292 := by
    simpa [prefixWord, tailWord_6612292, baseEnd_6612292] using wordTrace_append hprefix tailTrace_6612292
  have hstable : (prefixWord ++ tailWord_6612292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6612292).length < 2 ^ (prefixWord ++ tailWord_6612292).sum := by decide
  have hdescent : baseEnd_6612292 < baseStart_6612292 := by decide
  rcases family_descends (prefixWord ++ tailWord_6612292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6612295 : List Nat := [1, 1, 4, 1, 2, 4, 3, 1, 1, 1, 4]
def baseStart_6612295 : Nat := 118140960795 + 6612295 * 2 ^ 59
def prefixEnd_6612295 : Nat := 4983230072969 + 3 ^ 40 * 6612295 * 2
def baseEnd_6612295 : Nat := 3395285564321312099103115

theorem tailTrace_6612295 : CollatzResearch.WordTrace tailWord_6612295 prefixEnd_6612295 3395285564321312099103115 := by
  unfold tailWord_6612295
  simp only [CollatzResearch.WordTrace]
  refine ⟨241170211579791979923734339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160780141053194653282489559 241170211579791979923734339)
  ·
    refine ⟨361755317369687969885601509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241170211579791979923734339 361755317369687969885601509)
    ·
      refine ⟨67829122006816494353550283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 361755317369687969885601509 67829122006816494353550283)
      ·
        refine ⟨101743683010224741530325425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67829122006816494353550283 101743683010224741530325425)
        ·
          refine ⟨76307762257668556147744069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101743683010224741530325425 76307762257668556147744069)
          ·
            refine ⟨14307705423312854277702013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76307762257668556147744069 14307705423312854277702013)
            ·
              refine ⟨5365389533742320354138255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14307705423312854277702013 5365389533742320354138255)
              ·
                refine ⟨8048084300613480531207383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5365389533742320354138255 8048084300613480531207383)
                ·
                  refine ⟨12072126450920220796811075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8048084300613480531207383 12072126450920220796811075)
                  ·
                    refine ⟨18108189676380331195216613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12072126450920220796811075 18108189676380331195216613)
                    ·
                      refine ⟨3395285564321312099103115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18108189676380331195216613 3395285564321312099103115)
                      ·
                        rfl

theorem cell23_6612295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 3, 1, 1, 1, 4].length) (baseStart_6612295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6612295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6612295 prefixEnd_6612295 := by exact prefixLift 6612295
  have htrace : WordTrace (prefixWord ++ tailWord_6612295) baseStart_6612295 baseEnd_6612295 := by
    simpa [prefixWord, tailWord_6612295, baseEnd_6612295] using wordTrace_append hprefix tailTrace_6612295
  have hstable : (prefixWord ++ tailWord_6612295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6612295).length < 2 ^ (prefixWord ++ tailWord_6612295).sum := by decide
  have hdescent : baseEnd_6612295 < baseStart_6612295 := by decide
  rcases family_descends (prefixWord ++ tailWord_6612295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6612298 : List Nat := [3, 1, 2, 1, 1, 1, 1, 7, 1, 2, 3]
def baseStart_6612298 : Nat := 118140960795 + 6612298 * 2 ^ 59
def prefixEnd_6612298 : Nat := 4983230072969 + 3 ^ 40 * 6612298 * 2
def baseEnd_6612298 : Nat := 3395287104763275587365601

theorem tailTrace_6612298 : CollatzResearch.WordTrace tailWord_6612298 prefixEnd_6612298 3395287104763275587365601 := by
  unfold tailWord_6612298
  simp only [CollatzResearch.WordTrace]
  refine ⟨60292580249695277859023387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160780213999187407624062365 60292580249695277859023387)
  ·
    refine ⟨90438870374542916788535081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60292580249695277859023387 90438870374542916788535081)
    ·
      refine ⟨67829152780907187591401311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90438870374542916788535081 67829152780907187591401311)
      ·
        refine ⟨101743729171360781387101967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67829152780907187591401311 101743729171360781387101967)
        ·
          refine ⟨152615593757041172080652951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101743729171360781387101967 152615593757041172080652951)
          ·
            refine ⟨228923390635561758120979427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152615593757041172080652951 228923390635561758120979427)
            ·
              refine ⟨343385085953342637181469141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 228923390635561758120979427 343385085953342637181469141)
              ·
                refine ⟨8048087952031468058940683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 343385085953342637181469141 8048087952031468058940683)
                ·
                  refine ⟨12072131928047202088411025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8048087952031468058940683 12072131928047202088411025)
                  ·
                    refine ⟨9054098946035401566308269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12072131928047202088411025 9054098946035401566308269)
                    ·
                      refine ⟨3395287104763275587365601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9054098946035401566308269 3395287104763275587365601)
                      ·
                        rfl

theorem cell23_6612298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 7, 1, 2, 3].length) (baseStart_6612298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6612298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6612298 prefixEnd_6612298 := by exact prefixLift 6612298
  have htrace : WordTrace (prefixWord ++ tailWord_6612298) baseStart_6612298 baseEnd_6612298 := by
    simpa [prefixWord, tailWord_6612298, baseEnd_6612298] using wordTrace_append hprefix tailTrace_6612298
  have hstable : (prefixWord ++ tailWord_6612298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6612298).length < 2 ^ (prefixWord ++ tailWord_6612298).sum := by decide
  have hdescent : baseEnd_6612298 < baseStart_6612298 := by decide
  rcases family_descends (prefixWord ++ tailWord_6612298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6612312 : List Nat := [2, 1, 2, 2, 1, 1, 5, 4, 1, 2, 2]
def baseStart_6612312 : Nat := 118140960795 + 6612312 * 2 ^ 59
def prefixEnd_6612312 : Nat := 4983230072969 + 3 ^ 40 * 6612312 * 2
def baseEnd_6612312 : Nat := 3395294293492438532590537

theorem tailTrace_6612312 : CollatzResearch.WordTrace tailWord_6612312 prefixEnd_6612312 3395294293492438532590537 := by
  unfold tailWord_6612312
  simp only [CollatzResearch.WordTrace]
  refine ⟨120585415810365195913551595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160780554413820261218068793 120585415810365195913551595)
  ·
    refine ⟨180878123715547793870327393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120585415810365195913551595 180878123715547793870327393)
    ·
      refine ⟨135658592786660845402745545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180878123715547793870327393 135658592786660845402745545)
      ·
        refine ⟨101743944589995634052059159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135658592786660845402745545 101743944589995634052059159)
        ·
          refine ⟨152615916884993451078088739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101743944589995634052059159 152615916884993451078088739)
          ·
            refine ⟨228923875327490176617133109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152615916884993451078088739 228923875327490176617133109)
            ·
              refine ⟨21461613311952204057856229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 228923875327490176617133109 21461613311952204057856229)
              ·
                refine ⟨4024052495991038260848043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21461613311952204057856229 4024052495991038260848043)
                ·
                  refine ⟨6036078743986557391272065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4024052495991038260848043 6036078743986557391272065)
                  ·
                    refine ⟨4527059057989918043454049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6036078743986557391272065 4527059057989918043454049)
                    ·
                      refine ⟨3395294293492438532590537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4527059057989918043454049 3395294293492438532590537)
                      ·
                        rfl

theorem cell23_6612312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 4, 1, 2, 2].length) (baseStart_6612312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6612312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6612312 prefixEnd_6612312 := by exact prefixLift 6612312
  have htrace : WordTrace (prefixWord ++ tailWord_6612312) baseStart_6612312 baseEnd_6612312 := by
    simpa [prefixWord, tailWord_6612312, baseEnd_6612312] using wordTrace_append hprefix tailTrace_6612312
  have hstable : (prefixWord ++ tailWord_6612312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6612312).length < 2 ^ (prefixWord ++ tailWord_6612312).sum := by decide
  have hdescent : baseEnd_6612312 < baseStart_6612312 := by decide
  rcases family_descends (prefixWord ++ tailWord_6612312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6612431 : List Nat := [1, 1, 2, 1, 1, 4, 3, 1, 1, 1, 7]
def baseStart_6612431 : Nat := 118140960795 + 6612431 * 2 ^ 59
def prefixEnd_6612431 : Nat := 4983230072969 + 3 ^ 40 * 6612431 * 2
def baseEnd_6612431 : Nat := 3395355397690323567002489

theorem tailTrace_6612431 : CollatzResearch.WordTrace tailWord_6612431 prefixEnd_6612431 3395355397690323567002489 := by
  unfold tailWord_6612431
  simp only [CollatzResearch.WordTrace]
  refine ⟨241175171907299275150685147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160783447938199516767123431 241175171907299275150685147)
  ·
    refine ⟨361762757860948912726027721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241175171907299275150685147 361762757860948912726027721)
    ·
      refine ⟨271322068395711684544520791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 361762757860948912726027721 271322068395711684544520791)
      ·
        refine ⟨406983102593567526816781187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271322068395711684544520791 406983102593567526816781187)
        ·
          refine ⟨610474653890351290225171781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 406983102593567526816781187 610474653890351290225171781)
          ·
            refine ⟨114463997604440866917219709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 610474653890351290225171781 114463997604440866917219709)
            ·
              refine ⟨42923999101665325093957391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 114463997604440866917219709 42923999101665325093957391)
              ·
                refine ⟨64385998652497987640936087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42923999101665325093957391 64385998652497987640936087)
                ·
                  refine ⟨96578997978746981461404131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64385998652497987640936087 96578997978746981461404131)
                  ·
                    refine ⟨144868496968120472192106197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 96578997978746981461404131 144868496968120472192106197)
                    ·
                      refine ⟨3395355397690323567002489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 144868496968120472192106197 3395355397690323567002489)
                      ·
                        rfl

theorem cell23_6612431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 1, 1, 1, 7].length) (baseStart_6612431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6612431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6612431 prefixEnd_6612431 := by exact prefixLift 6612431
  have htrace : WordTrace (prefixWord ++ tailWord_6612431) baseStart_6612431 baseEnd_6612431 := by
    simpa [prefixWord, tailWord_6612431, baseEnd_6612431] using wordTrace_append hprefix tailTrace_6612431
  have hstable : (prefixWord ++ tailWord_6612431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6612431).length < 2 ^ (prefixWord ++ tailWord_6612431).sum := by decide
  have hdescent : baseEnd_6612431 < baseStart_6612431 := by decide
  rcases family_descends (prefixWord ++ tailWord_6612431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6612455 : List Nat := [1, 1, 5, 2, 1, 3, 2, 1, 2, 5]
def baseStart_6612455 : Nat := 118140960795 + 6612455 * 2 ^ 59
def prefixEnd_6612455 : Nat := 4983230072969 + 3 ^ 40 * 6612455 * 2
def baseEnd_6612455 : Nat := 1131789240408677157700793

theorem tailTrace_6612455 : CollatzResearch.WordTrace tailWord_6612455 prefixEnd_6612455 1131789240408677157700793 := by
  unfold tailWord_6612455
  simp only [CollatzResearch.WordTrace]
  refine ⟨241176047259212327249558819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160784031506141551499705879 241176047259212327249558819)
  ·
    refine ⟨361764070888818490874338229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241176047259212327249558819 361764070888818490874338229)
    ·
      refine ⟨33915381645826733519469209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 361764070888818490874338229 33915381645826733519469209)
      ·
        refine ⟨25436536234370050139601907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33915381645826733519469209 25436536234370050139601907)
        ·
          refine ⟨38154804351555075209402861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25436536234370050139601907 38154804351555075209402861)
          ·
            refine ⟨14308051631833153203526073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38154804351555075209402861 14308051631833153203526073)
            ·
              refine ⟨10731038723874864902644555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14308051631833153203526073 10731038723874864902644555)
              ·
                refine ⟨16096558085812297353966833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10731038723874864902644555 16096558085812297353966833)
                ·
                  refine ⟨12072418564359223015475125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16096558085812297353966833 12072418564359223015475125)
                  ·
                    refine ⟨1131789240408677157700793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12072418564359223015475125 1131789240408677157700793)
                    ·
                      rfl

theorem cell23_6612455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 2, 1, 2, 5].length) (baseStart_6612455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6612455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6612455 prefixEnd_6612455 := by exact prefixLift 6612455
  have htrace : WordTrace (prefixWord ++ tailWord_6612455) baseStart_6612455 baseEnd_6612455 := by
    simpa [prefixWord, tailWord_6612455, baseEnd_6612455] using wordTrace_append hprefix tailTrace_6612455
  have hstable : (prefixWord ++ tailWord_6612455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6612455).length < 2 ^ (prefixWord ++ tailWord_6612455).sum := by decide
  have hdescent : baseEnd_6612455 < baseStart_6612455 := by decide
  rcases family_descends (prefixWord ++ tailWord_6612455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6612486 : List Nat := [6, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3]
def baseStart_6612486 : Nat := 118140960795 + 6612486 * 2 ^ 59
def prefixEnd_6612486 : Nat := 4983230072969 + 3 ^ 40 * 6612486 * 2
def baseEnd_6612486 : Nat := 3395383639126320851814737

theorem tailTrace_6612486 : CollatzResearch.WordTrace tailWord_6612486 prefixEnd_6612486 3395383639126320851814737 := by
  unfold tailWord_6612486
  simp only [CollatzResearch.WordTrace]
  refine ⟨7536786810065625610748041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 160784785281400013029291541 7536786810065625610748041)
  ·
    refine ⟨5652590107549219208061031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7536786810065625610748041 5652590107549219208061031)
    ·
      refine ⟨8478885161323828812091547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5652590107549219208061031 8478885161323828812091547)
      ·
        refine ⟨12718327741985743218137321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8478885161323828812091547 12718327741985743218137321)
        ·
          refine ⟨9538745806489307413602991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12718327741985743218137321 9538745806489307413602991)
          ·
            refine ⟨14308118709733961120404487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9538745806489307413602991 14308118709733961120404487)
            ·
              refine ⟨21462178064600941680606731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14308118709733961120404487 21462178064600941680606731)
              ·
                refine ⟨32193267096901412520910097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21462178064600941680606731 32193267096901412520910097)
                ·
                  refine ⟨24144950322676059390682573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32193267096901412520910097 24144950322676059390682573)
                  ·
                    refine ⟨9054356371003522271505965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24144950322676059390682573 9054356371003522271505965)
                    ·
                      refine ⟨3395383639126320851814737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9054356371003522271505965 3395383639126320851814737)
                      ·
                        rfl

theorem cell23_6612486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_6612486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6612486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6612486 prefixEnd_6612486 := by exact prefixLift 6612486
  have htrace : WordTrace (prefixWord ++ tailWord_6612486) baseStart_6612486 baseEnd_6612486 := by
    simpa [prefixWord, tailWord_6612486, baseEnd_6612486] using wordTrace_append hprefix tailTrace_6612486
  have hstable : (prefixWord ++ tailWord_6612486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6612486).length < 2 ^ (prefixWord ++ tailWord_6612486).sum := by decide
  have hdescent : baseEnd_6612486 < baseStart_6612486 := by decide
  rcases family_descends (prefixWord ++ tailWord_6612486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6612492 : List Nat := [2, 2, 1, 2, 5, 1, 1, 1, 2, 4, 2]
def baseStart_6612492 : Nat := 118140960795 + 6612492 * 2 ^ 59
def prefixEnd_6612492 : Nat := 4983230072969 + 3 ^ 40 * 6612492 * 2
def baseEnd_6612492 : Nat := 3395386720010247828339709

theorem tailTrace_6612492 : CollatzResearch.WordTrace tailWord_6612492 prefixEnd_6612492 3395386720010247828339709 := by
  unfold tailWord_6612492
  simp only [CollatzResearch.WordTrace]
  refine ⟨120588698380039141284327865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160784931173385521712437153 120588698380039141284327865)
  ·
    refine ⟨90441523785029355963245899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120588698380039141284327865 90441523785029355963245899)
    ·
      refine ⟨135662285677544033944868849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90441523785029355963245899 135662285677544033944868849)
      ·
        refine ⟨101746714258158025458651637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135662285677544033944868849 101746714258158025458651637)
        ·
          refine ⟨9538754461702314886748591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 101746714258158025458651637 9538754461702314886748591)
          ·
            refine ⟨14308131692553472330122887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9538754461702314886748591 14308131692553472330122887)
            ·
              refine ⟨21462197538830208495184331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14308131692553472330122887 21462197538830208495184331)
              ·
                refine ⟨32193296308245312742776497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21462197538830208495184331 32193296308245312742776497)
                ·
                  refine ⟨24144972231183984557082373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32193296308245312742776497 24144972231183984557082373)
                  ·
                    refine ⟨4527182293346997104452945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24144972231183984557082373 4527182293346997104452945)
                    ·
                      refine ⟨3395386720010247828339709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4527182293346997104452945 3395386720010247828339709)
                      ·
                        rfl

theorem cell23_6612492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 1, 2, 4, 2].length) (baseStart_6612492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6612492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6612492 prefixEnd_6612492 := by exact prefixLift 6612492
  have htrace : WordTrace (prefixWord ++ tailWord_6612492) baseStart_6612492 baseEnd_6612492 := by
    simpa [prefixWord, tailWord_6612492, baseEnd_6612492] using wordTrace_append hprefix tailTrace_6612492
  have hstable : (prefixWord ++ tailWord_6612492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6612492).length < 2 ^ (prefixWord ++ tailWord_6612492).sum := by decide
  have hdescent : baseEnd_6612492 < baseStart_6612492 := by decide
  rcases family_descends (prefixWord ++ tailWord_6612492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6612512 : List Nat := [2, 1, 1, 6, 1, 1, 3, 1, 2, 2, 3]
def baseStart_6612512 : Nat := 118140960795 + 6612512 * 2 ^ 59
def prefixEnd_6612512 : Nat := 4983230072969 + 3 ^ 40 * 6612512 * 2
def baseEnd_6612512 : Nat := 3395396989623337750089617

theorem tailTrace_6612512 : CollatzResearch.WordTrace tailWord_6612512 prefixEnd_6612512 3395396989623337750089617 := by
  unfold tailWord_6612512
  simp only [CollatzResearch.WordTrace]
  refine ⟨120589063110002912992191895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160785417480003883989589193 120589063110002912992191895)
  ·
    refine ⟨180883594665004369488287843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120589063110002912992191895 180883594665004369488287843)
    ·
      refine ⟨271325391997506554232431765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180883594665004369488287843 271325391997506554232431765)
      ·
        refine ⟨12718377749883119729645239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 271325391997506554232431765 12718377749883119729645239)
        ·
          refine ⟨19077566624824679594467859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12718377749883119729645239 19077566624824679594467859)
          ·
            refine ⟨28616349937237019391701789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19077566624824679594467859 28616349937237019391701789)
            ·
              refine ⟨10731131226463882271888171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28616349937237019391701789 10731131226463882271888171)
              ·
                refine ⟨16096696839695823407832257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10731131226463882271888171 16096696839695823407832257)
                ·
                  refine ⟨12072522629771867555874193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16096696839695823407832257 12072522629771867555874193)
                  ·
                    refine ⟨9054391972328900666905645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12072522629771867555874193 9054391972328900666905645)
                    ·
                      refine ⟨3395396989623337750089617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9054391972328900666905645 3395396989623337750089617)
                      ·
                        rfl

theorem cell23_6612512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_6612512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6612512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6612512 prefixEnd_6612512 := by exact prefixLift 6612512
  have htrace : WordTrace (prefixWord ++ tailWord_6612512) baseStart_6612512 baseEnd_6612512 := by
    simpa [prefixWord, tailWord_6612512, baseEnd_6612512] using wordTrace_append hprefix tailTrace_6612512
  have hstable : (prefixWord ++ tailWord_6612512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6612512).length < 2 ^ (prefixWord ++ tailWord_6612512).sum := by decide
  have hdescent : baseEnd_6612512 < baseStart_6612512 := by decide
  rcases family_descends (prefixWord ++ tailWord_6612512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6612562 : List Nat := [3, 2, 2, 1, 2, 3, 2, 2, 1, 5]
def baseStart_6612562 : Nat := 118140960795 + 6612562 * 2 ^ 59
def prefixEnd_6612562 : Nat := 4983230072969 + 3 ^ 40 * 6612562 * 2
def baseEnd_6612562 : Nat := 1131807554552020851488129

theorem tailTrace_6612562 : CollatzResearch.WordTrace tailWord_6612562 prefixEnd_6612562 1131807554552020851488129 := by
  unfold tailWord_6612562
  simp only [CollatzResearch.WordTrace]
  refine ⟨60294987467456171130925985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160786633246549789682469293 60294987467456171130925985)
  ·
    refine ⟨45221240600592128348194489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60294987467456171130925985 45221240600592128348194489)
    ·
      refine ⟨33915930450444096261145867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45221240600592128348194489 33915930450444096261145867)
      ·
        refine ⟨50873895675666144391718801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33915930450444096261145867 50873895675666144391718801)
        ·
          refine ⟨38155421756749608293789101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50873895675666144391718801 38155421756749608293789101)
          ·
            refine ⟨14308283158781103110170913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38155421756749608293789101 14308283158781103110170913)
            ·
              refine ⟨10731212369085827332628185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14308283158781103110170913 10731212369085827332628185)
              ·
                refine ⟨8048409276814370499471139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10731212369085827332628185 8048409276814370499471139)
                ·
                  refine ⟨12072613915221555749206709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8048409276814370499471139 12072613915221555749206709)
                  ·
                    refine ⟨1131807554552020851488129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12072613915221555749206709 1131807554552020851488129)
                    ·
                      rfl

theorem cell23_6612562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 2, 2, 1, 5].length) (baseStart_6612562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6612562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6612562 prefixEnd_6612562 := by exact prefixLift 6612562
  have htrace : WordTrace (prefixWord ++ tailWord_6612562) baseStart_6612562 baseEnd_6612562 := by
    simpa [prefixWord, tailWord_6612562, baseEnd_6612562] using wordTrace_append hprefix tailTrace_6612562
  have hstable : (prefixWord ++ tailWord_6612562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6612562).length < 2 ^ (prefixWord ++ tailWord_6612562).sum := by decide
  have hdescent : baseEnd_6612562 < baseStart_6612562 := by decide
  rcases family_descends (prefixWord ++ tailWord_6612562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6612565 : List Nat := [1, 3, 2, 2, 1, 1, 1, 1, 1, 8, 2]
def baseStart_6612565 : Nat := 118140960795 + 6612565 * 2 ^ 59
def prefixEnd_6612565 : Nat := 4983230072969 + 3 ^ 40 * 6612565 * 2
def baseEnd_6612565 : Nat := 3395424204098026042726873

theorem tailTrace_6612565 : CollatzResearch.WordTrace tailWord_6612565 prefixEnd_6612565 3395424204098026042726873 := by
  unfold tailWord_6612565
  simp only [CollatzResearch.WordTrace]
  refine ⟨241180059288813816036063149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160786706192542544024042099 241180059288813816036063149)
  ·
    refine ⟨90442522233305181013523681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 241180059288813816036063149 90442522233305181013523681)
    ·
      refine ⟨67831891674978885760142761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90442522233305181013523681 67831891674978885760142761)
      ·
        refine ⟨50873918756234164320107071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67831891674978885760142761 50873918756234164320107071)
        ·
          refine ⟨76310878134351246480160607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50873918756234164320107071 76310878134351246480160607)
          ·
            refine ⟨114466317201526869720240911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76310878134351246480160607 114466317201526869720240911)
            ·
              refine ⟨171699475802290304580361367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114466317201526869720240911 171699475802290304580361367)
              ·
                refine ⟨257549213703435456870542051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 171699475802290304580361367 257549213703435456870542051)
                ·
                  refine ⟨386323820555153185305813077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 257549213703435456870542051 386323820555153185305813077)
                  ·
                    refine ⟨4527232272130701390302497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 386323820555153185305813077 4527232272130701390302497)
                    ·
                      refine ⟨3395424204098026042726873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4527232272130701390302497 3395424204098026042726873)
                      ·
                        rfl

theorem cell23_6612565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 8, 2].length) (baseStart_6612565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6612565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6612565 prefixEnd_6612565 := by exact prefixLift 6612565
  have htrace : WordTrace (prefixWord ++ tailWord_6612565) baseStart_6612565 baseEnd_6612565 := by
    simpa [prefixWord, tailWord_6612565, baseEnd_6612565] using wordTrace_append hprefix tailTrace_6612565
  have hstable : (prefixWord ++ tailWord_6612565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6612565).length < 2 ^ (prefixWord ++ tailWord_6612565).sum := by decide
  have hdescent : baseEnd_6612565 < baseStart_6612565 := by decide
  rcases family_descends (prefixWord ++ tailWord_6612565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6612568 : List Nat := [2, 1, 2, 2, 1, 2, 1, 1, 5, 1, 5]
def baseStart_6612568 : Nat := 118140960795 + 6612568 * 2 ^ 59
def prefixEnd_6612568 : Nat := 4983230072969 + 3 ^ 40 * 6612568 * 2
def baseEnd_6612568 : Nat := 3395425744539989530989359

theorem tailTrace_6612568 : CollatzResearch.WordTrace tailWord_6612568 prefixEnd_6612568 3395425744539989530989359 := by
  unfold tailWord_6612568
  simp only [CollatzResearch.WordTrace]
  refine ⟨120590084353901473774211179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160786779138535298365614905 120590084353901473774211179)
  ·
    refine ⟨180885126530852210661316769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120590084353901473774211179 180885126530852210661316769)
    ·
      refine ⟨135663844898139157995987577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180885126530852210661316769 135663844898139157995987577)
      ·
        refine ⟨101747883673604368496990683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135663844898139157995987577 101747883673604368496990683)
        ·
          refine ⟨152621825510406552745486025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101747883673604368496990683 152621825510406552745486025)
          ·
            refine ⟨114466369132804914559114519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152621825510406552745486025 114466369132804914559114519)
            ·
              refine ⟨171699553699207371838671779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114466369132804914559114519 171699553699207371838671779)
              ·
                refine ⟨257549330548811057758007669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 171699553699207371838671779 257549330548811057758007669)
                ·
                  refine ⟨24145249738951036664813219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 257549330548811057758007669 24145249738951036664813219)
                  ·
                    refine ⟨36217874608426554997219829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24145249738951036664813219 36217874608426554997219829)
                    ·
                      refine ⟨3395425744539989530989359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36217874608426554997219829 3395425744539989530989359)
                      ·
                        rfl

theorem cell23_6612568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 5, 1, 5].length) (baseStart_6612568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6612568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6612568 prefixEnd_6612568 := by exact prefixLift 6612568
  have htrace : WordTrace (prefixWord ++ tailWord_6612568) baseStart_6612568 baseEnd_6612568 := by
    simpa [prefixWord, tailWord_6612568, baseEnd_6612568] using wordTrace_append hprefix tailTrace_6612568
  have hstable : (prefixWord ++ tailWord_6612568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6612568).length < 2 ^ (prefixWord ++ tailWord_6612568).sum := by decide
  have hdescent : baseEnd_6612568 < baseStart_6612568 := by decide
  rcases family_descends (prefixWord ++ tailWord_6612568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6612605 : List Nat := [1, 4, 1, 1, 4, 2, 2, 8]
def baseStart_6612605 : Nat := 118140960795 + 6612605 * 2 ^ 59
def prefixEnd_6612605 : Nat := 4983230072969 + 3 ^ 40 * 6612605 * 2
def baseEnd_6612605 : Nat := 125757212715711329119507

theorem tailTrace_6612605 : CollatzResearch.WordTrace tailWord_6612605 prefixEnd_6612605 125757212715711329119507 := by
  unfold tailWord_6612605
  simp only [CollatzResearch.WordTrace]
  refine ⟨241181518208668902867519269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160787678805779268578346179 241181518208668902867519269)
  ·
    refine ⟨45221534664125419287659863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 241181518208668902867519269 45221534664125419287659863)
    ·
      refine ⟨67832301996188128931489795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45221534664125419287659863 67832301996188128931489795)
      ·
        refine ⟨101748452994282193397234693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67832301996188128931489795 101748452994282193397234693)
        ·
          refine ⟨19077834936427911261981505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 101748452994282193397234693 19077834936427911261981505)
          ·
            refine ⟨14308376202320933446486129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19077834936427911261981505 14308376202320933446486129)
            ·
              refine ⟨10731282151740700084864597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14308376202320933446486129 10731282151740700084864597)
              ·
                refine ⟨125757212715711329119507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10731282151740700084864597 125757212715711329119507)
                ·
                  rfl

theorem cell23_6612605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 2, 8].length) (baseStart_6612605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6612605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6612605 prefixEnd_6612605 := by exact prefixLift 6612605
  have htrace : WordTrace (prefixWord ++ tailWord_6612605) baseStart_6612605 baseEnd_6612605 := by
    simpa [prefixWord, tailWord_6612605, baseEnd_6612605] using wordTrace_append hprefix tailTrace_6612605
  have hstable : (prefixWord ++ tailWord_6612605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6612605).length < 2 ^ (prefixWord ++ tailWord_6612605).sum := by decide
  have hdescent : baseEnd_6612605 < baseStart_6612605 := by decide
  rcases family_descends (prefixWord ++ tailWord_6612605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6612608 : List Nat := [2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 6]
def baseStart_6612608 : Nat := 118140960795 + 6612608 * 2 ^ 59
def prefixEnd_6612608 : Nat := 4983230072969 + 3 ^ 40 * 6612608 * 2
def baseEnd_6612608 : Nat := 3395446283766169374489175

theorem tailTrace_6612608 : CollatzResearch.WordTrace tailWord_6612608 prefixEnd_6612608 3395446283766169374489175 := by
  unfold tailWord_6612608
  simp only [CollatzResearch.WordTrace]
  refine ⟨120590813813829017189939239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160787751751772022919918985 120590813813829017189939239)
  ·
    refine ⟨180886220720743525784908859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120590813813829017189939239 180886220720743525784908859)
    ·
      refine ⟨271329331081115288677363289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180886220720743525784908859 271329331081115288677363289)
      ·
        refine ⟨203496998310836466508022467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 271329331081115288677363289 203496998310836466508022467)
        ·
          refine ⟨305245497466254699762033701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203496998310836466508022467 305245497466254699762033701)
          ·
            refine ⟨57233530774922756205381319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 305245497466254699762033701 57233530774922756205381319)
            ·
              refine ⟨85850296162384134308071979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57233530774922756205381319 85850296162384134308071979)
              ·
                refine ⟨128775444243576201462107969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85850296162384134308071979 128775444243576201462107969)
                ·
                  refine ⟨96581583182682151096580977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 128775444243576201462107969 96581583182682151096580977)
                  ·
                    refine ⟨72436187387011613322435733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 96581583182682151096580977 72436187387011613322435733)
                    ·
                      refine ⟨3395446283766169374489175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72436187387011613322435733 3395446283766169374489175)
                      ·
                        rfl

theorem cell23_6612608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 6].length) (baseStart_6612608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6612608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6612608 prefixEnd_6612608 := by exact prefixLift 6612608
  have htrace : WordTrace (prefixWord ++ tailWord_6612608) baseStart_6612608 baseEnd_6612608 := by
    simpa [prefixWord, tailWord_6612608, baseEnd_6612608] using wordTrace_append hprefix tailTrace_6612608
  have hstable : (prefixWord ++ tailWord_6612608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6612608).length < 2 ^ (prefixWord ++ tailWord_6612608).sum := by decide
  have hdescent : baseEnd_6612608 < baseStart_6612608 := by decide
  rcases family_descends (prefixWord ++ tailWord_6612608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6612609 : List Nat := [1, 2, 4, 2, 1, 2, 4, 1, 2, 4]
def baseStart_6612609 : Nat := 118140960795 + 6612609 * 2 ^ 59
def prefixEnd_6612609 : Nat := 4983230072969 + 3 ^ 40 * 6612609 * 2
def baseEnd_6612609 : Nat := 1131815599082274623525557

theorem tailTrace_6612609 : CollatzResearch.WordTrace tailWord_6612609 prefixEnd_6612609 1131815599082274623525557 := by
  unfold tailWord_6612609
  simp only [CollatzResearch.WordTrace]
  refine ⟨241181664100654411550664881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160787776067102941033776587 241181664100654411550664881)
  ·
    refine ⟨180886248075490808662998661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241181664100654411550664881 180886248075490808662998661)
    ·
      refine ⟨33916171514154526624312249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 180886248075490808662998661 33916171514154526624312249)
      ·
        refine ⟨25437128635615894968234187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33916171514154526624312249 25437128635615894968234187)
        ·
          refine ⟨38155692953423842452351281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25437128635615894968234187 38155692953423842452351281)
          ·
            refine ⟨28616769715067881839263461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38155692953423842452351281 28616769715067881839263461)
            ·
              refine ⟨5365644321575227844861899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28616769715067881839263461 5365644321575227844861899)
              ·
                refine ⟨8048466482362841767292849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5365644321575227844861899 8048466482362841767292849)
                ·
                  refine ⟨6036349861772131325469637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8048466482362841767292849 6036349861772131325469637)
                  ·
                    refine ⟨1131815599082274623525557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6036349861772131325469637 1131815599082274623525557)
                    ·
                      rfl

theorem cell23_6612609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 4, 1, 2, 4].length) (baseStart_6612609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6612609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6612609 prefixEnd_6612609 := by exact prefixLift 6612609
  have htrace : WordTrace (prefixWord ++ tailWord_6612609) baseStart_6612609 baseEnd_6612609 := by
    simpa [prefixWord, tailWord_6612609, baseEnd_6612609] using wordTrace_append hprefix tailTrace_6612609
  have hstable : (prefixWord ++ tailWord_6612609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6612609).length < 2 ^ (prefixWord ++ tailWord_6612609).sum := by decide
  have hdescent : baseEnd_6612609 < baseStart_6612609 := by decide
  rcases family_descends (prefixWord ++ tailWord_6612609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6612616 : List Nat := [2, 1, 3, 5, 1, 2, 1, 2, 1, 1, 4]
def baseStart_6612616 : Nat := 118140960795 + 6612616 * 2 ^ 59
def prefixEnd_6612616 : Nat := 4983230072969 + 3 ^ 40 * 6612616 * 2
def baseEnd_6612616 : Nat := 3395450391611405343189139

theorem tailTrace_6612616 : CollatzResearch.WordTrace tailWord_6612616 prefixEnd_6612616 3395450391611405343189139 := by
  unfold tailWord_6612616
  simp only [CollatzResearch.WordTrace]
  refine ⟨120590959705814525873084851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160787946274419367830779801 120590959705814525873084851)
  ·
    refine ⟨180886439558721788809627277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120590959705814525873084851 180886439558721788809627277)
    ·
      refine ⟨67832414834520670803610229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180886439558721788809627277 67832414834520670803610229)
      ·
        refine ⟨6359288890736312887838459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 67832414834520670803610229 6359288890736312887838459)
        ·
          refine ⟨9538933336104469331757689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6359288890736312887838459 9538933336104469331757689)
          ·
            refine ⟨7154200002078351998818267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9538933336104469331757689 7154200002078351998818267)
            ·
              refine ⟨10731300003117527998227401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7154200002078351998818267 10731300003117527998227401)
              ·
                refine ⟨8048475002338145998670551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10731300003117527998227401 8048475002338145998670551)
                ·
                  refine ⟨12072712503507218998005827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8048475002338145998670551 12072712503507218998005827)
                  ·
                    refine ⟨18109068755260828497008741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12072712503507218998005827 18109068755260828497008741)
                    ·
                      refine ⟨3395450391611405343189139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18109068755260828497008741 3395450391611405343189139)
                      ·
                        rfl

theorem cell23_6612616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_6612616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6612616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6612616 prefixEnd_6612616 := by exact prefixLift 6612616
  have htrace : WordTrace (prefixWord ++ tailWord_6612616) baseStart_6612616 baseEnd_6612616 := by
    simpa [prefixWord, tailWord_6612616, baseEnd_6612616] using wordTrace_append hprefix tailTrace_6612616
  have hstable : (prefixWord ++ tailWord_6612616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6612616).length < 2 ^ (prefixWord ++ tailWord_6612616).sum := by decide
  have hdescent : baseEnd_6612616 < baseStart_6612616 := by decide
  rcases family_descends (prefixWord ++ tailWord_6612616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6612632 : List Nat := [2, 1, 2, 4, 1, 3, 1, 2, 1, 3, 3]
def baseStart_6612632 : Nat := 118140960795 + 6612632 * 2 ^ 59
def prefixEnd_6612632 : Nat := 4983230072969 + 3 ^ 40 * 6612632 * 2
def baseEnd_6612632 : Nat := 3395458607301877280589065

theorem tailTrace_6612632 : CollatzResearch.WordTrace tailWord_6612632 prefixEnd_6612632 3395458607301877280589065 := by
  unfold tailWord_6612632
  simp only [CollatzResearch.WordTrace]
  refine ⟨120591251489785543239376075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160788335319714057652501433 120591251489785543239376075)
  ·
    refine ⟨180886877234678314859064113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120591251489785543239376075 180886877234678314859064113)
    ·
      refine ⟨135665157926008736144298085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180886877234678314859064113 135665157926008736144298085)
      ·
        refine ⟨25437217111126638027055891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 135665157926008736144298085 25437217111126638027055891)
        ·
          refine ⟨38155825666689957040583837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25437217111126638027055891 38155825666689957040583837)
          ·
            refine ⟨14308434625008733890218939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38155825666689957040583837 14308434625008733890218939)
            ·
              refine ⟨21462651937513100835328409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14308434625008733890218939 21462651937513100835328409)
              ·
                refine ⟨16096988953134825626496307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21462651937513100835328409 16096988953134825626496307)
                ·
                  refine ⟨24145483429702238439744461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16096988953134825626496307 24145483429702238439744461)
                  ·
                    refine ⟨9054556286138339414904173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24145483429702238439744461 9054556286138339414904173)
                    ·
                      refine ⟨3395458607301877280589065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9054556286138339414904173 3395458607301877280589065)
                      ·
                        rfl

theorem cell23_6612632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 2, 1, 3, 3].length) (baseStart_6612632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6612632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6612632 prefixEnd_6612632 := by exact prefixLift 6612632
  have htrace : WordTrace (prefixWord ++ tailWord_6612632) baseStart_6612632 baseEnd_6612632 := by
    simpa [prefixWord, tailWord_6612632, baseEnd_6612632] using wordTrace_append hprefix tailTrace_6612632
  have hstable : (prefixWord ++ tailWord_6612632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6612632).length < 2 ^ (prefixWord ++ tailWord_6612632).sum := by decide
  have hdescent : baseEnd_6612632 < baseStart_6612632 := by decide
  rcases family_descends (prefixWord ++ tailWord_6612632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6612636 : List Nat := [2, 2, 3, 2, 3, 1, 3, 1, 1, 2, 3]
def baseStart_6612636 : Nat := 118140960795 + 6612636 * 2 ^ 59
def prefixEnd_6612636 : Nat := 4983230072969 + 3 ^ 40 * 6612636 * 2
def baseEnd_6612636 : Nat := 3395460661224495264939047

theorem tailTrace_6612636 : CollatzResearch.WordTrace tailWord_6612636 prefixEnd_6612636 3395460661224495264939047 := by
  unfold tailWord_6612636
  simp only [CollatzResearch.WordTrace]
  refine ⟨120591324435778297580948881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160788432581037730107931841 120591324435778297580948881)
  ·
    refine ⟨90443493326833723185711661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120591324435778297580948881 90443493326833723185711661)
    ·
      refine ⟨33916309997562646194641873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90443493326833723185711661 33916309997562646194641873)
      ·
        refine ⟨25437232498171984645981405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33916309997562646194641873 25437232498171984645981405)
        ·
          refine ⟨9538962186814494242243027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25437232498171984645981405 9538962186814494242243027)
          ·
            refine ⟨14308443280221741363364541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9538962186814494242243027 14308443280221741363364541)
            ·
              refine ⟨5365666230083153011261703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14308443280221741363364541 5365666230083153011261703)
              ·
                refine ⟨8048499345124729516892555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5365666230083153011261703 8048499345124729516892555)
                ·
                  refine ⟨12072749017687094275338833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8048499345124729516892555 12072749017687094275338833)
                  ·
                    refine ⟨9054561763265320706504125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12072749017687094275338833 9054561763265320706504125)
                    ·
                      refine ⟨3395460661224495264939047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9054561763265320706504125 3395460661224495264939047)
                      ·
                        rfl

theorem cell23_6612636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 3, 1, 1, 2, 3].length) (baseStart_6612636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6612636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6612636 prefixEnd_6612636 := by exact prefixLift 6612636
  have htrace : WordTrace (prefixWord ++ tailWord_6612636) baseStart_6612636 baseEnd_6612636 := by
    simpa [prefixWord, tailWord_6612636, baseEnd_6612636] using wordTrace_append hprefix tailTrace_6612636
  have hstable : (prefixWord ++ tailWord_6612636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6612636).length < 2 ^ (prefixWord ++ tailWord_6612636).sum := by decide
  have hdescent : baseEnd_6612636 < baseStart_6612636 := by decide
  rcases family_descends (prefixWord ++ tailWord_6612636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6612700 : List Nat := [2, 2, 5, 1, 3, 1, 1, 2, 2, 1, 3]
def baseStart_6612700 : Nat := 118140960795 + 6612700 * 2 ^ 59
def prefixEnd_6612700 : Nat := 4983230072969 + 3 ^ 40 * 6612700 * 2
def baseEnd_6612700 : Nat := 3395493523986383014538753

theorem tailTrace_6612700 : CollatzResearch.WordTrace tailWord_6612700 prefixEnd_6612700 3395493523986383014538753 := by
  unfold tailWord_6612700
  simp only [CollatzResearch.WordTrace]
  refine ⟨120592491571662367046113777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160789988762216489394818369 120592491571662367046113777)
  ·
    refine ⟨90444368678746775284585333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120592491571662367046113777 90444368678746775284585333)
    ·
      refine ⟨8479159563632510182929875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 90444368678746775284585333 8479159563632510182929875)
      ·
        refine ⟨12718739345448765274394813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8479159563632510182929875 12718739345448765274394813)
        ·
          refine ⟨4769527254543286977898055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12718739345448765274394813 4769527254543286977898055)
          ·
            refine ⟨7154290881814930466847083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4769527254543286977898055 7154290881814930466847083)
            ·
              refine ⟨10731436322722395700270625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7154290881814930466847083 10731436322722395700270625)
              ·
                refine ⟨8048577242041796775202969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10731436322722395700270625 8048577242041796775202969)
                ·
                  refine ⟨6036432931531347581402227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8048577242041796775202969 6036432931531347581402227)
                  ·
                    refine ⟨9054649397297021372103341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6036432931531347581402227 9054649397297021372103341)
                    ·
                      refine ⟨3395493523986383014538753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9054649397297021372103341 3395493523986383014538753)
                      ·
                        rfl

theorem cell23_6612700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 1, 2, 2, 1, 3].length) (baseStart_6612700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6612700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6612700 prefixEnd_6612700 := by exact prefixLift 6612700
  have htrace : WordTrace (prefixWord ++ tailWord_6612700) baseStart_6612700 baseEnd_6612700 := by
    simpa [prefixWord, tailWord_6612700, baseEnd_6612700] using wordTrace_append hprefix tailTrace_6612700
  have hstable : (prefixWord ++ tailWord_6612700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6612700).length < 2 ^ (prefixWord ++ tailWord_6612700).sum := by decide
  have hdescent : baseEnd_6612700 < baseStart_6612700 := by decide
  rcases family_descends (prefixWord ++ tailWord_6612700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6612712 : List Nat := [2, 1, 4, 1, 3, 2, 2, 1, 7]
def baseStart_6612712 : Nat := 118140960795 + 6612712 * 2 ^ 59
def prefixEnd_6612712 : Nat := 4983230072969 + 3 ^ 40 * 6612712 * 2
def baseEnd_6612712 : Nat := 377277742861581885287633

theorem tailTrace_6612712 : CollatzResearch.WordTrace tailWord_6612712 prefixEnd_6612712 377277742861581885287633 := by
  unfold tailWord_6612712
  simp only [CollatzResearch.WordTrace]
  refine ⟨120592710409640630070832195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160790280546187506761109593 120592710409640630070832195)
  ·
    refine ⟨180889065614460945106248293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120592710409640630070832195 180889065614460945106248293)
    ·
      refine ⟨33916699802711427207421555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 180889065614460945106248293 33916699802711427207421555)
      ·
        refine ⟨50875049704067140811132333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33916699802711427207421555 50875049704067140811132333)
        ·
          refine ⟨19078143639025177804174625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50875049704067140811132333 19078143639025177804174625)
          ·
            refine ⟨14308607729268883353130969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19078143639025177804174625 14308607729268883353130969)
            ·
              refine ⟨10731455796951662514848227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14308607729268883353130969 10731455796951662514848227)
              ·
                refine ⟨16097183695427493772272341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10731455796951662514848227 16097183695427493772272341)
                ·
                  refine ⟨377277742861581885287633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16097183695427493772272341 377277742861581885287633)
                  ·
                    rfl

theorem cell23_6612712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 2, 1, 7].length) (baseStart_6612712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6612712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6612712 prefixEnd_6612712 := by exact prefixLift 6612712
  have htrace : WordTrace (prefixWord ++ tailWord_6612712) baseStart_6612712 baseEnd_6612712 := by
    simpa [prefixWord, tailWord_6612712, baseEnd_6612712] using wordTrace_append hprefix tailTrace_6612712
  have hstable : (prefixWord ++ tailWord_6612712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6612712).length < 2 ^ (prefixWord ++ tailWord_6612712).sum := by decide
  have hdescent : baseEnd_6612712 < baseStart_6612712 := by decide
  rcases family_descends (prefixWord ++ tailWord_6612712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6612722 : List Nat := [3, 2, 1, 3, 1, 1, 1, 3, 2, 3, 3]
def baseStart_6612722 : Nat := 118140960795 + 6612722 * 2 ^ 59
def prefixEnd_6612722 : Nat := 4983230072969 + 3 ^ 40 * 6612722 * 2
def baseEnd_6612722 : Nat := 3395504820560781928463651

theorem tailTrace_6612722 : CollatzResearch.WordTrace tailWord_6612722 prefixEnd_6612722 3395504820560781928463651 := by
  unfold tailWord_6612722
  simp only [CollatzResearch.WordTrace]
  refine ⟨60296446387311257962382105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160790523699496687899685613 60296446387311257962382105)
  ·
    refine ⟨45222334790483443471786579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60296446387311257962382105 45222334790483443471786579)
    ·
      refine ⟨67833502185725165207679869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45222334790483443471786579 67833502185725165207679869)
      ·
        refine ⟨25437563319646936952879951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67833502185725165207679869 25437563319646936952879951)
        ·
          refine ⟨38156344979470405429319927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25437563319646936952879951 38156344979470405429319927)
          ·
            refine ⟨57234517469205608143979891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38156344979470405429319927 57234517469205608143979891)
            ·
              refine ⟨85851776203808412215969837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57234517469205608143979891 85851776203808412215969837)
              ·
                refine ⟨32194416076428154580988689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85851776203808412215969837 32194416076428154580988689)
                ·
                  refine ⟨24145812057321115935741517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32194416076428154580988689 24145812057321115935741517)
                  ·
                    refine ⟨9054679521495418475903069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24145812057321115935741517 9054679521495418475903069)
                    ·
                      refine ⟨3395504820560781928463651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9054679521495418475903069 3395504820560781928463651)
                      ·
                        rfl

theorem cell23_6612722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 3, 2, 3, 3].length) (baseStart_6612722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6612722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6612722 prefixEnd_6612722 := by exact prefixLift 6612722
  have htrace : WordTrace (prefixWord ++ tailWord_6612722) baseStart_6612722 baseEnd_6612722 := by
    simpa [prefixWord, tailWord_6612722, baseEnd_6612722] using wordTrace_append hprefix tailTrace_6612722
  have hstable : (prefixWord ++ tailWord_6612722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6612722).length < 2 ^ (prefixWord ++ tailWord_6612722).sum := by decide
  have hdescent : baseEnd_6612722 < baseStart_6612722 := by decide
  rcases family_descends (prefixWord ++ tailWord_6612722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6612762 : List Nat := [3, 1, 1, 3, 2, 2, 1, 1, 4, 1, 4]
def baseStart_6612762 : Nat := 118140960795 + 6612762 * 2 ^ 59
def prefixEnd_6612762 : Nat := 4983230072969 + 3 ^ 40 * 6612762 * 2
def baseEnd_6612762 : Nat := 3395525359786961771963467

theorem tailTrace_6612762 : CollatzResearch.WordTrace tailWord_6612762 prefixEnd_6612762 3395525359786961771963467 := by
  unfold tailWord_6612762
  simp only [CollatzResearch.WordTrace]
  refine ⟨60296811117275029670246135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160791496312733412453989693 60296811117275029670246135)
  ·
    refine ⟨90445216675912544505369203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60296811117275029670246135 90445216675912544505369203)
    ·
      refine ⟨135667825013868816758053805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90445216675912544505369203 135667825013868816758053805)
      ·
        refine ⟨50875434380200806284270177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135667825013868816758053805 50875434380200806284270177)
        ·
          refine ⟨38156575785150604713202633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50875434380200806284270177 38156575785150604713202633)
          ·
            refine ⟨28617431838862953534901975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38156575785150604713202633 28617431838862953534901975)
            ·
              refine ⟨42926147758294430302352963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28617431838862953534901975 42926147758294430302352963)
              ·
                refine ⟨64389221637441645453529445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42926147758294430302352963 64389221637441645453529445)
                ·
                  refine ⟨12072979057020308522536771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64389221637441645453529445 12072979057020308522536771)
                  ·
                    refine ⟨18109468585530462783805157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12072979057020308522536771 18109468585530462783805157)
                    ·
                      refine ⟨3395525359786961771963467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18109468585530462783805157 3395525359786961771963467)
                      ·
                        rfl

theorem cell23_6612762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 1, 4, 1, 4].length) (baseStart_6612762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6612762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6612762 prefixEnd_6612762 := by exact prefixLift 6612762
  have htrace : WordTrace (prefixWord ++ tailWord_6612762) baseStart_6612762 baseEnd_6612762 := by
    simpa [prefixWord, tailWord_6612762, baseEnd_6612762] using wordTrace_append hprefix tailTrace_6612762
  have hstable : (prefixWord ++ tailWord_6612762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6612762).length < 2 ^ (prefixWord ++ tailWord_6612762).sum := by decide
  have hdescent : baseEnd_6612762 < baseStart_6612762 := by decide
  rcases family_descends (prefixWord ++ tailWord_6612762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6612832 : List Nat := [2, 1, 1, 3, 3, 2, 1, 2, 3, 5]
def baseStart_6612832 : Nat := 118140960795 + 6612832 * 2 ^ 59
def prefixEnd_6612832 : Nat := 4983230072969 + 3 ^ 40 * 6612832 * 2
def baseEnd_6612832 : Nat := 1131853767810925499362715

theorem tailTrace_6612832 : CollatzResearch.WordTrace tailWord_6612832 prefixEnd_6612832 1131853767810925499362715 := by
  unfold tailWord_6612832
  simp only [CollatzResearch.WordTrace]
  refine ⟨120594898789423260318016375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160793198385897680424021833 120594898789423260318016375)
  ·
    refine ⟨180892348184134890477024563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120594898789423260318016375 180892348184134890477024563)
    ·
      refine ⟨271338522276202335715536845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180892348184134890477024563 271338522276202335715536845)
      ·
        refine ⟨101751945853575875893326317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 271338522276202335715536845 101751945853575875893326317)
        ·
          refine ⟨38156979695090953459997369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101751945853575875893326317 38156979695090953459997369)
          ·
            refine ⟨28617734771318215094998027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38156979695090953459997369 28617734771318215094998027)
            ·
              refine ⟨42926602156977322642497041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28617734771318215094998027 42926602156977322642497041)
              ·
                refine ⟨32194951617732991981872781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42926602156977322642497041 32194951617732991981872781)
                ·
                  refine ⟨12073106856649871993202293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32194951617732991981872781 12073106856649871993202293)
                  ·
                    refine ⟨1131853767810925499362715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12073106856649871993202293 1131853767810925499362715)
                    ·
                      rfl

theorem cell23_6612832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 2, 3, 5].length) (baseStart_6612832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6612832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6612832 prefixEnd_6612832 := by exact prefixLift 6612832
  have htrace : WordTrace (prefixWord ++ tailWord_6612832) baseStart_6612832 baseEnd_6612832 := by
    simpa [prefixWord, tailWord_6612832, baseEnd_6612832] using wordTrace_append hprefix tailTrace_6612832
  have hstable : (prefixWord ++ tailWord_6612832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6612832).length < 2 ^ (prefixWord ++ tailWord_6612832).sum := by decide
  have hdescent : baseEnd_6612832 < baseStart_6612832 := by decide
  rcases family_descends (prefixWord ++ tailWord_6612832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6612839 : List Nat := [1, 1, 5, 1, 2, 1, 2, 2, 1, 5, 2]
def baseStart_6612839 : Nat := 118140960795 + 6612839 * 2 ^ 59
def prefixEnd_6612839 : Nat := 4983230072969 + 3 ^ 40 * 6612839 * 2
def baseEnd_6612839 : Nat := 3395564897797357970700613

theorem tailTrace_6612839 : CollatzResearch.WordTrace tailWord_6612839 prefixEnd_6612839 3395564897797357970700613 := by
  unfold tailWord_6612839
  simp only [CollatzResearch.WordTrace]
  refine ⟨241190052889821160831537571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160793368593214107221025047 241190052889821160831537571)
  ·
    refine ⟨361785079334731741247306357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241190052889821160831537571 361785079334731741247306357)
    ·
      refine ⟨33917351187631100741934971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 361785079334731741247306357 33917351187631100741934971)
      ·
        refine ⟨50876026781446651112902457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33917351187631100741934971 50876026781446651112902457)
        ·
          refine ⟨38157020086084988334676843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50876026781446651112902457 38157020086084988334676843)
          ·
            refine ⟨57235530129127482502015265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38157020086084988334676843 57235530129127482502015265)
            ·
              refine ⟨42926647596845611876511449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57235530129127482502015265 42926647596845611876511449)
              ·
                refine ⟨32194985697634208907383587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42926647596845611876511449 32194985697634208907383587)
                ·
                  refine ⟨48292478546451313361075381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32194985697634208907383587 48292478546451313361075381)
                  ·
                    refine ⟨4527419863729810627600817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48292478546451313361075381 4527419863729810627600817)
                    ·
                      refine ⟨3395564897797357970700613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4527419863729810627600817 3395564897797357970700613)
                      ·
                        rfl

theorem cell23_6612839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 2, 1, 5, 2].length) (baseStart_6612839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6612839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6612839 prefixEnd_6612839 := by exact prefixLift 6612839
  have htrace : WordTrace (prefixWord ++ tailWord_6612839) baseStart_6612839 baseEnd_6612839 := by
    simpa [prefixWord, tailWord_6612839, baseEnd_6612839] using wordTrace_append hprefix tailTrace_6612839
  have hstable : (prefixWord ++ tailWord_6612839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6612839).length < 2 ^ (prefixWord ++ tailWord_6612839).sum := by decide
  have hdescent : baseEnd_6612839 < baseStart_6612839 := by decide
  rcases family_descends (prefixWord ++ tailWord_6612839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6612846 : List Nat := [4, 1, 2, 3, 1, 1, 1, 1, 5, 1, 3]
def baseStart_6612846 : Nat := 118140960795 + 6612846 * 2 ^ 59
def prefixEnd_6612846 : Nat := 4983230072969 + 3 ^ 40 * 6612846 * 2
def baseEnd_6612846 : Nat := 3395568492161939443313081

theorem tailTrace_6612846 : CollatzResearch.WordTrace tailWord_6612846 prefixEnd_6612846 3395568492161939443313081 := by
  unfold tailWord_6612846
  simp only [CollatzResearch.WordTrace]
  refine ⟨30148788525099475128380299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 160793538800530534018028261 30148788525099475128380299)
  ·
    refine ⟨45223182787649212692570449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30148788525099475128380299 45223182787649212692570449)
    ·
      refine ⟨33917387090736909519427837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45223182787649212692570449 33917387090736909519427837)
      ·
        refine ⟨12719020159026341069785439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33917387090736909519427837 12719020159026341069785439)
        ·
          refine ⟨19078530238539511604678159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12719020159026341069785439 19078530238539511604678159)
          ·
            refine ⟨28617795357809267407017239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19078530238539511604678159 28617795357809267407017239)
            ·
              refine ⟨42926693036713901110525859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28617795357809267407017239 42926693036713901110525859)
              ·
                refine ⟨64390039555070851665788789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42926693036713901110525859 64390039555070851665788789)
                ·
                  refine ⟨6036566208287892343667699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 64390039555070851665788789 6036566208287892343667699)
                  ·
                    refine ⟨9054849312431838515501549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6036566208287892343667699 9054849312431838515501549)
                    ·
                      refine ⟨3395568492161939443313081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9054849312431838515501549 3395568492161939443313081)
                      ·
                        rfl

theorem cell23_6612846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_6612846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6612846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6612846 prefixEnd_6612846 := by exact prefixLift 6612846
  have htrace : WordTrace (prefixWord ++ tailWord_6612846) baseStart_6612846 baseEnd_6612846 := by
    simpa [prefixWord, tailWord_6612846, baseEnd_6612846] using wordTrace_append hprefix tailTrace_6612846
  have hstable : (prefixWord ++ tailWord_6612846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6612846).length < 2 ^ (prefixWord ++ tailWord_6612846).sum := by decide
  have hdescent : baseEnd_6612846 < baseStart_6612846 := by decide
  rcases family_descends (prefixWord ++ tailWord_6612846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6612869 : List Nat := [1, 3, 1, 1, 3, 2, 3, 3, 1, 1, 4]
def baseStart_6612869 : Nat := 118140960795 + 6612869 * 2 ^ 59
def prefixEnd_6612869 : Nat := 4983230072969 + 3 ^ 40 * 6612869 * 2
def baseEnd_6612869 : Nat := 3395580302216992853325475

theorem tailTrace_6612869 : CollatzResearch.WordTrace tailWord_6612869 prefixEnd_6612869 3395580302216992853325475 := by
  unfold tailWord_6612869
  simp only [CollatzResearch.WordTrace]
  refine ⟨241191147079712475955129661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160794098053141650636753107 241191147079712475955129661)
  ·
    refine ⟨90446680154892178483173623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 241191147079712475955129661 90446680154892178483173623)
    ·
      refine ⟨135670020232338267724760435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90446680154892178483173623 135670020232338267724760435)
      ·
        refine ⟨203505030348507401587140653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135670020232338267724760435 203505030348507401587140653)
        ·
          refine ⟨76314386380690275595177745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 203505030348507401587140653 76314386380690275595177745)
          ·
            refine ⟨57235789785517706696383309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76314386380690275595177745 57235789785517706696383309)
            ·
              refine ⟨21463421169569140011143741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57235789785517706696383309 21463421169569140011143741)
              ·
                refine ⟨8048782938588427504178903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21463421169569140011143741 8048782938588427504178903)
                ·
                  refine ⟨12073174407882641256268355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8048782938588427504178903 12073174407882641256268355)
                  ·
                    refine ⟨18109761611823961884402533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12073174407882641256268355 18109761611823961884402533)
                    ·
                      refine ⟨3395580302216992853325475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18109761611823961884402533 3395580302216992853325475)
                      ·
                        rfl

theorem cell23_6612869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 3, 1, 1, 4].length) (baseStart_6612869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6612869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6612869 prefixEnd_6612869 := by exact prefixLift 6612869
  have htrace : WordTrace (prefixWord ++ tailWord_6612869) baseStart_6612869 baseEnd_6612869 := by
    simpa [prefixWord, tailWord_6612869, baseEnd_6612869] using wordTrace_append hprefix tailTrace_6612869
  have hstable : (prefixWord ++ tailWord_6612869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6612869).length < 2 ^ (prefixWord ++ tailWord_6612869).sum := by decide
  have hdescent : baseEnd_6612869 < baseStart_6612869 := by decide
  rcases family_descends (prefixWord ++ tailWord_6612869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6612903 : List Nat := [1, 1, 6, 1, 2, 1, 2, 2, 3, 2, 2]
def baseStart_6612903 : Nat := 118140960795 + 6612903 * 2 ^ 59
def prefixEnd_6612903 : Nat := 4983230072969 + 3 ^ 40 * 6612903 * 2
def baseEnd_6612903 : Nat := 3395597760559245720300319

theorem tailTrace_6612903 : CollatzResearch.WordTrace tailWord_6612903 prefixEnd_6612903 3395597760559245720300319 := by
  unfold tailWord_6612903
  simp only [CollatzResearch.WordTrace]
  refine ⟨241192387161589299761867363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160794924774392866507911575 241192387161589299761867363)
  ·
    refine ⟨361788580742383949642801045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241192387161589299761867363 361788580742383949642801045)
    ·
      refine ⟨16958839722299247639506299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 361788580742383949642801045 16958839722299247639506299)
      ·
        refine ⟨25438259583448871459259449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16958839722299247639506299 25438259583448871459259449)
        ·
          refine ⟨19078694687586653594444587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25438259583448871459259449 19078694687586653594444587)
          ·
            refine ⟨28618042031379980391666881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19078694687586653594444587 28618042031379980391666881)
            ·
              refine ⟨21463531523534985293750161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28618042031379980391666881 21463531523534985293750161)
              ·
                refine ⟨16097648642651238970312621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21463531523534985293750161 16097648642651238970312621)
                ·
                  refine ⟨6036618240994214613867233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16097648642651238970312621 6036618240994214613867233)
                  ·
                    refine ⟨4527463680745660960400425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6036618240994214613867233 4527463680745660960400425)
                    ·
                      refine ⟨3395597760559245720300319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4527463680745660960400425 3395597760559245720300319)
                      ·
                        rfl

theorem cell23_6612903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 2, 2, 3, 2, 2].length) (baseStart_6612903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6612903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6612903 prefixEnd_6612903 := by exact prefixLift 6612903
  have htrace : WordTrace (prefixWord ++ tailWord_6612903) baseStart_6612903 baseEnd_6612903 := by
    simpa [prefixWord, tailWord_6612903, baseEnd_6612903] using wordTrace_append hprefix tailTrace_6612903
  have hstable : (prefixWord ++ tailWord_6612903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6612903).length < 2 ^ (prefixWord ++ tailWord_6612903).sum := by decide
  have hdescent : baseEnd_6612903 < baseStart_6612903 := by decide
  rcases family_descends (prefixWord ++ tailWord_6612903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6612936 : List Nat := [2, 1, 3, 1, 4, 1, 2, 1, 4, 1, 3]
def baseStart_6612936 : Nat := 118140960795 + 6612936 * 2 ^ 59
def prefixEnd_6612936 : Nat := 4983230072969 + 3 ^ 40 * 6612936 * 2
def baseEnd_6612936 : Nat := 3395614705420844091187667

theorem tailTrace_6612936 : CollatzResearch.WordTrace tailWord_6612936 prefixEnd_6612936 3395614705420844091187667 := by
  unfold tailWord_6612936
  simp only [CollatzResearch.WordTrace]
  refine ⟨120596795385234873198909331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160795727180313164265212441 120596795385234873198909331)
  ·
    refine ⟨180895193077852309798363997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120596795385234873198909331 180895193077852309798363997)
    ·
      refine ⟨67835697404194616174386499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180895193077852309798363997 67835697404194616174386499)
      ·
        refine ⟨101753546106291924261579749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67835697404194616174386499 101753546106291924261579749)
        ·
          refine ⟨19078789894929735799046203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 101753546106291924261579749 19078789894929735799046203)
          ·
            refine ⟨28618184842394603698569305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19078789894929735799046203 28618184842394603698569305)
            ·
              refine ⟨21463638631795952773926979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28618184842394603698569305 21463638631795952773926979)
              ·
                refine ⟨32195457947693929160890469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21463638631795952773926979 32195457947693929160890469)
                ·
                  refine ⟨6036648365192611717666963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32195457947693929160890469 6036648365192611717666963)
                  ·
                    refine ⟨9054972547788917576500445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6036648365192611717666963 9054972547788917576500445)
                    ·
                      refine ⟨3395614705420844091187667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9054972547788917576500445 3395614705420844091187667)
                      ·
                        rfl

theorem cell23_6612936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 1, 4, 1, 3].length) (baseStart_6612936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6612936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6612936 prefixEnd_6612936 := by exact prefixLift 6612936
  have htrace : WordTrace (prefixWord ++ tailWord_6612936) baseStart_6612936 baseEnd_6612936 := by
    simpa [prefixWord, tailWord_6612936, baseEnd_6612936] using wordTrace_append hprefix tailTrace_6612936
  have hstable : (prefixWord ++ tailWord_6612936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6612936).length < 2 ^ (prefixWord ++ tailWord_6612936).sum := by decide
  have hdescent : baseEnd_6612936 < baseStart_6612936 := by decide
  rcases family_descends (prefixWord ++ tailWord_6612936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6612952 : List Nat := [2, 1, 2, 2, 2, 2, 2, 1, 1, 8]
def baseStart_6612952 : Nat := 118140960795 + 6612952 * 2 ^ 59
def prefixEnd_6612952 : Nat := 4983230072969 + 3 ^ 40 * 6612952 * 2
def baseEnd_6612952 : Nat := 1131874307037105342862531

theorem tailTrace_6612952 : CollatzResearch.WordTrace tailWord_6612952 prefixEnd_6612952 1131874307037105342862531 := by
  unfold tailWord_6612952
  simp only [CollatzResearch.WordTrace]
  refine ⟨120597087169205890565200555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160796116225607854086934073 120597087169205890565200555)
  ·
    refine ⟨180895630753808835847800833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120597087169205890565200555 180895630753808835847800833)
    ·
      refine ⟨135671723065356626885850625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180895630753808835847800833 135671723065356626885850625)
      ·
        refine ⟨101753792299017470164387969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135671723065356626885850625 101753792299017470164387969)
        ·
          refine ⟨76315344224263102623290977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101753792299017470164387969 76315344224263102623290977)
          ·
            refine ⟨57236508168197326967468233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76315344224263102623290977 57236508168197326967468233)
            ·
              refine ⟨42927381126147995225601175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57236508168197326967468233 42927381126147995225601175)
              ·
                refine ⟨64391071689221992838401763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42927381126147995225601175 64391071689221992838401763)
                ·
                  refine ⟨96586607533832989257602645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64391071689221992838401763 96586607533832989257602645)
                  ·
                    refine ⟨1131874307037105342862531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 96586607533832989257602645 1131874307037105342862531)
                    ·
                      rfl

theorem cell23_6612952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 1, 1, 8].length) (baseStart_6612952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6612952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6612952 prefixEnd_6612952 := by exact prefixLift 6612952
  have htrace : WordTrace (prefixWord ++ tailWord_6612952) baseStart_6612952 baseEnd_6612952 := by
    simpa [prefixWord, tailWord_6612952, baseEnd_6612952] using wordTrace_append hprefix tailTrace_6612952
  have hstable : (prefixWord ++ tailWord_6612952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6612952).length < 2 ^ (prefixWord ++ tailWord_6612952).sum := by decide
  have hdescent : baseEnd_6612952 < baseStart_6612952 := by decide
  rcases family_descends (prefixWord ++ tailWord_6612952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6612953 : List Nat := [1, 2, 1, 2, 6, 1, 1, 3, 2, 1, 3]
def baseStart_6612953 : Nat := 118140960795 + 6612953 * 2 ^ 59
def prefixEnd_6612953 : Nat := 4983230072969 + 3 ^ 40 * 6612953 * 2
def baseEnd_6612953 : Nat := 3395623434591970524675089

theorem tailTrace_6612953 : CollatzResearch.WordTrace tailWord_6612953 prefixEnd_6612953 3395623434591970524675089 := by
  unfold tailWord_6612953
  simp only [CollatzResearch.WordTrace]
  refine ⟨241194210811408158301187513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160796140540938772200791675 241194210811408158301187513)
  ·
    refine ⟨180895658108556118725890635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241194210811408158301187513 180895658108556118725890635)
    ·
      refine ⟨271343487162834178088835953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180895658108556118725890635 271343487162834178088835953)
      ·
        refine ⟨203507615372125633566626965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 271343487162834178088835953 203507615372125633566626965)
        ·
          refine ⟨9539419470568389073435639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 203507615372125633566626965 9539419470568389073435639)
          ·
            refine ⟨14309129205852583610153459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9539419470568389073435639 14309129205852583610153459)
            ·
              refine ⟨21463693808778875415230189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14309129205852583610153459 21463693808778875415230189)
              ·
                refine ⟨8048885178292078280711321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21463693808778875415230189 8048885178292078280711321)
                ·
                  refine ⟨6036663883719058710533491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8048885178292078280711321 6036663883719058710533491)
                  ·
                    refine ⟨9054995825578588065800237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6036663883719058710533491 9054995825578588065800237)
                    ·
                      refine ⟨3395623434591970524675089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9054995825578588065800237 3395623434591970524675089)
                      ·
                        rfl

theorem cell23_6612953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 3, 2, 1, 3].length) (baseStart_6612953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6612953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6612953 prefixEnd_6612953 := by exact prefixLift 6612953
  have htrace : WordTrace (prefixWord ++ tailWord_6612953) baseStart_6612953 baseEnd_6612953 := by
    simpa [prefixWord, tailWord_6612953, baseEnd_6612953] using wordTrace_append hprefix tailTrace_6612953
  have hstable : (prefixWord ++ tailWord_6612953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6612953).length < 2 ^ (prefixWord ++ tailWord_6612953).sum := by decide
  have hdescent : baseEnd_6612953 < baseStart_6612953 := by decide
  rcases family_descends (prefixWord ++ tailWord_6612953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6612963 : List Nat := [1, 1, 1, 6, 1, 2, 3, 2, 1, 3, 2]
def baseStart_6612963 : Nat := 118140960795 + 6612963 * 2 ^ 59
def prefixEnd_6612963 : Nat := 4983230072969 + 3 ^ 40 * 6612963 * 2
def baseEnd_6612963 : Nat := 3395628569398515485550043

theorem tailTrace_6612963 : CollatzResearch.WordTrace tailWord_6612963 prefixEnd_6612963 3395628569398515485550043 := by
  unfold tailWord_6612963
  simp only [CollatzResearch.WordTrace]
  refine ⟨241194575541371930009051543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160796383694247953339367695 241194575541371930009051543)
  ·
    refine ⟨361791863312057895013577315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241194575541371930009051543 361791863312057895013577315)
    ·
      refine ⟨542687794968086842520365973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 361791863312057895013577315 542687794968086842520365973)
      ·
        refine ⟨25438490389129070743142155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 542687794968086842520365973 25438490389129070743142155)
        ·
          refine ⟨38157735583693606114713233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25438490389129070743142155 38157735583693606114713233)
          ·
            refine ⟨28618301687770204586034925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38157735583693606114713233 28618301687770204586034925)
            ·
              refine ⟨10731863132913826719763097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28618301687770204586034925 10731863132913826719763097)
              ·
                refine ⟨8048897349685370039822323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10731863132913826719763097 8048897349685370039822323)
                ·
                  refine ⟨12073346024528055059733485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8048897349685370039822323 12073346024528055059733485)
                  ·
                    refine ⟨4527504759198020647400057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12073346024528055059733485 4527504759198020647400057)
                    ·
                      refine ⟨3395628569398515485550043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4527504759198020647400057 3395628569398515485550043)
                      ·
                        rfl

theorem cell23_6612963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 3, 2, 1, 3, 2].length) (baseStart_6612963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6612963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6612963 prefixEnd_6612963 := by exact prefixLift 6612963
  have htrace : WordTrace (prefixWord ++ tailWord_6612963) baseStart_6612963 baseEnd_6612963 := by
    simpa [prefixWord, tailWord_6612963, baseEnd_6612963] using wordTrace_append hprefix tailTrace_6612963
  have hstable : (prefixWord ++ tailWord_6612963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6612963).length < 2 ^ (prefixWord ++ tailWord_6612963).sum := by decide
  have hdescent : baseEnd_6612963 < baseStart_6612963 := by decide
  rcases family_descends (prefixWord ++ tailWord_6612963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6612976 : List Nat := [2, 1, 1, 1, 3, 2, 2, 1, 6, 2, 2]
def baseStart_6612976 : Nat := 118140960795 + 6612976 * 2 ^ 59
def prefixEnd_6612976 : Nat := 4983230072969 + 3 ^ 40 * 6612976 * 2
def baseEnd_6612976 : Nat := 3395635244647023934687483

theorem tailTrace_6612976 : CollatzResearch.WordTrace tailWord_6612976 prefixEnd_6612976 3395635244647023934687483 := by
  unfold tailWord_6612976
  simp only [CollatzResearch.WordTrace]
  refine ⟨120597524845162416614637391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160796699793549888819516521 120597524845162416614637391)
  ·
    refine ⟨180896287267743624921956087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120597524845162416614637391 180896287267743624921956087)
    ·
      refine ⟨271344430901615437382934131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180896287267743624921956087 271344430901615437382934131)
      ·
        refine ⟨407016646352423156074401197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271344430901615437382934131 407016646352423156074401197)
        ·
          refine ⟨152631242382158683527900449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 407016646352423156074401197 152631242382158683527900449)
          ·
            refine ⟨114473431786619012645925337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152631242382158683527900449 114473431786619012645925337)
            ·
              refine ⟨85855073839964259484444003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114473431786619012645925337 85855073839964259484444003)
              ·
                refine ⟨128782610759946389226666005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85855073839964259484444003 128782610759946389226666005)
                ·
                  refine ⟨6036684879372486994999969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 128782610759946389226666005 6036684879372486994999969)
                  ·
                    refine ⟨4527513659529365246249977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6036684879372486994999969 4527513659529365246249977)
                    ·
                      refine ⟨3395635244647023934687483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4527513659529365246249977 3395635244647023934687483)
                      ·
                        rfl

theorem cell23_6612976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 6, 2, 2].length) (baseStart_6612976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6612976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6612976 prefixEnd_6612976 := by exact prefixLift 6612976
  have htrace : WordTrace (prefixWord ++ tailWord_6612976) baseStart_6612976 baseEnd_6612976 := by
    simpa [prefixWord, tailWord_6612976, baseEnd_6612976] using wordTrace_append hprefix tailTrace_6612976
  have hstable : (prefixWord ++ tailWord_6612976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6612976).length < 2 ^ (prefixWord ++ tailWord_6612976).sum := by decide
  have hdescent : baseEnd_6612976 < baseStart_6612976 := by decide
  rcases family_descends (prefixWord ++ tailWord_6612976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6613029 : List Nat := [1, 3, 1, 2, 2, 4, 1, 1, 1, 7]
def baseStart_6613029 : Nat := 118140960795 + 6613029 * 2 ^ 59
def prefixEnd_6613029 : Nat := 4983230072969 + 3 ^ 40 * 6613029 * 2
def baseEnd_6613029 : Nat := 1131887486373904075774913

theorem tailTrace_6613029 : CollatzResearch.WordTrace tailWord_6613029 prefixEnd_6613029 1131887486373904075774913 := by
  unfold tailWord_6613029
  simp only [CollatzResearch.WordTrace]
  refine ⟨241196982759132823280954141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160797988506088548853969427 241196982759132823280954141)
  ·
    refine ⟨90448868534674808730357803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 241196982759132823280954141 90448868534674808730357803)
    ·
      refine ⟨135673302802012213095536705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90448868534674808730357803 135673302802012213095536705)
      ·
        refine ⟨101754977101509159821652529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135673302802012213095536705 101754977101509159821652529)
        ·
          refine ⟨76316232826131869866239397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101754977101509159821652529 76316232826131869866239397)
          ·
            refine ⟨14309293654899725599919887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76316232826131869866239397 14309293654899725599919887)
            ·
              refine ⟨21463940482349588399879831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14309293654899725599919887 21463940482349588399879831)
              ·
                refine ⟨32195910723524382599819747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21463940482349588399879831 32195910723524382599819747)
                ·
                  refine ⟨48293866085286573899729621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32195910723524382599819747 48293866085286573899729621)
                  ·
                    refine ⟨1131887486373904075774913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48293866085286573899729621 1131887486373904075774913)
                    ·
                      rfl

theorem cell23_6613029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 1, 1, 7].length) (baseStart_6613029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6613029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6613029 prefixEnd_6613029 := by exact prefixLift 6613029
  have htrace : WordTrace (prefixWord ++ tailWord_6613029) baseStart_6613029 baseEnd_6613029 := by
    simpa [prefixWord, tailWord_6613029, baseEnd_6613029] using wordTrace_append hprefix tailTrace_6613029
  have hstable : (prefixWord ++ tailWord_6613029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6613029).length < 2 ^ (prefixWord ++ tailWord_6613029).sum := by decide
  have hdescent : baseEnd_6613029 < baseStart_6613029 := by decide
  rcases family_descends (prefixWord ++ tailWord_6613029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6613044 : List Nat := [2, 5, 1, 2, 2, 2, 1, 2, 2, 2, 2]
def baseStart_6613044 : Nat := 118140960795 + 6613044 * 2 ^ 59
def prefixEnd_6613044 : Nat := 4983230072969 + 3 ^ 40 * 6613044 * 2
def baseEnd_6613044 : Nat := 3395670161331529668637171

theorem tailTrace_6613044 : CollatzResearch.WordTrace tailWord_6613044 prefixEnd_6613044 3395670161331529668637171 := by
  unfold tailWord_6613044
  simp only [CollatzResearch.WordTrace]
  refine ⟨120598764927039240421375093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160798353236052320561833457 120598764927039240421375093)
  ·
    refine ⟨11306134211909928789503915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 120598764927039240421375093 11306134211909928789503915)
    ·
      refine ⟨16959201317864893184255873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11306134211909928789503915 16959201317864893184255873)
      ·
        refine ⟨12719400988398669888191905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16959201317864893184255873 12719400988398669888191905)
        ·
          refine ⟨9539550741299002416143929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12719400988398669888191905 9539550741299002416143929)
          ·
            refine ⟨7154663055974251812107947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9539550741299002416143929 7154663055974251812107947)
            ·
              refine ⟨10731994583961377718161921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7154663055974251812107947 10731994583961377718161921)
              ·
                refine ⟨8048995937971033288621441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10731994583961377718161921 8048995937971033288621441)
                ·
                  refine ⟨6036746953478274966466081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8048995937971033288621441 6036746953478274966466081)
                  ·
                    refine ⟨4527560215108706224849561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6036746953478274966466081 4527560215108706224849561)
                    ·
                      refine ⟨3395670161331529668637171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4527560215108706224849561 3395670161331529668637171)
                      ·
                        rfl

theorem cell23_6613044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 1, 2, 2, 2, 2].length) (baseStart_6613044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6613044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6613044 prefixEnd_6613044 := by exact prefixLift 6613044
  have htrace : WordTrace (prefixWord ++ tailWord_6613044) baseStart_6613044 baseEnd_6613044 := by
    simpa [prefixWord, tailWord_6613044, baseEnd_6613044] using wordTrace_append hprefix tailTrace_6613044
  have hstable : (prefixWord ++ tailWord_6613044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6613044).length < 2 ^ (prefixWord ++ tailWord_6613044).sum := by decide
  have hdescent : baseEnd_6613044 < baseStart_6613044 := by decide
  rcases family_descends (prefixWord ++ tailWord_6613044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6613046 : List Nat := [5, 1, 2, 1, 1, 1, 2, 1, 4, 5]
def baseStart_6613046 : Nat := 118140960795 + 6613046 * 2 ^ 59
def prefixEnd_6613046 : Nat := 4983230072969 + 3 ^ 40 * 6613046 * 2
def baseEnd_6613046 : Nat := 1131890396097612886937387

theorem tailTrace_6613046 : CollatzResearch.WordTrace tailWord_6613046 prefixEnd_6613046 1131890396097612886937387 := by
  unfold tailWord_6613046
  simp only [CollatzResearch.WordTrace]
  refine ⟨15074850175004452199020187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 160798401866714156789548661 15074850175004452199020187)
  ·
    refine ⟨22612275262506678298530281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15074850175004452199020187 22612275262506678298530281)
    ·
      refine ⟨16959206446880008723897711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22612275262506678298530281 16959206446880008723897711)
      ·
        refine ⟨25438809670320013085846567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16959206446880008723897711 25438809670320013085846567)
        ·
          refine ⟨38158214505480019628769851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25438809670320013085846567 38158214505480019628769851)
          ·
            refine ⟨57237321758220029443154777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38158214505480019628769851 57237321758220029443154777)
            ·
              refine ⟨42927991318665022082366083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57237321758220029443154777 42927991318665022082366083)
              ·
                refine ⟨64391986977997533123549125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42927991318665022082366083 64391986977997533123549125)
                ·
                  refine ⟨12073497558374537460665461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64391986977997533123549125 12073497558374537460665461)
                  ·
                    refine ⟨1131890396097612886937387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12073497558374537460665461 1131890396097612886937387)
                    ·
                      rfl

theorem cell23_6613046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 1, 4, 5].length) (baseStart_6613046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6613046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6613046 prefixEnd_6613046 := by exact prefixLift 6613046
  have htrace : WordTrace (prefixWord ++ tailWord_6613046) baseStart_6613046 baseEnd_6613046 := by
    simpa [prefixWord, tailWord_6613046, baseEnd_6613046] using wordTrace_append hprefix tailTrace_6613046
  have hstable : (prefixWord ++ tailWord_6613046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6613046).length < 2 ^ (prefixWord ++ tailWord_6613046).sum := by decide
  have hdescent : baseEnd_6613046 < baseStart_6613046 := by decide
  rcases family_descends (prefixWord ++ tailWord_6613046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6613110 : List Nat := [5, 1, 1, 2, 1, 4, 1, 1, 3, 4]
def baseStart_6613110 : Nat := 118140960795 + 6613110 * 2 ^ 59
def prefixEnd_6613110 : Nat := 4983230072969 + 3 ^ 40 * 6613110 * 2
def baseEnd_6613110 : Nat := 1131901350351575470137289

theorem tailTrace_6613110 : CollatzResearch.WordTrace tailWord_6613110 prefixEnd_6613110 1131901350351575470137289 := by
  unfold tailWord_6613110
  simp only [CollatzResearch.WordTrace]
  refine ⟨15074996066989960882165799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 160799958047892916076435189 15074996066989960882165799)
  ·
    refine ⟨22612494100484941323248699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15074996066989960882165799 22612494100484941323248699)
    ·
      refine ⟨33918741150727411984873049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22612494100484941323248699 33918741150727411984873049)
      ·
        refine ⟨25439055863045558988654787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33918741150727411984873049 25439055863045558988654787)
        ·
          refine ⟨38158583794568338482982181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25439055863045558988654787 38158583794568338482982181)
          ·
            refine ⟨7154734461481563465559159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38158583794568338482982181 7154734461481563465559159)
            ·
              refine ⟨10732101692222345198338739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7154734461481563465559159 10732101692222345198338739)
              ·
                refine ⟨16098152538333517797508109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10732101692222345198338739 16098152538333517797508109)
                ·
                  refine ⟨6036807201875069174065541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16098152538333517797508109 6036807201875069174065541)
                  ·
                    refine ⟨1131901350351575470137289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6036807201875069174065541 1131901350351575470137289)
                    ·
                      rfl

theorem cell23_6613110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 1, 1, 3, 4].length) (baseStart_6613110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6613110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6613110 prefixEnd_6613110 := by exact prefixLift 6613110
  have htrace : WordTrace (prefixWord ++ tailWord_6613110) baseStart_6613110 baseEnd_6613110 := by
    simpa [prefixWord, tailWord_6613110, baseEnd_6613110] using wordTrace_append hprefix tailTrace_6613110
  have hstable : (prefixWord ++ tailWord_6613110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6613110).length < 2 ^ (prefixWord ++ tailWord_6613110).sum := by decide
  have hdescent : baseEnd_6613110 < baseStart_6613110 := by decide
  rcases family_descends (prefixWord ++ tailWord_6613110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6613123 : List Nat := [1, 1, 1, 3, 3, 5, 2, 1, 6]
def baseStart_6613123 : Nat := 118140960795 + 6613123 * 2 ^ 59
def prefixEnd_6613123 : Nat := 4983230072969 + 3 ^ 40 * 6613123 * 2
def baseEnd_6613123 : Nat := 377301191811470539949923

theorem tailTrace_6613123 : CollatzResearch.WordTrace tailWord_6613123 prefixEnd_6613123 377301191811470539949923 := by
  unfold tailWord_6613123
  simp only [CollatzResearch.WordTrace]
  refine ⟨241200411220792277334876023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160800274147194851556584015 241200411220792277334876023)
  ·
    refine ⟨361800616831188416002314035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241200411220792277334876023 361800616831188416002314035)
    ·
      refine ⟨542700925246782624003471053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 361800616831188416002314035 542700925246782624003471053)
      ·
        refine ⟨203512846967543484001301645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 542700925246782624003471053 203512846967543484001301645)
        ·
          refine ⟨76317317612828806500488117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 203512846967543484001301645 76317317612828806500488117)
          ·
            refine ⟨7154748526202700609420761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 76317317612828806500488117 7154748526202700609420761)
            ·
              refine ⟨5366061394652025457065571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7154748526202700609420761 5366061394652025457065571)
              ·
                refine ⟨8049092091978038185598357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5366061394652025457065571 8049092091978038185598357)
                ·
                  refine ⟨377301191811470539949923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8049092091978038185598357 377301191811470539949923)
                  ·
                    rfl

theorem cell23_6613123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 2, 1, 6].length) (baseStart_6613123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6613123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6613123 prefixEnd_6613123 := by exact prefixLift 6613123
  have htrace : WordTrace (prefixWord ++ tailWord_6613123) baseStart_6613123 baseEnd_6613123 := by
    simpa [prefixWord, tailWord_6613123, baseEnd_6613123] using wordTrace_append hprefix tailTrace_6613123
  have hstable : (prefixWord ++ tailWord_6613123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6613123).length < 2 ^ (prefixWord ++ tailWord_6613123).sum := by decide
  have hdescent : baseEnd_6613123 < baseStart_6613123 := by decide
  rcases family_descends (prefixWord ++ tailWord_6613123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6613176 : List Nat := [2, 1, 2, 1, 2, 1, 3, 1, 5, 2, 3]
def baseStart_6613176 : Nat := 118140960795 + 6613176 * 2 ^ 59
def prefixEnd_6613176 : Nat := 4983230072969 + 3 ^ 40 * 6613176 * 2
def baseEnd_6613176 : Nat := 3395737940777923152186563

theorem tailTrace_6613176 : CollatzResearch.WordTrace tailWord_6613176 prefixEnd_6613176 3395737940777923152186563 := by
  unfold tailWord_6613176
  simp only [CollatzResearch.WordTrace]
  refine ⟨120601172144800133693277691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160801562859733511591036921 120601172144800133693277691)
  ·
    refine ⟨180901758217200200539916537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120601172144800133693277691 180901758217200200539916537)
    ·
      refine ⟨135676318662900150404937403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180901758217200200539916537 135676318662900150404937403)
      ·
        refine ⟨203514477994350225607406105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135676318662900150404937403 203514477994350225607406105)
        ·
          refine ⟨152635858495762669205554579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 203514477994350225607406105 152635858495762669205554579)
          ·
            refine ⟨228953787743644003808331869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152635858495762669205554579 228953787743644003808331869)
            ·
              refine ⟨85857670403866501428124451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 228953787743644003808331869 85857670403866501428124451)
              ·
                refine ⟨128786505605799752142186677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85857670403866501428124451 128786505605799752142186677)
                ·
                  refine ⟨12073734900543726763330001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 128786505605799752142186677 12073734900543726763330001)
                  ·
                    refine ⟨9055301175407795072497501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12073734900543726763330001 9055301175407795072497501)
                    ·
                      refine ⟨3395737940777923152186563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9055301175407795072497501 3395737940777923152186563)
                      ·
                        rfl

theorem cell23_6613176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 5, 2, 3].length) (baseStart_6613176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6613176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6613176 prefixEnd_6613176 := by exact prefixLift 6613176
  have htrace : WordTrace (prefixWord ++ tailWord_6613176) baseStart_6613176 baseEnd_6613176 := by
    simpa [prefixWord, tailWord_6613176, baseEnd_6613176] using wordTrace_append hprefix tailTrace_6613176
  have hstable : (prefixWord ++ tailWord_6613176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6613176).length < 2 ^ (prefixWord ++ tailWord_6613176).sum := by decide
  have hdescent : baseEnd_6613176 < baseStart_6613176 := by decide
  rcases family_descends (prefixWord ++ tailWord_6613176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6613210 : List Nat := [3, 1, 1, 2, 2, 1, 6, 1, 1, 2, 3]
def baseStart_6613210 : Nat := 118140960795 + 6613210 * 2 ^ 59
def prefixEnd_6613210 : Nat := 4983230072969 + 3 ^ 40 * 6613210 * 2
def baseEnd_6613210 : Nat := 3395755399120176019161407

theorem tailTrace_6613210 : CollatzResearch.WordTrace tailWord_6613210 prefixEnd_6613210 3395755399120176019161407 := by
  unfold tailWord_6613210
  simp only [CollatzResearch.WordTrace]
  refine ⟨60300896092869272798323271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160802389580984727462195389 60300896092869272798323271)
  ·
    refine ⟨90451344139303909197484907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60300896092869272798323271 90451344139303909197484907)
    ·
      refine ⟨135677016208955863796227361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90451344139303909197484907 135677016208955863796227361)
      ·
        refine ⟨101757762156716897847170521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135677016208955863796227361 101757762156716897847170521)
        ·
          refine ⟨76318321617537673385377891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101757762156716897847170521 76318321617537673385377891)
          ·
            refine ⟨114477482426306510078066837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76318321617537673385377891 114477482426306510078066837)
            ·
              refine ⟨5366131988733117659909383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 114477482426306510078066837 5366131988733117659909383)
              ·
                refine ⟨8049197983099676489864075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5366131988733117659909383 8049197983099676489864075)
                ·
                  refine ⟨12073796974649514734796113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8049197983099676489864075 12073796974649514734796113)
                  ·
                    refine ⟨9055347730987136051097085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12073796974649514734796113 9055347730987136051097085)
                    ·
                      refine ⟨3395755399120176019161407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9055347730987136051097085 3395755399120176019161407)
                      ·
                        rfl

theorem cell23_6613210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 6, 1, 1, 2, 3].length) (baseStart_6613210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6613210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6613210 prefixEnd_6613210 := by exact prefixLift 6613210
  have htrace : WordTrace (prefixWord ++ tailWord_6613210) baseStart_6613210 baseEnd_6613210 := by
    simpa [prefixWord, tailWord_6613210, baseEnd_6613210] using wordTrace_append hprefix tailTrace_6613210
  have hstable : (prefixWord ++ tailWord_6613210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6613210).length < 2 ^ (prefixWord ++ tailWord_6613210).sum := by decide
  have hdescent : baseEnd_6613210 < baseStart_6613210 := by decide
  rcases family_descends (prefixWord ++ tailWord_6613210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6613233 : List Nat := [1, 2, 2, 2, 2, 1, 2, 1, 5, 3, 2]
def baseStart_6613233 : Nat := 118140960795 + 6613233 * 2 ^ 59
def prefixEnd_6613233 : Nat := 4983230072969 + 3 ^ 40 * 6613233 * 2
def baseEnd_6613233 : Nat := 3395767209175229429173801

theorem tailTrace_6613233 : CollatzResearch.WordTrace tailWord_6613233 prefixEnd_6613233 3395767209175229429173801 := by
  unfold tailWord_6613233
  simp only [CollatzResearch.WordTrace]
  refine ⟨241204423250393766121380353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160802948833595844080920235 241204423250393766121380353)
  ·
    refine ⟨180903317437795324591035265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241204423250393766121380353 180903317437795324591035265)
    ·
      refine ⟨135677488078346493443276449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180903317437795324591035265 135677488078346493443276449)
      ·
        refine ⟨101758116058759870082457337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135677488078346493443276449 101758116058759870082457337)
        ·
          refine ⟨76318587044069902561843003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101758116058759870082457337 76318587044069902561843003)
          ·
            refine ⟨114477880566104853842764505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76318587044069902561843003 114477880566104853842764505)
            ·
              refine ⟨85858410424578640382073379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114477880566104853842764505 85858410424578640382073379)
              ·
                refine ⟨128787615636867960573110069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85858410424578640382073379 128787615636867960573110069)
                ·
                  refine ⟨12073838965956371303729069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 128787615636867960573110069 12073838965956371303729069)
                  ·
                    refine ⟨4527689612233639238898401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12073838965956371303729069 4527689612233639238898401)
                    ·
                      refine ⟨3395767209175229429173801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4527689612233639238898401 3395767209175229429173801)
                      ·
                        rfl

theorem cell23_6613233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 5, 3, 2].length) (baseStart_6613233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6613233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6613233 prefixEnd_6613233 := by exact prefixLift 6613233
  have htrace : WordTrace (prefixWord ++ tailWord_6613233) baseStart_6613233 baseEnd_6613233 := by
    simpa [prefixWord, tailWord_6613233, baseEnd_6613233] using wordTrace_append hprefix tailTrace_6613233
  have hstable : (prefixWord ++ tailWord_6613233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6613233).length < 2 ^ (prefixWord ++ tailWord_6613233).sum := by decide
  have hdescent : baseEnd_6613233 < baseStart_6613233 := by decide
  rcases family_descends (prefixWord ++ tailWord_6613233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6613263 : List Nat := [1, 1, 2, 1, 1, 1, 3, 6, 1, 4, 2]
def baseStart_6613263 : Nat := 118140960795 + 6613263 * 2 ^ 59
def prefixEnd_6613263 : Nat := 4983230072969 + 3 ^ 40 * 6613263 * 2
def baseEnd_6613263 : Nat := 3395782613594864311798663

theorem tailTrace_6613263 : CollatzResearch.WordTrace tailWord_6613263 prefixEnd_6613263 3395782613594864311798663 := by
  unfold tailWord_6613263
  simp only [CollatzResearch.WordTrace]
  refine ⟨241205517440285081244972443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160803678293523387496648295 241205517440285081244972443)
  ·
    refine ⟨361808276160427621867458665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241205517440285081244972443 361808276160427621867458665)
    ·
      refine ⟨271356207120320716400593999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 361808276160427621867458665 271356207120320716400593999)
      ·
        refine ⟨407034310680481074600890999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271356207120320716400593999 407034310680481074600890999)
        ·
          refine ⟨610551466020721611901336499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 407034310680481074600890999 610551466020721611901336499)
          ·
            refine ⟨915827199031082417852004749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 610551466020721611901336499 915827199031082417852004749)
            ·
              refine ⟨343435199636655906694501781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 915827199031082417852004749 343435199636655906694501781)
              ·
                refine ⟨16098524982968245626304771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 343435199636655906694501781 16098524982968245626304771)
                ·
                  refine ⟨24147787474452368439457157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16098524982968245626304771 24147787474452368439457157)
                  ·
                    refine ⟨4527710151459819082398217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24147787474452368439457157 4527710151459819082398217)
                    ·
                      refine ⟨3395782613594864311798663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4527710151459819082398217 3395782613594864311798663)
                      ·
                        rfl

theorem cell23_6613263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 6, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 6, 1, 4, 2].length) (baseStart_6613263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6613263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6613263 prefixEnd_6613263 := by exact prefixLift 6613263
  have htrace : WordTrace (prefixWord ++ tailWord_6613263) baseStart_6613263 baseEnd_6613263 := by
    simpa [prefixWord, tailWord_6613263, baseEnd_6613263] using wordTrace_append hprefix tailTrace_6613263
  have hstable : (prefixWord ++ tailWord_6613263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6613263).length < 2 ^ (prefixWord ++ tailWord_6613263).sum := by decide
  have hdescent : baseEnd_6613263 < baseStart_6613263 := by decide
  rcases family_descends (prefixWord ++ tailWord_6613263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6613363 : List Nat := [1, 1, 1, 2, 2, 1, 2, 6, 3, 4]
def baseStart_6613363 : Nat := 118140960795 + 6613363 * 2 ^ 59
def prefixEnd_6613363 : Nat := 4983230072969 + 3 ^ 40 * 6613363 * 2
def baseEnd_6613363 : Nat := 1131944653886771306849401

theorem tailTrace_6613363 : CollatzResearch.WordTrace tailWord_6613363 prefixEnd_6613363 1131944653886771306849401 := by
  unfold tailWord_6613363
  simp only [CollatzResearch.WordTrace]
  refine ⟨241209164739922798323612743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160806109826615198882408495 241209164739922798323612743)
  ·
    refine ⟨361813747109884197485419115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241209164739922798323612743 361813747109884197485419115)
    ·
      refine ⟨542720620664826296228128673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 361813747109884197485419115 542720620664826296228128673)
      ·
        refine ⟨407040465498619722171096505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 542720620664826296228128673 407040465498619722171096505)
        ·
          refine ⟨305280349123964791628322379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 407040465498619722171096505 305280349123964791628322379)
          ·
            refine ⟨457920523685947187442483569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 305280349123964791628322379 457920523685947187442483569)
            ·
              refine ⟨343440392764460390581862677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 457920523685947187442483569 343440392764460390581862677)
              ·
                refine ⟨16098768410834080808524813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 343440392764460390581862677 16098768410834080808524813)
                ·
                  refine ⟨6037038154062780303196805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16098768410834080808524813 6037038154062780303196805)
                  ·
                    refine ⟨1131944653886771306849401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6037038154062780303196805 1131944653886771306849401)
                    ·
                      rfl

theorem cell23_6613363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 6, 3, 4].length) (baseStart_6613363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6613363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6613363 prefixEnd_6613363 := by exact prefixLift 6613363
  have htrace : WordTrace (prefixWord ++ tailWord_6613363) baseStart_6613363 baseEnd_6613363 := by
    simpa [prefixWord, tailWord_6613363, baseEnd_6613363] using wordTrace_append hprefix tailTrace_6613363
  have hstable : (prefixWord ++ tailWord_6613363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6613363).length < 2 ^ (prefixWord ++ tailWord_6613363).sum := by decide
  have hdescent : baseEnd_6613363 < baseStart_6613363 := by decide
  rcases family_descends (prefixWord ++ tailWord_6613363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6613441 : List Nat := [1, 2, 7, 1, 1, 1, 1, 2, 2, 2, 3]
def baseStart_6613441 : Nat := 118140960795 + 6613441 * 2 ^ 59
def prefixEnd_6613441 : Nat := 4983230072969 + 3 ^ 40 * 6613441 * 2
def baseEnd_6613441 : Nat := 3395874013151364615372845

theorem tailTrace_6613441 : CollatzResearch.WordTrace tailWord_6613441 prefixEnd_6613441 3395874013151364615372845 := by
  unfold tailWord_6613441
  simp only [CollatzResearch.WordTrace]
  refine ⟨241212009633640217644952177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160808006422426811763301451 241212009633640217644952177)
  ·
    refine ⟨180909007225230163233714133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241212009633640217644952177 180909007225230163233714133)
    ·
      refine ⟨4240054856841331950790175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 180909007225230163233714133 4240054856841331950790175)
      ·
        refine ⟨6360082285261997926185263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4240054856841331950790175 6360082285261997926185263)
        ·
          refine ⟨9540123427892996889277895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6360082285261997926185263 9540123427892996889277895)
          ·
            refine ⟨14310185141839495333916843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9540123427892996889277895 14310185141839495333916843)
            ·
              refine ⟨21465277712759243000875265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14310185141839495333916843 21465277712759243000875265)
              ·
                refine ⟨16098958284569432250656449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21465277712759243000875265 16098958284569432250656449)
                ·
                  refine ⟨12074218713427074187992337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16098958284569432250656449 12074218713427074187992337)
                  ·
                    refine ⟨9055664035070305640994253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12074218713427074187992337 9055664035070305640994253)
                    ·
                      refine ⟨3395874013151364615372845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9055664035070305640994253 3395874013151364615372845)
                      ·
                        rfl

theorem cell23_6613441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_6613441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6613441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6613441 prefixEnd_6613441 := by exact prefixLift 6613441
  have htrace : WordTrace (prefixWord ++ tailWord_6613441) baseStart_6613441 baseEnd_6613441 := by
    simpa [prefixWord, tailWord_6613441, baseEnd_6613441] using wordTrace_append hprefix tailTrace_6613441
  have hstable : (prefixWord ++ tailWord_6613441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6613441).length < 2 ^ (prefixWord ++ tailWord_6613441).sum := by decide
  have hdescent : baseEnd_6613441 < baseStart_6613441 := by decide
  rcases family_descends (prefixWord ++ tailWord_6613441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6613443 : List Nat := [1, 1, 1, 3, 1, 1, 3, 2, 5, 1, 4]
def baseStart_6613443 : Nat := 118140960795 + 6613443 * 2 ^ 59
def prefixEnd_6613443 : Nat := 4983230072969 + 3 ^ 40 * 6613443 * 2
def baseEnd_6613443 : Nat := 3395875040112673607547835

theorem tailTrace_6613443 : CollatzResearch.WordTrace tailWord_6613443 prefixEnd_6613443 3395875040112673607547835 := by
  unfold tailWord_6613443
  simp only [CollatzResearch.WordTrace]
  refine ⟨241212082579632971986524983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160808055053088647991016655 241212082579632971986524983)
  ·
    refine ⟨361818123869449457979787475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241212082579632971986524983 361818123869449457979787475)
    ·
      refine ⟨542727185804174186969681213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 361818123869449457979787475 542727185804174186969681213)
      ·
        refine ⟨203522694676565320113630455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 542727185804174186969681213 203522694676565320113630455)
        ·
          refine ⟨305284042014847980170445683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203522694676565320113630455 305284042014847980170445683)
          ·
            refine ⟨457926063022271970255668525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 305284042014847980170445683 457926063022271970255668525)
            ·
              refine ⟨171722273633351988845875697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 457926063022271970255668525 171722273633351988845875697)
              ·
                refine ⟨128791705225013991634406773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 171722273633351988845875697 128791705225013991634406773)
                ·
                  refine ⟨12074222364845061715725635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 128791705225013991634406773 12074222364845061715725635)
                  ·
                    refine ⟨18111333547267592573588453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12074222364845061715725635 18111333547267592573588453)
                    ·
                      refine ⟨3395875040112673607547835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18111333547267592573588453 3395875040112673607547835)
                      ·
                        rfl

theorem cell23_6613443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 2, 5, 1, 4].length) (baseStart_6613443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6613443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6613443 prefixEnd_6613443 := by exact prefixLift 6613443
  have htrace : WordTrace (prefixWord ++ tailWord_6613443) baseStart_6613443 baseEnd_6613443 := by
    simpa [prefixWord, tailWord_6613443, baseEnd_6613443] using wordTrace_append hprefix tailTrace_6613443
  have hstable : (prefixWord ++ tailWord_6613443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6613443).length < 2 ^ (prefixWord ++ tailWord_6613443).sum := by decide
  have hdescent : baseEnd_6613443 < baseStart_6613443 := by decide
  rcases family_descends (prefixWord ++ tailWord_6613443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6613447 : List Nat := [1, 1, 4, 1, 1, 5, 1, 2, 2, 3, 2]
def baseStart_6613447 : Nat := 118140960795 + 6613447 * 2 ^ 59
def prefixEnd_6613447 : Nat := 4983230072969 + 3 ^ 40 * 6613447 * 2
def baseEnd_6613447 : Nat := 3395877094035291591897817

theorem tailTrace_6613447 : CollatzResearch.WordTrace tailWord_6613447 prefixEnd_6613447 3395877094035291591897817 := by
  unfold tailWord_6613447
  simp only [CollatzResearch.WordTrace]
  refine ⟨241212228471618480669670595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160808152314412320446447063 241212228471618480669670595)
  ·
    refine ⟨361818342707427721004505893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241212228471618480669670595 361818342707427721004505893)
    ·
      refine ⟨67840939257642697688344855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 361818342707427721004505893 67840939257642697688344855)
      ·
        refine ⟨101761408886464046532517283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67840939257642697688344855 101761408886464046532517283)
        ·
          refine ⟨152642113329696069798775925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101761408886464046532517283 152642113329696069798775925)
          ·
            refine ⟨14310198124659006543635243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 152642113329696069798775925 14310198124659006543635243)
            ·
              refine ⟨21465297186988509815452865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14310198124659006543635243 21465297186988509815452865)
              ·
                refine ⟨16098972890241382361589649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21465297186988509815452865 16098972890241382361589649)
                ·
                  refine ⟨12074229667681036771192237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16098972890241382361589649 12074229667681036771192237)
                  ·
                    refine ⟨4527836125380388789197089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12074229667681036771192237 4527836125380388789197089)
                    ·
                      refine ⟨3395877094035291591897817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4527836125380388789197089 3395877094035291591897817)
                      ·
                        rfl

theorem cell23_6613447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 2, 2, 3, 2].length) (baseStart_6613447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6613447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6613447 prefixEnd_6613447 := by exact prefixLift 6613447
  have htrace : WordTrace (prefixWord ++ tailWord_6613447) baseStart_6613447 baseEnd_6613447 := by
    simpa [prefixWord, tailWord_6613447, baseEnd_6613447] using wordTrace_append hprefix tailTrace_6613447
  have hstable : (prefixWord ++ tailWord_6613447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6613447).length < 2 ^ (prefixWord ++ tailWord_6613447).sum := by decide
  have hdescent : baseEnd_6613447 < baseStart_6613447 := by decide
  rcases family_descends (prefixWord ++ tailWord_6613447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6613463 : List Nat := [1, 1, 3, 2, 1, 1, 1, 1, 1, 8, 3]
def baseStart_6613463 : Nat := 118140960795 + 6613463 * 2 ^ 59
def prefixEnd_6613463 : Nat := 4983230072969 + 3 ^ 40 * 6613463 * 2
def baseEnd_6613463 : Nat := 3395885309725763529297743

theorem tailTrace_6613463 : CollatzResearch.WordTrace tailWord_6613463 prefixEnd_6613463 3395885309725763529297743 := by
  unfold tailWord_6613463
  simp only [CollatzResearch.WordTrace]
  refine ⟨241212812039560515402253043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160808541359707010268168695 241212812039560515402253043)
  ·
    refine ⟨361819218059340773103379565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241212812039560515402253043 361819218059340773103379565)
    ·
      refine ⟨135682206772252789913767337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 361819218059340773103379565 135682206772252789913767337)
      ·
        refine ⟨101761655079189592435325503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135682206772252789913767337 101761655079189592435325503)
        ·
          refine ⟨152642482618784388652988255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101761655079189592435325503 152642482618784388652988255)
          ·
            refine ⟨228963723928176582979482383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152642482618784388652988255 228963723928176582979482383)
            ·
              refine ⟨343445585892264874469223575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 228963723928176582979482383 343445585892264874469223575)
              ·
                refine ⟨515168378838397311703835363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 343445585892264874469223575 515168378838397311703835363)
                ·
                  refine ⟨772752568257595967555753045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 515168378838397311703835363 772752568257595967555753045)
                  ·
                    refine ⟨9055694159268702744793981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 772752568257595967555753045 9055694159268702744793981)
                    ·
                      refine ⟨3395885309725763529297743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9055694159268702744793981 3395885309725763529297743)
                      ·
                        rfl

theorem cell23_6613463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 8, 3].length) (baseStart_6613463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6613463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6613463 prefixEnd_6613463 := by exact prefixLift 6613463
  have htrace : WordTrace (prefixWord ++ tailWord_6613463) baseStart_6613463 baseEnd_6613463 := by
    simpa [prefixWord, tailWord_6613463, baseEnd_6613463] using wordTrace_append hprefix tailTrace_6613463
  have hstable : (prefixWord ++ tailWord_6613463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6613463).length < 2 ^ (prefixWord ++ tailWord_6613463).sum := by decide
  have hdescent : baseEnd_6613463 < baseStart_6613463 := by decide
  rcases family_descends (prefixWord ++ tailWord_6613463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6613473 : List Nat := [1, 2, 3, 1, 2, 2, 1, 3, 1, 1, 6]
def baseStart_6613473 : Nat := 118140960795 + 6613473 * 2 ^ 59
def prefixEnd_6613473 : Nat := 4983230072969 + 3 ^ 40 * 6613473 * 2
def baseEnd_6613473 : Nat := 3395890444532308490172697

theorem tailTrace_6613473 : CollatzResearch.WordTrace tailWord_6613473 prefixEnd_6613473 3395890444532308490172697 := by
  unfold tailWord_6613473
  simp only [CollatzResearch.WordTrace]
  refine ⟨241213176769524287110117073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160808784513016191406744715 241213176769524287110117073)
  ·
    refine ⟨180909882577143215332587805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241213176769524287110117073 180909882577143215332587805)
    ·
      refine ⟨67841205966428705749720427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180909882577143215332587805 67841205966428705749720427)
      ·
        refine ⟨101761808949643058624580641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67841205966428705749720427 101761808949643058624580641)
        ·
          refine ⟨76321356712232293968435481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101761808949643058624580641 76321356712232293968435481)
          ·
            refine ⟨57241017534174220476326611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76321356712232293968435481 57241017534174220476326611)
            ·
              refine ⟨85861526301261330714489917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57241017534174220476326611 85861526301261330714489917)
              ·
                refine ⟨32198072362972999017933719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85861526301261330714489917 32198072362972999017933719)
                ·
                  refine ⟨48297108544459498526900579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32198072362972999017933719 48297108544459498526900579)
                  ·
                    refine ⟨72445662816689247790350869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48297108544459498526900579 72445662816689247790350869)
                    ·
                      refine ⟨3395890444532308490172697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72445662816689247790350869 3395890444532308490172697)
                      ·
                        rfl

theorem cell23_6613473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 3, 1, 1, 6].length) (baseStart_6613473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6613473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6613473 prefixEnd_6613473 := by exact prefixLift 6613473
  have htrace : WordTrace (prefixWord ++ tailWord_6613473) baseStart_6613473 baseEnd_6613473 := by
    simpa [prefixWord, tailWord_6613473, baseEnd_6613473] using wordTrace_append hprefix tailTrace_6613473
  have hstable : (prefixWord ++ tailWord_6613473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6613473).length < 2 ^ (prefixWord ++ tailWord_6613473).sum := by decide
  have hdescent : baseEnd_6613473 < baseStart_6613473 := by decide
  rcases family_descends (prefixWord ++ tailWord_6613473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6613474 : List Nat := [3, 3, 3, 2, 1, 1, 1, 1, 3, 5]
def baseStart_6613474 : Nat := 118140960795 + 6613474 * 2 ^ 59
def prefixEnd_6613474 : Nat := 4983230072969 + 3 ^ 40 * 6613474 * 2
def baseEnd_6613474 : Nat := 1131963652670987662086731

theorem tailTrace_6613474 : CollatzResearch.WordTrace tailWord_6613474 prefixEnd_6613474 1131963652670987662086731 := by
  unfold tailWord_6613474
  simp only [CollatzResearch.WordTrace]
  refine ⟨60303303310630166070225869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160808808828347109520602317 60303303310630166070225869)
  ·
    refine ⟨22613738741486312276334701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60303303310630166070225869 22613738741486312276334701)
    ·
      refine ⟨8480152028057367103625513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22613738741486312276334701 8480152028057367103625513)
      ·
        refine ⟨6360114021043025327719135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8480152028057367103625513 6360114021043025327719135)
        ·
          refine ⟨9540171031564537991578703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6360114021043025327719135 9540171031564537991578703)
          ·
            refine ⟨14310256547346806987368055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9540171031564537991578703 14310256547346806987368055)
            ·
              refine ⟨21465384821020210481052083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14310256547346806987368055 21465384821020210481052083)
              ·
                refine ⟨32198077231530315721578125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21465384821020210481052083 32198077231530315721578125)
                ·
                  refine ⟨12074278961823868395591797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32198077231530315721578125 12074278961823868395591797)
                  ·
                    refine ⟨1131963652670987662086731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12074278961823868395591797 1131963652670987662086731)
                    ·
                      rfl

theorem cell23_6613474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_6613474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6613474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6613474 prefixEnd_6613474 := by exact prefixLift 6613474
  have htrace : WordTrace (prefixWord ++ tailWord_6613474) baseStart_6613474 baseEnd_6613474 := by
    simpa [prefixWord, tailWord_6613474, baseEnd_6613474] using wordTrace_append hprefix tailTrace_6613474
  have hstable : (prefixWord ++ tailWord_6613474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6613474).length < 2 ^ (prefixWord ++ tailWord_6613474).sum := by decide
  have hdescent : baseEnd_6613474 < baseStart_6613474 := by decide
  rcases family_descends (prefixWord ++ tailWord_6613474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6613477 : List Nat := [1, 3, 1, 5, 2, 1, 1, 1, 3, 1, 4]
def baseStart_6613477 : Nat := 118140960795 + 6613477 * 2 ^ 59
def prefixEnd_6613477 : Nat := 4983230072969 + 3 ^ 40 * 6613477 * 2
def baseEnd_6613477 : Nat := 3395892498454926474522679

theorem tailTrace_6613477 : CollatzResearch.WordTrace tailWord_6613477 prefixEnd_6613477 3395892498454926474522679 := by
  unfold tailWord_6613477
  simp only [CollatzResearch.WordTrace]
  refine ⟨241213322661509795793262685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160808881774339863862175123 241213322661509795793262685)
  ·
    refine ⟨90454995998066173422473507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 241213322661509795793262685 90454995998066173422473507)
    ·
      refine ⟨135682493997099260133710261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90454995998066173422473507 135682493997099260133710261)
      ·
        refine ⟨12720233812228055637535337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 135682493997099260133710261 12720233812228055637535337)
        ·
          refine ⟨9540175359171041728151503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12720233812228055637535337 9540175359171041728151503)
          ·
            refine ⟨14310263038756562592227255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9540175359171041728151503 14310263038756562592227255)
            ·
              refine ⟨21465394558134843888340883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14310263038756562592227255 21465394558134843888340883)
              ·
                refine ⟨32198091837202265832511325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21465394558134843888340883 32198091837202265832511325)
                ·
                  refine ⟨12074284438950849687191747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32198091837202265832511325 12074284438950849687191747)
                  ·
                    refine ⟨18111426658426274530787621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12074284438950849687191747 18111426658426274530787621)
                    ·
                      refine ⟨3395892498454926474522679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18111426658426274530787621 3395892498454926474522679)
                      ·
                        rfl

theorem cell23_6613477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_6613477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6613477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6613477 prefixEnd_6613477 := by exact prefixLift 6613477
  have htrace : WordTrace (prefixWord ++ tailWord_6613477) baseStart_6613477 baseEnd_6613477 := by
    simpa [prefixWord, tailWord_6613477, baseEnd_6613477] using wordTrace_append hprefix tailTrace_6613477
  have hstable : (prefixWord ++ tailWord_6613477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6613477).length < 2 ^ (prefixWord ++ tailWord_6613477).sum := by decide
  have hdescent : baseEnd_6613477 < baseStart_6613477 := by decide
  rcases family_descends (prefixWord ++ tailWord_6613477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6613494 : List Nat := [5, 1, 1, 1, 2, 1, 5, 1, 1, 1, 4]
def baseStart_6613494 : Nat := 118140960795 + 6613494 * 2 ^ 59
def prefixEnd_6613494 : Nat := 4983230072969 + 3 ^ 40 * 6613494 * 2
def baseEnd_6613494 : Nat := 3395901227626052908010101

theorem tailTrace_6613494 : CollatzResearch.WordTrace tailWord_6613494 prefixEnd_6613494 3395901227626052908010101 := by
  unfold tailWord_6613494
  simp only [CollatzResearch.WordTrace]
  refine ⟨15075871418903012981039471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 160809295134965471797754357 15075871418903012981039471)
  ·
    refine ⟨22613807128354519471559207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15075871418903012981039471 22613807128354519471559207)
    ·
      refine ⟨33920710692531779207338811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22613807128354519471559207 33920710692531779207338811)
      ·
        refine ⟨50881066038797668811008217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33920710692531779207338811 50881066038797668811008217)
        ·
          refine ⟨38160799529098251608256163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50881066038797668811008217 38160799529098251608256163)
          ·
            refine ⟨57241199293647377412384245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38160799529098251608256163 57241199293647377412384245)
            ·
              refine ⟨5366362433779441632411023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57241199293647377412384245 5366362433779441632411023)
              ·
                refine ⟨8049543650669162448616535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5366362433779441632411023 8049543650669162448616535)
                ·
                  refine ⟨12074315476003743672924803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8049543650669162448616535 12074315476003743672924803)
                  ·
                    refine ⟨18111473214005615509387205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12074315476003743672924803 18111473214005615509387205)
                    ·
                      refine ⟨3395901227626052908010101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18111473214005615509387205 3395901227626052908010101)
                      ·
                        rfl

theorem cell23_6613494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 5, 1, 1, 1, 4].length) (baseStart_6613494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6613494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6613494 prefixEnd_6613494 := by exact prefixLift 6613494
  have htrace : WordTrace (prefixWord ++ tailWord_6613494) baseStart_6613494 baseEnd_6613494 := by
    simpa [prefixWord, tailWord_6613494, baseEnd_6613494] using wordTrace_append hprefix tailTrace_6613494
  have hstable : (prefixWord ++ tailWord_6613494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6613494).length < 2 ^ (prefixWord ++ tailWord_6613494).sum := by decide
  have hdescent : baseEnd_6613494 < baseStart_6613494 := by decide
  rcases family_descends (prefixWord ++ tailWord_6613494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6613524 : List Nat := [2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4]
def baseStart_6613524 : Nat := 118140960795 + 6613524 * 2 ^ 59
def prefixEnd_6613524 : Nat := 4983230072969 + 3 ^ 40 * 6613524 * 2
def baseEnd_6613524 : Nat := 3395916632045687790634963

theorem tailTrace_6613524 : CollatzResearch.WordTrace tailWord_6613524 prefixEnd_6613524 3395916632045687790634963 := by
  unfold tailWord_6613524
  simp only [CollatzResearch.WordTrace]
  refine ⟨120607518446169761410111813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160810024594893015213482417 120607518446169761410111813)
  ·
    refine ⟨22613909708656830264395965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 120607518446169761410111813 22613909708656830264395965)
    ·
      refine ⟨8480216140746311349148487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22613909708656830264395965 8480216140746311349148487)
      ·
        refine ⟨12720324211119467023722731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8480216140746311349148487 12720324211119467023722731)
        ·
          refine ⟨19080486316679200535584097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12720324211119467023722731 19080486316679200535584097)
          ·
            refine ⟨14310364737509400401688073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19080486316679200535584097 14310364737509400401688073)
            ·
              refine ⟨10732773553132050301266055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14310364737509400401688073 10732773553132050301266055)
              ·
                refine ⟨16099160329698075451899083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10732773553132050301266055 16099160329698075451899083)
                ·
                  refine ⟨24148740494547113177848625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16099160329698075451899083 24148740494547113177848625)
                  ·
                    refine ⟨18111555370910334883386469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24148740494547113177848625 18111555370910334883386469)
                    ·
                      refine ⟨3395916632045687790634963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18111555370910334883386469 3395916632045687790634963)
                      ·
                        rfl

theorem cell23_6613524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_6613524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6613524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6613524 prefixEnd_6613524 := by exact prefixLift 6613524
  have htrace : WordTrace (prefixWord ++ tailWord_6613524) baseStart_6613524 baseEnd_6613524 := by
    simpa [prefixWord, tailWord_6613524, baseEnd_6613524] using wordTrace_append hprefix tailTrace_6613524
  have hstable : (prefixWord ++ tailWord_6613524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6613524).length < 2 ^ (prefixWord ++ tailWord_6613524).sum := by decide
  have hdescent : baseEnd_6613524 < baseStart_6613524 := by decide
  rcases family_descends (prefixWord ++ tailWord_6613524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6613537 : List Nat := [1, 2, 3, 2, 2, 1, 1, 3, 3, 3, 2]
def baseStart_6613537 : Nat := 118140960795 + 6613537 * 2 ^ 59
def prefixEnd_6613537 : Nat := 4983230072969 + 3 ^ 40 * 6613537 * 2
def baseEnd_6613537 : Nat := 3395923307294196239772403

theorem tailTrace_6613537 : CollatzResearch.WordTrace tailWord_6613537 prefixEnd_6613537 3395923307294196239772403 := by
  unfold tailWord_6613537
  simp only [CollatzResearch.WordTrace]
  refine ⟨241215511041292426040446865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160810340694194950693631243 241215511041292426040446865)
  ·
    refine ⟨180911633280969319530335149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241215511041292426040446865 180911633280969319530335149)
    ·
      refine ⟨67841862480363494823875681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180911633280969319530335149 67841862480363494823875681)
      ·
        refine ⟨50881396860272621117906761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67841862480363494823875681 50881396860272621117906761)
        ·
          refine ⟨38161047645204465838430071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50881396860272621117906761 38161047645204465838430071)
          ·
            refine ⟨57241571467806698757645107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38161047645204465838430071 57241571467806698757645107)
            ·
              refine ⟨85862357201710048136467661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57241571467806698757645107 85862357201710048136467661)
              ·
                refine ⟨32198383950641268051175373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85862357201710048136467661 32198383950641268051175373)
                ·
                  refine ⟨12074393981490475519190765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32198383950641268051175373 12074393981490475519190765)
                  ·
                    refine ⟨4527897743058928319696537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12074393981490475519190765 4527897743058928319696537)
                    ·
                      refine ⟨3395923307294196239772403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4527897743058928319696537 3395923307294196239772403)
                      ·
                        rfl

theorem cell23_6613537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 3, 3, 3, 2].length) (baseStart_6613537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6613537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6613537 prefixEnd_6613537 := by exact prefixLift 6613537
  have htrace : WordTrace (prefixWord ++ tailWord_6613537) baseStart_6613537 baseEnd_6613537 := by
    simpa [prefixWord, tailWord_6613537, baseEnd_6613537] using wordTrace_append hprefix tailTrace_6613537
  have hstable : (prefixWord ++ tailWord_6613537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6613537).length < 2 ^ (prefixWord ++ tailWord_6613537).sum := by decide
  have hdescent : baseEnd_6613537 < baseStart_6613537 := by decide
  rcases family_descends (prefixWord ++ tailWord_6613537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6613580 : List Nat := [2, 2, 1, 3, 1, 2, 1, 3, 2, 2, 4]
def baseStart_6613580 : Nat := 118140960795 + 6613580 * 2 ^ 59
def prefixEnd_6613580 : Nat := 4983230072969 + 3 ^ 40 * 6613580 * 2
def baseEnd_6613580 : Nat := 3395945386962339571534705

theorem tailTrace_6613580 : CollatzResearch.WordTrace tailWord_6613580 prefixEnd_6613580 3395945386962339571534705 := by
  unfold tailWord_6613580
  simp only [CollatzResearch.WordTrace]
  refine ⟨120608539690068322192131097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160811386253424429589508129 120608539690068322192131097)
  ·
    refine ⟨90456404767551241644098323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120608539690068322192131097 90456404767551241644098323)
    ·
      refine ⟨135684607151326862466147485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90456404767551241644098323 135684607151326862466147485)
      ·
        refine ⟨50881727681747573424805307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135684607151326862466147485 50881727681747573424805307)
        ·
          refine ⟨76322591522621360137207961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50881727681747573424805307 76322591522621360137207961)
          ·
            refine ⟨57241943641966020102905971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76322591522621360137207961 57241943641966020102905971)
            ·
              refine ⟨85862915462949030154358957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57241943641966020102905971 85862915462949030154358957)
              ·
                refine ⟨32198593298605886307884609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85862915462949030154358957 32198593298605886307884609)
                ·
                  refine ⟨24148944973954414730913457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32198593298605886307884609 24148944973954414730913457)
                  ·
                    refine ⟨18111708730465811048185093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24148944973954414730913457 18111708730465811048185093)
                    ·
                      refine ⟨3395945386962339571534705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18111708730465811048185093 3395945386962339571534705)
                      ·
                        rfl

theorem cell23_6613580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 3, 2, 2, 4].length) (baseStart_6613580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6613580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6613580 prefixEnd_6613580 := by exact prefixLift 6613580
  have htrace : WordTrace (prefixWord ++ tailWord_6613580) baseStart_6613580 baseEnd_6613580 := by
    simpa [prefixWord, tailWord_6613580, baseEnd_6613580] using wordTrace_append hprefix tailTrace_6613580
  have hstable : (prefixWord ++ tailWord_6613580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6613580).length < 2 ^ (prefixWord ++ tailWord_6613580).sum := by decide
  have hdescent : baseEnd_6613580 < baseStart_6613580 := by decide
  rcases family_descends (prefixWord ++ tailWord_6613580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6613600 : List Nat := [2, 1, 1, 3, 2, 1, 2, 2, 1, 5, 3]
def baseStart_6613600 : Nat := 118140960795 + 6613600 * 2 ^ 59
def prefixEnd_6613600 : Nat := 4983230072969 + 3 ^ 40 * 6613600 * 2
def baseEnd_6613600 : Nat := 3395955656575429493284613

theorem tailTrace_6613600 : CollatzResearch.WordTrace tailWord_6613600 prefixEnd_6613600 3395955656575429493284613 := by
  unfold tailWord_6613600
  simp only [CollatzResearch.WordTrace]
  refine ⟨120608904420032093899995127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160811872560042791866660169 120608904420032093899995127)
  ·
    refine ⟨180913356630048140849992691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120608904420032093899995127 180913356630048140849992691)
    ·
      refine ⟨271370034945072211274989037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180913356630048140849992691 271370034945072211274989037)
      ·
        refine ⟨101763763104402079228120889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 271370034945072211274989037 101763763104402079228120889)
        ·
          refine ⟨76322822328301559421090667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101763763104402079228120889 76322822328301559421090667)
          ·
            refine ⟨114484233492452339131636001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76322822328301559421090667 114484233492452339131636001)
            ·
              refine ⟨85863175119339254348727001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114484233492452339131636001 85863175119339254348727001)
              ·
                refine ⟨64397381339504440761545251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85863175119339254348727001 64397381339504440761545251)
                ·
                  refine ⟨96596072009256661142317877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64397381339504440761545251 96596072009256661142317877)
                  ·
                    refine ⟨9055881750867811982092301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 96596072009256661142317877 9055881750867811982092301)
                    ·
                      refine ⟨3395955656575429493284613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9055881750867811982092301 3395955656575429493284613)
                      ·
                        rfl

theorem cell23_6613600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 2, 1, 5, 3].length) (baseStart_6613600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6613600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6613600 prefixEnd_6613600 := by exact prefixLift 6613600
  have htrace : WordTrace (prefixWord ++ tailWord_6613600) baseStart_6613600 baseEnd_6613600 := by
    simpa [prefixWord, tailWord_6613600, baseEnd_6613600] using wordTrace_append hprefix tailTrace_6613600
  have hstable : (prefixWord ++ tailWord_6613600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6613600).length < 2 ^ (prefixWord ++ tailWord_6613600).sum := by decide
  have hdescent : baseEnd_6613600 < baseStart_6613600 := by decide
  rcases family_descends (prefixWord ++ tailWord_6613600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6613657 : List Nat := [1, 2, 1, 2, 1, 2, 6, 1, 2, 1, 4]
def baseStart_6613657 : Nat := 118140960795 + 6613657 * 2 ^ 59
def prefixEnd_6613657 : Nat := 4983230072969 + 3 ^ 40 * 6613657 * 2
def baseEnd_6613657 : Nat := 3395984924972735770271851

theorem tailTrace_6613657 : CollatzResearch.WordTrace tailWord_6613657 prefixEnd_6613657 3395984924972735770271851 := by
  unfold tailWord_6613657
  simp only [CollatzResearch.WordTrace]
  refine ⟨241219887800857686534815225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160813258533905124356543483 241219887800857686534815225)
  ·
    refine ⟨180914915850643264901111419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241219887800857686534815225 180914915850643264901111419)
    ·
      refine ⟨271372373775964897351667129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180914915850643264901111419 271372373775964897351667129)
      ·
        refine ⟨203529280331973673013750347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 271372373775964897351667129 203529280331973673013750347)
        ·
          refine ⟨305293920497960509520625521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203529280331973673013750347 305293920497960509520625521)
          ·
            refine ⟨228970440373470382140469141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 305293920497960509520625521 228970440373470382140469141)
            ·
              refine ⟨10732989392506424162834491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 228970440373470382140469141 10732989392506424162834491)
              ·
                refine ⟨16099484088759636244251737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10732989392506424162834491 16099484088759636244251737)
                ·
                  refine ⟨12074613066569727183188803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16099484088759636244251737 12074613066569727183188803)
                  ·
                    refine ⟨18111919599854590774783205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12074613066569727183188803 18111919599854590774783205)
                    ·
                      refine ⟨3395984924972735770271851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18111919599854590774783205 3395984924972735770271851)
                      ·
                        rfl

theorem cell23_6613657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 6, 1, 2, 1, 4].length) (baseStart_6613657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6613657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6613657 prefixEnd_6613657 := by exact prefixLift 6613657
  have htrace : WordTrace (prefixWord ++ tailWord_6613657) baseStart_6613657 baseEnd_6613657 := by
    simpa [prefixWord, tailWord_6613657, baseEnd_6613657] using wordTrace_append hprefix tailTrace_6613657
  have hstable : (prefixWord ++ tailWord_6613657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6613657).length < 2 ^ (prefixWord ++ tailWord_6613657).sum := by decide
  have hdescent : baseEnd_6613657 < baseStart_6613657 := by decide
  rcases family_descends (prefixWord ++ tailWord_6613657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6613741 : List Nat := [1, 5, 1, 2, 1, 1, 4, 1, 3, 1, 3]
def baseStart_6613741 : Nat := 118140960795 + 6613741 * 2 ^ 59
def prefixEnd_6613741 : Nat := 4983230072969 + 3 ^ 40 * 6613741 * 2
def baseEnd_6613741 : Nat := 3396028057347713441621465

theorem tailTrace_6613741 : CollatzResearch.WordTrace tailWord_6613741 prefixEnd_6613741 3396028057347713441621465 := by
  unfold tailWord_6613741
  simp only [CollatzResearch.WordTrace]
  refine ⟨241222951532553368880873077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160815301021702245920582051 241222951532553368880873077)
  ·
    refine ⟨22614651706176878332581851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 241222951532553368880873077 22614651706176878332581851)
    ·
      refine ⟨33921977559265317498872777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22614651706176878332581851 33921977559265317498872777)
      ·
        refine ⟨25441483169448988124154583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33921977559265317498872777 25441483169448988124154583)
        ·
          refine ⟨38162224754173482186231875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25441483169448988124154583 38162224754173482186231875)
          ·
            refine ⟨57243337131260223279347813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38162224754173482186231875 57243337131260223279347813)
            ·
              refine ⟨10733125712111291864877715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57243337131260223279347813 10733125712111291864877715)
              ·
                refine ⟨16099688568166937797316573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10733125712111291864877715 16099688568166937797316573)
                ·
                  refine ⟨6037383213062601673993715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16099688568166937797316573 6037383213062601673993715)
                  ·
                    refine ⟨9056074819593902510990573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6037383213062601673993715 9056074819593902510990573)
                    ·
                      refine ⟨3396028057347713441621465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9056074819593902510990573 3396028057347713441621465)
                      ·
                        rfl

theorem cell23_6613741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 4, 1, 3, 1, 3].length) (baseStart_6613741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6613741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6613741 prefixEnd_6613741 := by exact prefixLift 6613741
  have htrace : WordTrace (prefixWord ++ tailWord_6613741) baseStart_6613741 baseEnd_6613741 := by
    simpa [prefixWord, tailWord_6613741, baseEnd_6613741] using wordTrace_append hprefix tailTrace_6613741
  have hstable : (prefixWord ++ tailWord_6613741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6613741).length < 2 ^ (prefixWord ++ tailWord_6613741).sum := by decide
  have hdescent : baseEnd_6613741 < baseStart_6613741 := by decide
  rcases family_descends (prefixWord ++ tailWord_6613741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6613764 : List Nat := [2, 3, 2, 2, 1, 1, 1, 1, 2, 6, 2]
def baseStart_6613764 : Nat := 118140960795 + 6613764 * 2 ^ 59
def prefixEnd_6613764 : Nat := 4983230072969 + 3 ^ 40 * 6613764 * 2
def baseEnd_6613764 : Nat := 3396039867402766851633859

theorem tailTrace_6613764 : CollatzResearch.WordTrace tailWord_6613764 prefixEnd_6613764 3396039867402766851633859 := by
  unfold tailWord_6613764
  simp only [CollatzResearch.WordTrace]
  refine ⟨120611895205735021904480173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160815860274313362539306897 120611895205735021904480173)
  ·
    refine ⟨45229460702150633214180065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120611895205735021904480173 45229460702150633214180065)
    ·
      refine ⟨33922095526612974910635049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45229460702150633214180065 33922095526612974910635049)
      ·
        refine ⟨25441571644959731182976287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33922095526612974910635049 25441571644959731182976287)
        ·
          refine ⟨38162357467439596774464431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25441571644959731182976287 38162357467439596774464431)
          ·
            refine ⟨57243536201159395161696647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38162357467439596774464431 57243536201159395161696647)
            ·
              refine ⟨85865304301739092742544971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57243536201159395161696647 85865304301739092742544971)
              ·
                refine ⟨128797956452608639113817457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85865304301739092742544971 128797956452608639113817457)
                ·
                  refine ⟨96598467339456479335363093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 128797956452608639113817457 96598467339456479335363093)
                  ·
                    refine ⟨4528053156537022468845145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 96598467339456479335363093 4528053156537022468845145)
                    ·
                      refine ⟨3396039867402766851633859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4528053156537022468845145 3396039867402766851633859)
                      ·
                        rfl

theorem cell23_6613764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 1, 2, 6, 2].length) (baseStart_6613764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6613764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6613764 prefixEnd_6613764 := by exact prefixLift 6613764
  have htrace : WordTrace (prefixWord ++ tailWord_6613764) baseStart_6613764 baseEnd_6613764 := by
    simpa [prefixWord, tailWord_6613764, baseEnd_6613764] using wordTrace_append hprefix tailTrace_6613764
  have hstable : (prefixWord ++ tailWord_6613764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6613764).length < 2 ^ (prefixWord ++ tailWord_6613764).sum := by decide
  have hdescent : baseEnd_6613764 < baseStart_6613764 := by decide
  rcases family_descends (prefixWord ++ tailWord_6613764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6613777 : List Nat := [1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 4]
def baseStart_6613777 : Nat := 118140960795 + 6613777 * 2 ^ 59
def prefixEnd_6613777 : Nat := 4983230072969 + 3 ^ 40 * 6613777 * 2
def baseEnd_6613777 : Nat := 3396046542651275300771299

theorem tailTrace_6613777 : CollatzResearch.WordTrace tailWord_6613777 prefixEnd_6613777 3396046542651275300771299 := by
  unfold tailWord_6613777
  simp only [CollatzResearch.WordTrace]
  refine ⟨241224264560422947029183585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160816176373615298019455723 241224264560422947029183585)
  ·
    refine ⟨180918198420317210271887689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241224264560422947029183585 180918198420317210271887689)
    ·
      refine ⟨135688648815237907703915767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180918198420317210271887689 135688648815237907703915767)
      ·
        refine ⟨203532973222856861555873651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135688648815237907703915767 203532973222856861555873651)
        ·
          refine ⟨305299459834285292333810477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203532973222856861555873651 305299459834285292333810477)
          ·
            refine ⟨114487297437856984625178929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 305299459834285292333810477 114487297437856984625178929)
            ·
              refine ⟨85865473078392738468884197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114487297437856984625178929 85865473078392738468884197)
              ·
                refine ⟨16099776202198638462915787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 85865473078392738468884197 16099776202198638462915787)
                ·
                  refine ⟨24149664303297957694373681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16099776202198638462915787 24149664303297957694373681)
                  ·
                    refine ⟨18112248227473468270780261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24149664303297957694373681 18112248227473468270780261)
                    ·
                      refine ⟨3396046542651275300771299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18112248227473468270780261 3396046542651275300771299)
                      ·
                        rfl

theorem cell23_6613777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 4].length) (baseStart_6613777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6613777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6613777 prefixEnd_6613777 := by exact prefixLift 6613777
  have htrace : WordTrace (prefixWord ++ tailWord_6613777) baseStart_6613777 baseEnd_6613777 := by
    simpa [prefixWord, tailWord_6613777, baseEnd_6613777] using wordTrace_append hprefix tailTrace_6613777
  have hstable : (prefixWord ++ tailWord_6613777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6613777).length < 2 ^ (prefixWord ++ tailWord_6613777).sum := by decide
  have hdescent : baseEnd_6613777 < baseStart_6613777 := by decide
  rcases family_descends (prefixWord ++ tailWord_6613777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6613818 : List Nat := [3, 1, 1, 1, 6, 2, 1, 2, 1, 2, 3]
def baseStart_6613818 : Nat := 118140960795 + 6613818 * 2 ^ 59
def prefixEnd_6613818 : Nat := 4983230072969 + 3 ^ 40 * 6613818 * 2
def baseEnd_6613818 : Nat := 3396067595358109640358611

theorem tailTrace_6613818 : CollatzResearch.WordTrace tailWord_6613818 prefixEnd_6613818 3396067595358109640358611 := by
  unfold tailWord_6613818
  simp only [CollatzResearch.WordTrace]
  refine ⟨60306439988318602757856527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160817173302182940687617405 60306439988318602757856527)
  ·
    refine ⟨90459659982477904136784791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60306439988318602757856527 90459659982477904136784791)
    ·
      refine ⟨135689489973716856205177187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90459659982477904136784791 135689489973716856205177187)
      ·
        refine ⟨203534234960575284307765781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135689489973716856205177187 203534234960575284307765781)
        ·
          refine ⟨9540667263776966451926521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 203534234960575284307765781 9540667263776966451926521)
          ·
            refine ⟨7155500447832724838944891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9540667263776966451926521 7155500447832724838944891)
            ·
              refine ⟨10733250671749087258417337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7155500447832724838944891 10733250671749087258417337)
              ·
                refine ⟨8049938003811815443813003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10733250671749087258417337 8049938003811815443813003)
                ·
                  refine ⟨12074907005717723165719505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8049938003811815443813003 12074907005717723165719505)
                  ·
                    refine ⟨9056180254288292374289629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12074907005717723165719505 9056180254288292374289629)
                    ·
                      refine ⟨3396067595358109640358611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9056180254288292374289629 3396067595358109640358611)
                      ·
                        rfl

theorem cell23_6613818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 1, 2, 1, 2, 3].length) (baseStart_6613818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6613818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6613818 prefixEnd_6613818 := by exact prefixLift 6613818
  have htrace : WordTrace (prefixWord ++ tailWord_6613818) baseStart_6613818 baseEnd_6613818 := by
    simpa [prefixWord, tailWord_6613818, baseEnd_6613818] using wordTrace_append hprefix tailTrace_6613818
  have hstable : (prefixWord ++ tailWord_6613818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6613818).length < 2 ^ (prefixWord ++ tailWord_6613818).sum := by decide
  have hdescent : baseEnd_6613818 < baseStart_6613818 := by decide
  rcases family_descends (prefixWord ++ tailWord_6613818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6613828 : List Nat := [2, 3, 4, 2, 1, 1, 1, 2, 1, 2, 4]
def baseStart_6613828 : Nat := 118140960795 + 6613828 * 2 ^ 59
def prefixEnd_6613828 : Nat := 4983230072969 + 3 ^ 40 * 6613828 * 2
def baseEnd_6613828 : Nat := 3396072730164654601233565

theorem tailTrace_6613828 : CollatzResearch.WordTrace tailWord_6613828 prefixEnd_6613828 3396072730164654601233565 := by
  unfold tailWord_6613828
  simp only [CollatzResearch.WordTrace]
  refine ⟨120613062341619091369645069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160817416455492121826193425 120613062341619091369645069)
  ·
    refine ⟨45229898378107159263616901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120613062341619091369645069 45229898378107159263616901)
    ·
      refine ⟨8480605945895092361928169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45229898378107159263616901 8480605945895092361928169)
      ·
        refine ⟨6360454459421319271446127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8480605945895092361928169 6360454459421319271446127)
        ·
          refine ⟨9540681689131978907169191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6360454459421319271446127 9540681689131978907169191)
          ·
            refine ⟨14311022533697968360753787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9540681689131978907169191 14311022533697968360753787)
            ·
              refine ⟨21466533800546952541130681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14311022533697968360753787 21466533800546952541130681)
              ·
                refine ⟨16099900350410214405848011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21466533800546952541130681 16099900350410214405848011)
                ·
                  refine ⟨24149850525615321608772017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16099900350410214405848011 24149850525615321608772017)
                  ·
                    refine ⟨18112387894211491206579013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24149850525615321608772017 18112387894211491206579013)
                    ·
                      refine ⟨3396072730164654601233565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18112387894211491206579013 3396072730164654601233565)
                      ·
                        rfl

theorem cell23_6613828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_6613828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6613828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6613828 prefixEnd_6613828 := by exact prefixLift 6613828
  have htrace : WordTrace (prefixWord ++ tailWord_6613828) baseStart_6613828 baseEnd_6613828 := by
    simpa [prefixWord, tailWord_6613828, baseEnd_6613828] using wordTrace_append hprefix tailTrace_6613828
  have hstable : (prefixWord ++ tailWord_6613828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6613828).length < 2 ^ (prefixWord ++ tailWord_6613828).sum := by decide
  have hdescent : baseEnd_6613828 < baseStart_6613828 := by decide
  rcases family_descends (prefixWord ++ tailWord_6613828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6613857 : List Nat := [1, 2, 3, 1, 1, 1, 2, 2, 4, 1, 5]
def baseStart_6613857 : Nat := 118140960795 + 6613857 * 2 ^ 59
def prefixEnd_6613857 : Nat := 4983230072969 + 3 ^ 40 * 6613857 * 2
def baseEnd_6613857 : Nat := 3396087621103634987770931

theorem tailTrace_6613857 : CollatzResearch.WordTrace tailWord_6613857 prefixEnd_6613857 3396087621103634987770931 := by
  unfold tailWord_6613857
  simp only [CollatzResearch.WordTrace]
  refine ⟨241227182400133120692095825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160818121600088747128063883 241227182400133120692095825)
  ·
    refine ⟨180920386800099840519071869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241227182400133120692095825 180920386800099840519071869)
    ·
      refine ⟨67845145050037440194651951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180920386800099840519071869 67845145050037440194651951)
      ·
        refine ⟨101767717575056160291977927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67845145050037440194651951 101767717575056160291977927)
        ·
          refine ⟨152651576362584240437966891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101767717575056160291977927 152651576362584240437966891)
          ·
            refine ⟨228977364543876360656950337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152651576362584240437966891 228977364543876360656950337)
            ·
              refine ⟨171733023407907270492712753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 228977364543876360656950337 171733023407907270492712753)
              ·
                refine ⟨128799767555930452869534565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 171733023407907270492712753 128799767555930452869534565)
                ·
                  refine ⟨24149956416736959913037731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 128799767555930452869534565 24149956416736959913037731)
                  ·
                    refine ⟨36224934625105439869556597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24149956416736959913037731 36224934625105439869556597)
                    ·
                      refine ⟨3396087621103634987770931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36224934625105439869556597 3396087621103634987770931)
                      ·
                        rfl

theorem cell23_6613857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 2, 4, 1, 5].length) (baseStart_6613857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6613857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6613857 prefixEnd_6613857 := by exact prefixLift 6613857
  have htrace : WordTrace (prefixWord ++ tailWord_6613857) baseStart_6613857 baseEnd_6613857 := by
    simpa [prefixWord, tailWord_6613857, baseEnd_6613857] using wordTrace_append hprefix tailTrace_6613857
  have hstable : (prefixWord ++ tailWord_6613857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6613857).length < 2 ^ (prefixWord ++ tailWord_6613857).sum := by decide
  have hdescent : baseEnd_6613857 < baseStart_6613857 := by decide
  rcases family_descends (prefixWord ++ tailWord_6613857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6613864 : List Nat := [2, 1, 4, 2, 1, 3, 1, 1, 2, 6]
def baseStart_6613864 : Nat := 118140960795 + 6613864 * 2 ^ 59
def prefixEnd_6613864 : Nat := 4983230072969 + 3 ^ 40 * 6613864 * 2
def baseEnd_6613864 : Nat := 1132030405156072153461133

theorem tailTrace_6613864 : CollatzResearch.WordTrace tailWord_6613864 prefixEnd_6613864 1132030405156072153461133 := by
  unfold tailWord_6613864
  simp only [CollatzResearch.WordTrace]
  refine ⟨120613718855553880443800323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160818291807405173925067097 120613718855553880443800323)
  ·
    refine ⟨180920578283330820665700485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120613718855553880443800323 180920578283330820665700485)
    ·
      refine ⟨33922608428124528874818841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 180920578283330820665700485 33922608428124528874818841)
      ·
        refine ⟨25441956321093396656114131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33922608428124528874818841 25441956321093396656114131)
        ·
          refine ⟨38162934481640094984171197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25441956321093396656114131 38162934481640094984171197)
          ·
            refine ⟨14311100430615035619064199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38162934481640094984171197 14311100430615035619064199)
            ·
              refine ⟨21466650645922553428596299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14311100430615035619064199 21466650645922553428596299)
              ·
                refine ⟨32199975968883830142894449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21466650645922553428596299 32199975968883830142894449)
                ·
                  refine ⟨24149981976662872607170837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32199975968883830142894449 24149981976662872607170837)
                  ·
                    refine ⟨1132030405156072153461133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24149981976662872607170837 1132030405156072153461133)
                    ·
                      rfl

theorem cell23_6613864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 1, 2, 6].length) (baseStart_6613864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6613864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6613864 prefixEnd_6613864 := by exact prefixLift 6613864
  have htrace : WordTrace (prefixWord ++ tailWord_6613864) baseStart_6613864 baseEnd_6613864 := by
    simpa [prefixWord, tailWord_6613864, baseEnd_6613864] using wordTrace_append hprefix tailTrace_6613864
  have hstable : (prefixWord ++ tailWord_6613864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6613864).length < 2 ^ (prefixWord ++ tailWord_6613864).sum := by decide
  have hdescent : baseEnd_6613864 < baseStart_6613864 := by decide
  rcases family_descends (prefixWord ++ tailWord_6613864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6613867 : List Nat := [1, 1, 1, 1, 2, 2, 5, 1, 1, 4, 4]
def baseStart_6613867 : Nat := 118140960795 + 6613867 * 2 ^ 59
def prefixEnd_6613867 : Nat := 4983230072969 + 3 ^ 40 * 6613867 * 2
def baseEnd_6613867 : Nat := 3396092755910179948645885

theorem tailTrace_6613867 : CollatzResearch.WordTrace tailWord_6613867 prefixEnd_6613867 3396092755910179948645885 := by
  unfold tailWord_6613867
  simp only [CollatzResearch.WordTrace]
  refine ⟨241227547130096892399959855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160818364753397928266639903 241227547130096892399959855)
  ·
    refine ⟨361841320695145338599939783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241227547130096892399959855 361841320695145338599939783)
    ·
      refine ⟨542761981042718007899909675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 361841320695145338599939783 542761981042718007899909675)
      ·
        refine ⟨814142971564077011849864513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 542761981042718007899909675 814142971564077011849864513)
        ·
          refine ⟨610607228673057758887398385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 814142971564077011849864513 610607228673057758887398385)
          ·
            refine ⟨457955421504793319165548789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 610607228673057758887398385 457955421504793319165548789)
            ·
              refine ⟨42933320766074373671770199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 457955421504793319165548789 42933320766074373671770199)
              ·
                refine ⟨64399981149111560507655299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42933320766074373671770199 64399981149111560507655299)
                ·
                  refine ⟨96599971723667340761482949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64399981149111560507655299 96599971723667340761482949)
                  ·
                    refine ⟨18112494698187626392778053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 96599971723667340761482949 18112494698187626392778053)
                    ·
                      refine ⟨3396092755910179948645885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18112494698187626392778053 3396092755910179948645885)
                      ·
                        rfl

theorem cell23_6613867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 1, 1, 4, 4].length) (baseStart_6613867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6613867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6613867 prefixEnd_6613867 := by exact prefixLift 6613867
  have htrace : WordTrace (prefixWord ++ tailWord_6613867) baseStart_6613867 baseEnd_6613867 := by
    simpa [prefixWord, tailWord_6613867, baseEnd_6613867] using wordTrace_append hprefix tailTrace_6613867
  have hstable : (prefixWord ++ tailWord_6613867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6613867).length < 2 ^ (prefixWord ++ tailWord_6613867).sum := by decide
  have hdescent : baseEnd_6613867 < baseStart_6613867 := by decide
  rcases family_descends (prefixWord ++ tailWord_6613867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6613921 : List Nat := [1, 2, 3, 4, 1, 1, 2, 1, 2, 3, 3]
def baseStart_6613921 : Nat := 118140960795 + 6613921 * 2 ^ 59
def prefixEnd_6613921 : Nat := 4983230072969 + 3 ^ 40 * 6613921 * 2
def baseEnd_6613921 : Nat := 3396120483865522737370637

theorem tailTrace_6613921 : CollatzResearch.WordTrace tailWord_6613921 prefixEnd_6613921 3396120483865522737370637 := by
  unfold tailWord_6613921
  simp only [CollatzResearch.WordTrace]
  refine ⟨241229516671901259622425617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160819677781267506414950411 241229516671901259622425617)
  ·
    refine ⟨180922137503925944716819213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241229516671901259622425617 180922137503925944716819213)
    ·
      refine ⟨67845801563972229268807205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180922137503925944716819213 67845801563972229268807205)
      ·
        refine ⟨12721087793244792987901351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67845801563972229268807205 12721087793244792987901351)
        ·
          refine ⟨19081631689867189481852027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12721087793244792987901351 19081631689867189481852027)
          ·
            refine ⟨28622447534800784222778041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19081631689867189481852027 28622447534800784222778041)
            ·
              refine ⟨21466835651100588167083531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28622447534800784222778041 21466835651100588167083531)
              ·
                refine ⟨32200253476650882250625297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21466835651100588167083531 32200253476650882250625297)
                ·
                  refine ⟨24150190107488161687968973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32200253476650882250625297 24150190107488161687968973)
                  ·
                    refine ⟨9056321290308060632988365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24150190107488161687968973 9056321290308060632988365)
                    ·
                      refine ⟨3396120483865522737370637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9056321290308060632988365 3396120483865522737370637)
                      ·
                        rfl

theorem cell23_6613921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_6613921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6613921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6613921 prefixEnd_6613921 := by exact prefixLift 6613921
  have htrace : WordTrace (prefixWord ++ tailWord_6613921) baseStart_6613921 baseEnd_6613921 := by
    simpa [prefixWord, tailWord_6613921, baseEnd_6613921] using wordTrace_append hprefix tailTrace_6613921
  have hstable : (prefixWord ++ tailWord_6613921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6613921).length < 2 ^ (prefixWord ++ tailWord_6613921).sum := by decide
  have hdescent : baseEnd_6613921 < baseStart_6613921 := by decide
  rcases family_descends (prefixWord ++ tailWord_6613921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6613922 : List Nat := [3, 3, 1, 2, 2, 2, 3, 1, 2, 2, 2]
def baseStart_6613922 : Nat := 118140960795 + 6613922 * 2 ^ 59
def prefixEnd_6613922 : Nat := 4983230072969 + 3 ^ 40 * 6613922 * 2
def baseEnd_6613922 : Nat := 3396120997346177233458133

theorem tailTrace_6613922 : CollatzResearch.WordTrace tailWord_6613922 prefixEnd_6613922 3396120997346177233458133 := by
  unfold tailWord_6613922
  simp only [CollatzResearch.WordTrace]
  refine ⟨60307388286224409198303005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160819702096598424528808013 60307388286224409198303005)
  ·
    refine ⟨22615270607334153449363627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60307388286224409198303005 22615270607334153449363627)
    ·
      refine ⟨33922905911001230174045441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22615270607334153449363627 33922905911001230174045441)
      ·
        refine ⟨25442179433250922630534081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33922905911001230174045441 25442179433250922630534081)
        ·
          refine ⟨19081634574938191972900561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25442179433250922630534081 19081634574938191972900561)
          ·
            refine ⟨14311225931203643979675421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19081634574938191972900561 14311225931203643979675421)
            ·
              refine ⟨5366709724201366492378283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14311225931203643979675421 5366709724201366492378283)
              ·
                refine ⟨8050064586302049738567425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5366709724201366492378283 8050064586302049738567425)
                ·
                  refine ⟨6037548439726537303925569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8050064586302049738567425 6037548439726537303925569)
                  ·
                    refine ⟨4528161329794902977944177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6037548439726537303925569 4528161329794902977944177)
                    ·
                      refine ⟨3396120997346177233458133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4528161329794902977944177 3396120997346177233458133)
                      ·
                        rfl

theorem cell23_6613922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 3, 1, 2, 2, 2].length) (baseStart_6613922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6613922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6613922 prefixEnd_6613922 := by exact prefixLift 6613922
  have htrace : WordTrace (prefixWord ++ tailWord_6613922) baseStart_6613922 baseEnd_6613922 := by
    simpa [prefixWord, tailWord_6613922, baseEnd_6613922] using wordTrace_append hprefix tailTrace_6613922
  have hstable : (prefixWord ++ tailWord_6613922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6613922).length < 2 ^ (prefixWord ++ tailWord_6613922).sum := by decide
  have hdescent : baseEnd_6613922 < baseStart_6613922 := by decide
  rcases family_descends (prefixWord ++ tailWord_6613922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6613944 : List Nat := [2, 1, 2, 1, 2, 4, 2, 1, 1, 3, 4]
def baseStart_6613944 : Nat := 118140960795 + 6613944 * 2 ^ 59
def prefixEnd_6613944 : Nat := 4983230072969 + 3 ^ 40 * 6613944 * 2
def baseEnd_6613944 : Nat := 3396132293920576147383031

theorem tailTrace_6613944 : CollatzResearch.WordTrace tailWord_6613944 prefixEnd_6613944 3396132293920576147383031 := by
  unfold tailWord_6613944
  simp only [CollatzResearch.WordTrace]
  refine ⟨120615177775408967275256443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160820237033878623033675257 120615177775408967275256443)
  ·
    refine ⟨180922766663113450912884665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120615177775408967275256443 180922766663113450912884665)
    ·
      refine ⟨135692074997335088184663499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180922766663113450912884665 135692074997335088184663499)
      ·
        refine ⟨203538112496002632276995249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135692074997335088184663499 203538112496002632276995249)
        ·
          refine ⟨152653584372001974207746437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 203538112496002632276995249 152653584372001974207746437)
          ·
            refine ⟨28622547069750370163952457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 152653584372001974207746437 28622547069750370163952457)
            ·
              refine ⟨21466910302312777622964343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28622547069750370163952457 21466910302312777622964343)
              ·
                refine ⟨32200365453469166434446515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21466910302312777622964343 32200365453469166434446515)
                ·
                  refine ⟨48300548180203749651669773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32200365453469166434446515 48300548180203749651669773)
                  ·
                    refine ⟨18112705567576406119376165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48300548180203749651669773 18112705567576406119376165)
                    ·
                      refine ⟨3396132293920576147383031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18112705567576406119376165 3396132293920576147383031)
                      ·
                        rfl

theorem cell23_6613944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 1, 1, 3, 4].length) (baseStart_6613944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6613944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6613944 prefixEnd_6613944 := by exact prefixLift 6613944
  have htrace : WordTrace (prefixWord ++ tailWord_6613944) baseStart_6613944 baseEnd_6613944 := by
    simpa [prefixWord, tailWord_6613944, baseEnd_6613944] using wordTrace_append hprefix tailTrace_6613944
  have hstable : (prefixWord ++ tailWord_6613944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6613944).length < 2 ^ (prefixWord ++ tailWord_6613944).sum := by decide
  have hdescent : baseEnd_6613944 < baseStart_6613944 := by decide
  rcases family_descends (prefixWord ++ tailWord_6613944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6614045 : List Nat := [1, 4, 2, 2, 3, 1, 1, 2, 3, 1, 3]
def baseStart_6614045 : Nat := 118140960795 + 6614045 * 2 ^ 59
def prefixEnd_6614045 : Nat := 4983230072969 + 3 ^ 40 * 6614045 * 2
def baseEnd_6614045 : Nat := 3396184155466680252220067

theorem tailTrace_6614045 : CollatzResearch.WordTrace tailWord_6614045 prefixEnd_6614045 3396184155466680252220067 := by
  unfold tailWord_6614045
  simp only [CollatzResearch.WordTrace]
  refine ⟨241234039323452028799939589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160822692882301352533293059 241234039323452028799939589)
  ·
    refine ⟨45231382373147255399988673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 241234039323452028799939589 45231382373147255399988673)
    ·
      refine ⟨33923536779860441549991505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45231382373147255399988673 33923536779860441549991505)
      ·
        refine ⟨25442652584895331162493629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33923536779860441549991505 25442652584895331162493629)
        ·
          refine ⟨9540994719335749185935111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25442652584895331162493629 9540994719335749185935111)
          ·
            refine ⟨14311492079003623778902667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9540994719335749185935111 14311492079003623778902667)
            ·
              refine ⟨21467238118505435668354001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14311492079003623778902667 21467238118505435668354001)
              ·
                refine ⟨16100428588879076751265501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21467238118505435668354001 16100428588879076751265501)
                ·
                  refine ⟨6037660720829653781724563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16100428588879076751265501 6037660720829653781724563)
                  ·
                    refine ⟨9056491081244480672586845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6037660720829653781724563 9056491081244480672586845)
                    ·
                      refine ⟨3396184155466680252220067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9056491081244480672586845 3396184155466680252220067)
                      ·
                        rfl

theorem cell23_6614045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 2, 3, 1, 3].length) (baseStart_6614045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6614045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6614045 prefixEnd_6614045 := by exact prefixLift 6614045
  have htrace : WordTrace (prefixWord ++ tailWord_6614045) baseStart_6614045 baseEnd_6614045 := by
    simpa [prefixWord, tailWord_6614045, baseEnd_6614045] using wordTrace_append hprefix tailTrace_6614045
  have hstable : (prefixWord ++ tailWord_6614045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6614045).length < 2 ^ (prefixWord ++ tailWord_6614045).sum := by decide
  have hdescent : baseEnd_6614045 < baseStart_6614045 := by decide
  rcases family_descends (prefixWord ++ tailWord_6614045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6614051 : List Nat := [1, 1, 1, 4, 3, 2, 2, 1, 3, 1, 4]
def baseStart_6614051 : Nat := 118140960795 + 6614051 * 2 ^ 59
def prefixEnd_6614051 : Nat := 4983230072969 + 3 ^ 40 * 6614051 * 2
def baseEnd_6614051 : Nat := 3396187236350607228745039

theorem tailTrace_6614051 : CollatzResearch.WordTrace tailWord_6614051 prefixEnd_6614051 3396187236350607228745039 := by
  unfold tailWord_6614051
  simp only [CollatzResearch.WordTrace]
  refine ⟨241234258161430291824658007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160822838774286861216438671 241234258161430291824658007)
  ·
    refine ⟨361851387242145437736987011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241234258161430291824658007 361851387242145437736987011)
    ·
      refine ⟨542777080863218156605480517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 361851387242145437736987011 542777080863218156605480517)
      ·
        refine ⟨101770702661853404363527597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 542777080863218156605480517 101770702661853404363527597)
        ·
          refine ⟨38164013498195026636322849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101770702661853404363527597 38164013498195026636322849)
          ·
            refine ⟨28623010123646269977242137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38164013498195026636322849 28623010123646269977242137)
            ·
              refine ⟨21467257592734702482931603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28623010123646269977242137 21467257592734702482931603)
              ·
                refine ⟨32200886389102053724397405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21467257592734702482931603 32200886389102053724397405)
                ·
                  refine ⟨12075332395913270146649027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32200886389102053724397405 12075332395913270146649027)
                  ·
                    refine ⟨18112998593869905219973541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12075332395913270146649027 18112998593869905219973541)
                    ·
                      refine ⟨3396187236350607228745039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18112998593869905219973541 3396187236350607228745039)
                      ·
                        rfl

theorem cell23_6614051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 1, 3, 1, 4].length) (baseStart_6614051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6614051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6614051 prefixEnd_6614051 := by exact prefixLift 6614051
  have htrace : WordTrace (prefixWord ++ tailWord_6614051) baseStart_6614051 baseEnd_6614051 := by
    simpa [prefixWord, tailWord_6614051, baseEnd_6614051] using wordTrace_append hprefix tailTrace_6614051
  have hstable : (prefixWord ++ tailWord_6614051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6614051).length < 2 ^ (prefixWord ++ tailWord_6614051).sum := by decide
  have hdescent : baseEnd_6614051 < baseStart_6614051 := by decide
  rcases family_descends (prefixWord ++ tailWord_6614051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6614055 : List Nat := [1, 1, 7, 1, 1, 2, 1, 1, 1, 5, 2]
def baseStart_6614055 : Nat := 118140960795 + 6614055 * 2 ^ 59
def prefixEnd_6614055 : Nat := 4983230072969 + 3 ^ 40 * 6614055 * 2
def baseEnd_6614055 : Nat := 3396189290273225213095021

theorem tailTrace_6614055 : CollatzResearch.WordTrace tailWord_6614055 prefixEnd_6614055 3396189290273225213095021 := by
  unfold tailWord_6614055
  simp only [CollatzResearch.WordTrace]
  refine ⟨241234404053415800507803619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160822936035610533671869079 241234404053415800507803619)
  ·
    refine ⟨361851606080123700761705429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241234404053415800507803619 361851606080123700761705429)
    ·
      refine ⟨8480897017502899236602471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 361851606080123700761705429 8480897017502899236602471)
      ·
        refine ⟨12721345526254348854903707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8480897017502899236602471 12721345526254348854903707)
        ·
          refine ⟨19082018289381523282355561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12721345526254348854903707 19082018289381523282355561)
          ·
            refine ⟨14311513717036142461766671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19082018289381523282355561 14311513717036142461766671)
            ·
              refine ⟨21467270575554213692650007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14311513717036142461766671 21467270575554213692650007)
              ·
                refine ⟨32200905863331320538975011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21467270575554213692650007 32200905863331320538975011)
                ·
                  refine ⟨48301358794996980808462517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32200905863331320538975011 48301358794996980808462517)
                  ·
                    refine ⟨4528252387030966950793361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48301358794996980808462517 4528252387030966950793361)
                    ·
                      refine ⟨3396189290273225213095021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4528252387030966950793361 3396189290273225213095021)
                      ·
                        rfl

theorem cell23_6614055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 1, 1, 5, 2].length) (baseStart_6614055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6614055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6614055 prefixEnd_6614055 := by exact prefixLift 6614055
  have htrace : WordTrace (prefixWord ++ tailWord_6614055) baseStart_6614055 baseEnd_6614055 := by
    simpa [prefixWord, tailWord_6614055, baseEnd_6614055] using wordTrace_append hprefix tailTrace_6614055
  have hstable : (prefixWord ++ tailWord_6614055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6614055).length < 2 ^ (prefixWord ++ tailWord_6614055).sum := by decide
  have hdescent : baseEnd_6614055 < baseStart_6614055 := by decide
  rcases family_descends (prefixWord ++ tailWord_6614055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6614062 : List Nat := [4, 1, 3, 1, 1, 1, 4, 3, 1, 1, 3]
def baseStart_6614062 : Nat := 118140960795 + 6614062 * 2 ^ 59
def prefixEnd_6614062 : Nat := 4983230072969 + 3 ^ 40 * 6614062 * 2
def baseEnd_6614062 : Nat := 3396192884637806685707489

theorem tailTrace_6614062 : CollatzResearch.WordTrace tailWord_6614062 prefixEnd_6614062 3396192884637806685707489 := by
  unfold tailWord_6614062
  simp only [CollatzResearch.WordTrace]
  refine ⟨30154332420548805087913555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 160823106242926960468872293 30154332420548805087913555)
  ·
    refine ⟨45231498630823207631870333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30154332420548805087913555 45231498630823207631870333)
    ·
      refine ⟨16961811986558702861951375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45231498630823207631870333 16961811986558702861951375)
      ·
        refine ⟨25442717979838054292927063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16961811986558702861951375 25442717979838054292927063)
        ·
          refine ⟨38164076969757081439390595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25442717979838054292927063 38164076969757081439390595)
          ·
            refine ⟨57246115454635622159085893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38164076969757081439390595 57246115454635622159085893)
            ·
              refine ⟨10733646647744179154828605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57246115454635622159085893 10733646647744179154828605)
              ·
                refine ⟨4025117492904067183060727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10733646647744179154828605 4025117492904067183060727)
                ·
                  refine ⟨6037676239356100774591091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4025117492904067183060727 6037676239356100774591091)
                  ·
                    refine ⟨9056514359034151161886637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6037676239356100774591091 9056514359034151161886637)
                    ·
                      refine ⟨3396192884637806685707489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9056514359034151161886637 3396192884637806685707489)
                      ·
                        rfl

theorem cell23_6614062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 4, 3, 1, 1, 3].length) (baseStart_6614062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6614062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6614062 prefixEnd_6614062 := by exact prefixLift 6614062
  have htrace : WordTrace (prefixWord ++ tailWord_6614062) baseStart_6614062 baseEnd_6614062 := by
    simpa [prefixWord, tailWord_6614062, baseEnd_6614062] using wordTrace_append hprefix tailTrace_6614062
  have hstable : (prefixWord ++ tailWord_6614062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6614062).length < 2 ^ (prefixWord ++ tailWord_6614062).sum := by decide
  have hdescent : baseEnd_6614062 < baseStart_6614062 := by decide
  rcases family_descends (prefixWord ++ tailWord_6614062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6614098 : List Nat := [3, 2, 2, 1, 3, 1, 3, 1, 1, 2, 4]
def baseStart_6614098 : Nat := 118140960795 + 6614098 * 2 ^ 59
def prefixEnd_6614098 : Nat := 4983230072969 + 3 ^ 40 * 6614098 * 2
def baseEnd_6614098 : Nat := 3396211369941368544857323

theorem tailTrace_6614098 : CollatzResearch.WordTrace tailWord_6614098 prefixEnd_6614098 3396211369941368544857323 := by
  unfold tailWord_6614098
  simp only [CollatzResearch.WordTrace]
  refine ⟨60308993098065004712904737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160823981594840012567745965 60308993098065004712904737)
  ·
    refine ⟨45231744823548753534678553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60308993098065004712904737 45231744823548753534678553)
    ·
      refine ⟨33923808617661565151008915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45231744823548753534678553 33923808617661565151008915)
      ·
        refine ⟨50885712926492347726513373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33923808617661565151008915 50885712926492347726513373)
        ·
          refine ⟨19082142347434630397442515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50885712926492347726513373 19082142347434630397442515)
          ·
            refine ⟨28623213521151945596163773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19082142347434630397442515 28623213521151945596163773)
            ·
              refine ⟨10733705070431979598561415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28623213521151945596163773 10733705070431979598561415)
              ·
                refine ⟨16100557605647969397842123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10733705070431979598561415 16100557605647969397842123)
                ·
                  refine ⟨24150836408471954096763185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16100557605647969397842123 24150836408471954096763185)
                  ·
                    refine ⟨18113127306353965572572389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24150836408471954096763185 18113127306353965572572389)
                    ·
                      refine ⟨3396211369941368544857323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18113127306353965572572389 3396211369941368544857323)
                      ·
                        rfl

theorem cell23_6614098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 3, 1, 1, 2, 4].length) (baseStart_6614098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6614098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6614098 prefixEnd_6614098 := by exact prefixLift 6614098
  have htrace : WordTrace (prefixWord ++ tailWord_6614098) baseStart_6614098 baseEnd_6614098 := by
    simpa [prefixWord, tailWord_6614098, baseEnd_6614098] using wordTrace_append hprefix tailTrace_6614098
  have hstable : (prefixWord ++ tailWord_6614098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6614098).length < 2 ^ (prefixWord ++ tailWord_6614098).sum := by decide
  have hdescent : baseEnd_6614098 < baseStart_6614098 := by decide
  rcases family_descends (prefixWord ++ tailWord_6614098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6614119 : List Nat := [1, 1, 5, 1, 1, 5, 1, 3, 1, 2, 2]
def baseStart_6614119 : Nat := 118140960795 + 6614119 * 2 ^ 59
def prefixEnd_6614119 : Nat := 4983230072969 + 3 ^ 40 * 6614119 * 2
def baseEnd_6614119 : Nat := 3396222153035112962694727

theorem tailTrace_6614119 : CollatzResearch.WordTrace tailWord_6614119 prefixEnd_6614119 3396222153035112962694727 := by
  unfold tailWord_6614119
  simp only [CollatzResearch.WordTrace]
  refine ⟨241236738325183939438133411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160824492216789292958755607 241236738325183939438133411)
  ·
    refine ⟨361855107487775909157200117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241236738325183939438133411 361855107487775909157200117)
    ·
      refine ⟨33923916326978991483487511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 361855107487775909157200117 33923916326978991483487511)
      ·
        refine ⟨50885874490468487225231267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33923916326978991483487511 50885874490468487225231267)
        ·
          refine ⟨76328811735702730837846901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50885874490468487225231267 76328811735702730837846901)
          ·
            refine ⟨7155826100222131016048147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 76328811735702730837846901 7155826100222131016048147)
            ·
              refine ⟨10733739150333196524072221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7155826100222131016048147 10733739150333196524072221)
              ·
                refine ⟨4025152181374948696527083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10733739150333196524072221 4025152181374948696527083)
                ·
                  refine ⟨6037728272062423044790625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4025152181374948696527083 6037728272062423044790625)
                  ·
                    refine ⟨4528296204046817283592969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6037728272062423044790625 4528296204046817283592969)
                    ·
                      refine ⟨3396222153035112962694727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4528296204046817283592969 3396222153035112962694727)
                      ·
                        rfl

theorem cell23_6614119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 1, 3, 1, 2, 2].length) (baseStart_6614119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6614119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6614119 prefixEnd_6614119 := by exact prefixLift 6614119
  have htrace : WordTrace (prefixWord ++ tailWord_6614119) baseStart_6614119 baseEnd_6614119 := by
    simpa [prefixWord, tailWord_6614119, baseEnd_6614119] using wordTrace_append hprefix tailTrace_6614119
  have hstable : (prefixWord ++ tailWord_6614119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6614119).length < 2 ^ (prefixWord ++ tailWord_6614119).sum := by decide
  have hdescent : baseEnd_6614119 < baseStart_6614119 := by decide
  rcases family_descends (prefixWord ++ tailWord_6614119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6614141 : List Nat := [1, 4, 1, 1, 3, 1, 2, 1, 2, 3, 4]
def baseStart_6614141 : Nat := 118140960795 + 6614141 * 2 ^ 59
def prefixEnd_6614141 : Nat := 4983230072969 + 3 ^ 40 * 6614141 * 2
def baseEnd_6614141 : Nat := 3396233449609511876619625

theorem tailTrace_6614141 : CollatzResearch.WordTrace tailWord_6614141 prefixEnd_6614141 3396233449609511876619625 := by
  unfold tailWord_6614141
  simp only [CollatzResearch.WordTrace]
  refine ⟨241237540731104237195434277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160825027154069491463622851 241237540731104237195434277)
  ·
    refine ⟨45232038887082044474143927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 241237540731104237195434277 45232038887082044474143927)
    ·
      refine ⟨67848058330623066711215891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45232038887082044474143927 67848058330623066711215891)
      ·
        refine ⟨101772087495934600066823837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67848058330623066711215891 101772087495934600066823837)
        ·
          refine ⟨38164532810975475025058939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101772087495934600066823837 38164532810975475025058939)
          ·
            refine ⟨57246799216463212537588409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38164532810975475025058939 57246799216463212537588409)
            ·
              refine ⟨42935099412347409403191307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57246799216463212537588409 42935099412347409403191307)
              ·
                refine ⟨64402649118521114104786961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42935099412347409403191307 64402649118521114104786961)
                ·
                  refine ⟨48301986838890835578590221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64402649118521114104786961 48301986838890835578590221)
                  ·
                    refine ⟨18113245064584063341971333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48301986838890835578590221 18113245064584063341971333)
                    ·
                      refine ⟨3396233449609511876619625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18113245064584063341971333 3396233449609511876619625)
                      ·
                        rfl

theorem cell23_6614141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 1, 2, 3, 4].length) (baseStart_6614141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6614141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6614141 prefixEnd_6614141 := by exact prefixLift 6614141
  have htrace : WordTrace (prefixWord ++ tailWord_6614141) baseStart_6614141 baseEnd_6614141 := by
    simpa [prefixWord, tailWord_6614141, baseEnd_6614141] using wordTrace_append hprefix tailTrace_6614141
  have hstable : (prefixWord ++ tailWord_6614141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6614141).length < 2 ^ (prefixWord ++ tailWord_6614141).sum := by decide
  have hdescent : baseEnd_6614141 < baseStart_6614141 := by decide
  rcases family_descends (prefixWord ++ tailWord_6614141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6614142 : List Nat := [4, 2, 4, 1, 1, 1, 2, 8]
def baseStart_6614142 : Nat := 118140960795 + 6614142 * 2 ^ 59
def prefixEnd_6614142 : Nat := 4983230072969 + 3 ^ 40 * 6614142 * 2
def baseEnd_6614142 : Nat := 125786443077413569359523

theorem tailTrace_6614142 : CollatzResearch.WordTrace tailWord_6614142 prefixEnd_6614142 125786443077413569359523 := by
  unfold tailWord_6614142
  simp only [CollatzResearch.WordTrace]
  refine ⟨30154697150512576795777585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 160825051469400409577480453 30154697150512576795777585)
  ·
    refine ⟨22616022862884432596833189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30154697150512576795777585 22616022862884432596833189)
    ·
      refine ⟨4240504286790831111906223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22616022862884432596833189 4240504286790831111906223)
      ·
        refine ⟨6360756430186246667859335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4240504286790831111906223 6360756430186246667859335)
        ·
          refine ⟨9541134645279370001789003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6360756430186246667859335 9541134645279370001789003)
          ·
            refine ⟨14311701967919055002683505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9541134645279370001789003 14311701967919055002683505)
            ·
              refine ⟨10733776475939291252012629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14311701967919055002683505 10733776475939291252012629)
              ·
                refine ⟨125786443077413569359523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10733776475939291252012629 125786443077413569359523)
                ·
                  rfl

theorem cell23_6614142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 2, 8].length) (baseStart_6614142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6614142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6614142 prefixEnd_6614142 := by exact prefixLift 6614142
  have htrace : WordTrace (prefixWord ++ tailWord_6614142) baseStart_6614142 baseEnd_6614142 := by
    simpa [prefixWord, tailWord_6614142, baseEnd_6614142] using wordTrace_append hprefix tailTrace_6614142
  have hstable : (prefixWord ++ tailWord_6614142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6614142).length < 2 ^ (prefixWord ++ tailWord_6614142).sum := by decide
  have hdescent : baseEnd_6614142 < baseStart_6614142 := by decide
  rcases family_descends (prefixWord ++ tailWord_6614142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6614152 : List Nat := [2, 1, 3, 4, 2, 1, 1, 3, 2, 1, 3]
def baseStart_6614152 : Nat := 118140960795 + 6614152 * 2 ^ 59
def prefixEnd_6614152 : Nat := 4983230072969 + 3 ^ 40 * 6614152 * 2
def baseEnd_6614152 : Nat := 3396239097896711333582075

theorem tailTrace_6614152 : CollatzResearch.WordTrace tailWord_6614152 prefixEnd_6614152 3396239097896711333582075 := by
  unfold tailWord_6614152
  simp only [CollatzResearch.WordTrace]
  refine ⟨120618970967032193037042355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160825294622709590716056473 120618970967032193037042355)
  ·
    refine ⟨180928456450548289555563533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120618970967032193037042355 180928456450548289555563533)
    ·
      refine ⟨67848171168955608583336325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180928456450548289555563533 67848171168955608583336325)
      ·
        refine ⟨12721532094179176609375561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67848171168955608583336325 12721532094179176609375561)
        ·
          refine ⟨9541149070634382457031671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12721532094179176609375561 9541149070634382457031671)
          ·
            refine ⟨14311723605951573685547507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9541149070634382457031671 14311723605951573685547507)
            ·
              refine ⟨21467585408927360528321261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14311723605951573685547507 21467585408927360528321261)
              ·
                refine ⟨8050344528347760198120473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21467585408927360528321261 8050344528347760198120473)
                ·
                  refine ⟨6037758396260820148590355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8050344528347760198120473 6037758396260820148590355)
                  ·
                    refine ⟨9056637594391230222885533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6037758396260820148590355 9056637594391230222885533)
                    ·
                      refine ⟨3396239097896711333582075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9056637594391230222885533 3396239097896711333582075)
                      ·
                        rfl

theorem cell23_6614152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_6614152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6614152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6614152 prefixEnd_6614152 := by exact prefixLift 6614152
  have htrace : WordTrace (prefixWord ++ tailWord_6614152) baseStart_6614152 baseEnd_6614152 := by
    simpa [prefixWord, tailWord_6614152, baseEnd_6614152] using wordTrace_append hprefix tailTrace_6614152
  have hstable : (prefixWord ++ tailWord_6614152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6614152).length < 2 ^ (prefixWord ++ tailWord_6614152).sum := by decide
  have hdescent : baseEnd_6614152 < baseStart_6614152 := by decide
  rcases family_descends (prefixWord ++ tailWord_6614152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6614162 : List Nat := [3, 2, 3, 1, 1, 2, 3, 2, 1, 3, 2]
def baseStart_6614162 : Nat := 118140960795 + 6614162 * 2 ^ 59
def prefixEnd_6614162 : Nat := 4983230072969 + 3 ^ 40 * 6614162 * 2
def baseEnd_6614162 : Nat := 3396244232703256294457029

theorem tailTrace_6614162 : CollatzResearch.WordTrace tailWord_6614162 prefixEnd_6614162 3396244232703256294457029 := by
  unfold tailWord_6614162
  simp only [CollatzResearch.WordTrace]
  refine ⟨60309576666007039445487185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160825537776018771854632493 60309576666007039445487185)
  ·
    refine ⟨45232182499505279584115389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60309576666007039445487185 45232182499505279584115389)
    ·
      refine ⟨16962068437314479844043271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45232182499505279584115389 16962068437314479844043271)
      ·
        refine ⟨25443102655971719766064907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16962068437314479844043271 25443102655971719766064907)
        ·
          refine ⟨38164653983957579649097361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25443102655971719766064907 38164653983957579649097361)
          ·
            refine ⟨28623490487968184736823021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38164653983957579649097361 28623490487968184736823021)
            ·
              refine ⟨10733808932988069276308633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28623490487968184736823021 10733808932988069276308633)
              ·
                refine ⟨8050356699741051957231475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10733808932988069276308633 8050356699741051957231475)
                ·
                  refine ⟨12075535049611577935847213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8050356699741051957231475 12075535049611577935847213)
                  ·
                    refine ⟨4528325643604341725942705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12075535049611577935847213 4528325643604341725942705)
                    ·
                      refine ⟨3396244232703256294457029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4528325643604341725942705 3396244232703256294457029)
                      ·
                        rfl

theorem cell23_6614162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 3, 2, 1, 3, 2].length) (baseStart_6614162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6614162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6614162 prefixEnd_6614162 := by exact prefixLift 6614162
  have htrace : WordTrace (prefixWord ++ tailWord_6614162) baseStart_6614162 baseEnd_6614162 := by
    simpa [prefixWord, tailWord_6614162, baseEnd_6614162] using wordTrace_append hprefix tailTrace_6614162
  have hstable : (prefixWord ++ tailWord_6614162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6614162).length < 2 ^ (prefixWord ++ tailWord_6614162).sum := by decide
  have hdescent : baseEnd_6614162 < baseStart_6614162 := by decide
  rcases family_descends (prefixWord ++ tailWord_6614162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6614209 : List Nat := [1, 2, 6, 1, 1, 1, 2, 3, 2, 2, 2]
def baseStart_6614209 : Nat := 118140960795 + 6614209 * 2 ^ 59
def prefixEnd_6614209 : Nat := 4983230072969 + 3 ^ 40 * 6614209 * 2
def baseEnd_6614209 : Nat := 3396268366294017610569313

theorem tailTrace_6614209 : CollatzResearch.WordTrace tailWord_6614209 prefixEnd_6614209 3396268366294017610569313 := by
  unfold tailWord_6614209
  simp only [CollatzResearch.WordTrace]
  refine ⟨241240020894857884808909681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160826680596571923205939787 241240020894857884808909681)
  ·
    refine ⟨180930015671143413606682261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241240020894857884808909681 180930015671143413606682261)
    ·
      refine ⟨8481094484584847512813231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 180930015671143413606682261 8481094484584847512813231)
      ·
        refine ⟨12721641726877271269219847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8481094484584847512813231 12721641726877271269219847)
        ·
          refine ⟨19082462590315906903829771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12721641726877271269219847 19082462590315906903829771)
          ·
            refine ⟨28623693885473860355744657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19082462590315906903829771 28623693885473860355744657)
            ·
              refine ⟨21467770414105395266808493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28623693885473860355744657 21467770414105395266808493)
              ·
                refine ⟨8050413905289523225053185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21467770414105395266808493 8050413905289523225053185)
                ·
                  refine ⟨6037810428967142418789889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8050413905289523225053185 6037810428967142418789889)
                  ·
                    refine ⟨4528357821725356814092417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6037810428967142418789889 4528357821725356814092417)
                    ·
                      refine ⟨3396268366294017610569313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4528357821725356814092417 3396268366294017610569313)
                      ·
                        rfl

theorem cell23_6614209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 3, 2, 2, 2].length) (baseStart_6614209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6614209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6614209 prefixEnd_6614209 := by exact prefixLift 6614209
  have htrace : WordTrace (prefixWord ++ tailWord_6614209) baseStart_6614209 baseEnd_6614209 := by
    simpa [prefixWord, tailWord_6614209, baseEnd_6614209] using wordTrace_append hprefix tailTrace_6614209
  have hstable : (prefixWord ++ tailWord_6614209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6614209).length < 2 ^ (prefixWord ++ tailWord_6614209).sum := by decide
  have hdescent : baseEnd_6614209 < baseStart_6614209 := by decide
  rcases family_descends (prefixWord ++ tailWord_6614209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6614248 : List Nat := [2, 1, 4, 1, 2, 1, 2, 1, 4, 1, 4]
def baseStart_6614248 : Nat := 118140960795 + 6614248 * 2 ^ 59
def prefixEnd_6614248 : Nat := 4983230072969 + 3 ^ 40 * 6614248 * 2
def baseEnd_6614248 : Nat := 3396288392039542957981633

theorem tailTrace_6614248 : CollatzResearch.WordTrace tailWord_6614248 prefixEnd_6614248 3396288392039542957981633 := by
  unfold tailWord_6614248
  simp only [CollatzResearch.WordTrace]
  refine ⟨120620721670858297234789699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160827628894477729646386265 120620721670858297234789699)
  ·
    refine ⟨180931082506287445852184549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120620721670858297234789699 180931082506287445852184549)
    ·
      refine ⟨33924577969928896097284603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 180931082506287445852184549 33924577969928896097284603)
      ·
        refine ⟨50886866954893344145926905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33924577969928896097284603 50886866954893344145926905)
        ·
          refine ⟨38165150216170008109445179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50886866954893344145926905 38165150216170008109445179)
          ·
            refine ⟨57247725324255012164167769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38165150216170008109445179 57247725324255012164167769)
            ·
              refine ⟨42935793993191259123125827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57247725324255012164167769 42935793993191259123125827)
              ·
                refine ⟨64403690989786888684688741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42935793993191259123125827 64403690989786888684688741)
                ·
                  refine ⟨12075692060585041628379139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64403690989786888684688741 12075692060585041628379139)
                  ·
                    refine ⟨18113538090877562442568709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12075692060585041628379139 18113538090877562442568709)
                    ·
                      refine ⟨3396288392039542957981633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18113538090877562442568709 3396288392039542957981633)
                      ·
                        rfl

theorem cell23_6614248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 1, 4, 1, 4].length) (baseStart_6614248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6614248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6614248 prefixEnd_6614248 := by exact prefixLift 6614248
  have htrace : WordTrace (prefixWord ++ tailWord_6614248) baseStart_6614248 baseEnd_6614248 := by
    simpa [prefixWord, tailWord_6614248, baseEnd_6614248] using wordTrace_append hprefix tailTrace_6614248
  have hstable : (prefixWord ++ tailWord_6614248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6614248).length < 2 ^ (prefixWord ++ tailWord_6614248).sum := by decide
  have hdescent : baseEnd_6614248 < baseStart_6614248 := by decide
  rcases family_descends (prefixWord ++ tailWord_6614248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6614260 : List Nat := [2, 6, 1, 2, 1, 1, 3, 1, 2, 2, 2]
def baseStart_6614260 : Nat := 118140960795 + 6614260 * 2 ^ 59
def prefixEnd_6614260 : Nat := 4983230072969 + 3 ^ 40 * 6614260 * 2
def baseEnd_6614260 : Nat := 3396294553807396911031579

theorem tailTrace_6614260 : CollatzResearch.WordTrace tailWord_6614260 prefixEnd_6614260 3396294553807396911031579 := by
  unfold tailWord_6614260
  simp only [CollatzResearch.WordTrace]
  refine ⟨120620940508836560259508117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160827920678448747012677489 120620940508836560259508117)
  ·
    refine ⟨5654106586351713762164443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 120620940508836560259508117 5654106586351713762164443)
    ·
      refine ⟨8481159879527570643246665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5654106586351713762164443 8481159879527570643246665)
      ·
        refine ⟨6360869909645677982434999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8481159879527570643246665 6360869909645677982434999)
        ·
          refine ⟨9541304864468516973652499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6360869909645677982434999 9541304864468516973652499)
          ·
            refine ⟨14311957296702775460478749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9541304864468516973652499 14311957296702775460478749)
            ·
              refine ⟨5366983986263540797679531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14311957296702775460478749 5366983986263540797679531)
              ·
                refine ⟨8050475979395311196519297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5366983986263540797679531 8050475979395311196519297)
                ·
                  refine ⟨6037856984546483397389473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8050475979395311196519297 6037856984546483397389473)
                  ·
                    refine ⟨4528392738409862548042105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6037856984546483397389473 4528392738409862548042105)
                    ·
                      refine ⟨3396294553807396911031579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4528392738409862548042105 3396294553807396911031579)
                      ·
                        rfl

theorem cell23_6614260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_6614260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6614260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6614260 prefixEnd_6614260 := by exact prefixLift 6614260
  have htrace : WordTrace (prefixWord ++ tailWord_6614260) baseStart_6614260 baseEnd_6614260 := by
    simpa [prefixWord, tailWord_6614260, baseEnd_6614260] using wordTrace_append hprefix tailTrace_6614260
  have hstable : (prefixWord ++ tailWord_6614260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6614260).length < 2 ^ (prefixWord ++ tailWord_6614260).sum := by decide
  have hdescent : baseEnd_6614260 < baseStart_6614260 := by decide
  rcases family_descends (prefixWord ++ tailWord_6614260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6614309 : List Nat := [1, 3, 1, 2, 4, 2, 3, 2, 1, 4]
def baseStart_6614309 : Nat := 118140960795 + 6614309 * 2 ^ 59
def prefixEnd_6614309 : Nat := 4983230072969 + 3 ^ 40 * 6614309 * 2
def baseEnd_6614309 : Nat := 1132106571453155739772951

theorem tailTrace_6614309 : CollatzResearch.WordTrace tailWord_6614309 prefixEnd_6614309 1132106571453155739772951 := by
  unfold tailWord_6614309
  simp only [CollatzResearch.WordTrace]
  refine ⟨241243668194495601887549981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160829112129663734591699987 241243668194495601887549981)
  ·
    refine ⟨90466375572935850707831243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 241243668194495601887549981 90466375572935850707831243)
    ·
      refine ⟨135699563359403776061746865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90466375572935850707831243 135699563359403776061746865)
      ·
        refine ⟨101774672519552832046310149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135699563359403776061746865 101774672519552832046310149)
        ·
          refine ⟨19082751097416156008683153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 101774672519552832046310149 19082751097416156008683153)
          ·
            refine ⟨14312063323062117006512365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19082751097416156008683153 14312063323062117006512365)
            ·
              refine ⟨5367023746148293877442137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14312063323062117006512365 5367023746148293877442137)
              ·
                refine ⟨4025267809611220408081603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5367023746148293877442137 4025267809611220408081603)
                ·
                  refine ⟨6037901714416830612122405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4025267809611220408081603 6037901714416830612122405)
                  ·
                    refine ⟨1132106571453155739772951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6037901714416830612122405 1132106571453155739772951)
                    ·
                      rfl

theorem cell23_6614309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 3, 2, 1, 4].length) (baseStart_6614309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6614309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6614309 prefixEnd_6614309 := by exact prefixLift 6614309
  have htrace : WordTrace (prefixWord ++ tailWord_6614309) baseStart_6614309 baseEnd_6614309 := by
    simpa [prefixWord, tailWord_6614309, baseEnd_6614309] using wordTrace_append hprefix tailTrace_6614309
  have hstable : (prefixWord ++ tailWord_6614309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6614309).length < 2 ^ (prefixWord ++ tailWord_6614309).sum := by decide
  have hdescent : baseEnd_6614309 < baseStart_6614309 := by decide
  rcases family_descends (prefixWord ++ tailWord_6614309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6614322 : List Nat := [3, 2, 1, 1, 4, 3, 2, 1, 6]
def baseStart_6614322 : Nat := 118140960795 + 6614322 * 2 ^ 59
def prefixEnd_6614322 : Nat := 4983230072969 + 3 ^ 40 * 6614322 * 2
def baseEnd_6614322 : Nat := 377369598845330629828477

theorem tailTrace_6614322 : CollatzResearch.WordTrace tailWord_6614322 prefixEnd_6614322 377369598845330629828477 := by
  unfold tailWord_6614322
  simp only [CollatzResearch.WordTrace]
  refine ⟨60311035585862126276943305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160829428228965670071848813 60311035585862126276943305)
  ·
    refine ⟨45233276689396594707707479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60311035585862126276943305 45233276689396594707707479)
    ·
      refine ⟨67849915034094892061561219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45233276689396594707707479 67849915034094892061561219)
      ·
        refine ⟨101774872551142338092341829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67849915034094892061561219 101774872551142338092341829)
        ·
          refine ⟨19082788603339188392314093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 101774872551142338092341829 19082788603339188392314093)
          ·
            refine ⟨7156045726252195647117785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19082788603339188392314093 7156045726252195647117785)
            ·
              refine ⟨5367034294689146735338339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7156045726252195647117785 5367034294689146735338339)
              ·
                refine ⟨8050551442033720103007509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5367034294689146735338339 8050551442033720103007509)
                ·
                  refine ⟨377369598845330629828477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8050551442033720103007509 377369598845330629828477)
                  ·
                    rfl

theorem cell23_6614322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 2, 1, 6].length) (baseStart_6614322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6614322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6614322 prefixEnd_6614322 := by exact prefixLift 6614322
  have htrace : WordTrace (prefixWord ++ tailWord_6614322) baseStart_6614322 baseEnd_6614322 := by
    simpa [prefixWord, tailWord_6614322, baseEnd_6614322] using wordTrace_append hprefix tailTrace_6614322
  have hstable : (prefixWord ++ tailWord_6614322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6614322).length < 2 ^ (prefixWord ++ tailWord_6614322).sum := by decide
  have hdescent : baseEnd_6614322 < baseStart_6614322 := by decide
  rcases family_descends (prefixWord ++ tailWord_6614322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6614335 : List Nat := [1, 1, 2, 2, 4, 2, 3, 2, 1, 5]
def baseStart_6614335 : Nat := 118140960795 + 6614335 * 2 ^ 59
def prefixEnd_6614335 : Nat := 4983230072969 + 3 ^ 40 * 6614335 * 2
def baseEnd_6614335 : Nat := 1132111021618828039197911

theorem tailTrace_6614335 : CollatzResearch.WordTrace tailWord_6614335 prefixEnd_6614335 1132111021618828039197911 := by
  unfold tailWord_6614335
  simp only [CollatzResearch.WordTrace]
  refine ⟨241244616492401408327996459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160829744328267605551997639 241244616492401408327996459)
  ·
    refine ⟨361866924738602112491994689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241244616492401408327996459 361866924738602112491994689)
    ·
      refine ⟨271400193553951584368996017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 361866924738602112491994689 271400193553951584368996017)
      ·
        refine ⟨203550145165463688276747013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 271400193553951584368996017 203550145165463688276747013)
        ·
          refine ⟨38165652218524441551890065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 203550145165463688276747013 38165652218524441551890065)
          ·
            refine ⟨28624239163893331163917549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38165652218524441551890065 28624239163893331163917549)
            ·
              refine ⟨10734089686459999186469081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28624239163893331163917549 10734089686459999186469081)
              ·
                refine ⟨8050567264844999389851811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10734089686459999186469081 8050567264844999389851811)
                ·
                  refine ⟨12075850897267499084777717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8050567264844999389851811 12075850897267499084777717)
                  ·
                    refine ⟨1132111021618828039197911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12075850897267499084777717 1132111021618828039197911)
                    ·
                      rfl

theorem cell23_6614335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 3, 2, 1, 5].length) (baseStart_6614335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6614335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6614335 prefixEnd_6614335 := by exact prefixLift 6614335
  have htrace : WordTrace (prefixWord ++ tailWord_6614335) baseStart_6614335 baseEnd_6614335 := by
    simpa [prefixWord, tailWord_6614335, baseEnd_6614335] using wordTrace_append hprefix tailTrace_6614335
  have hstable : (prefixWord ++ tailWord_6614335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6614335).length < 2 ^ (prefixWord ++ tailWord_6614335).sum := by decide
  have hdescent : baseEnd_6614335 < baseStart_6614335 := by decide
  rcases family_descends (prefixWord ++ tailWord_6614335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6614348 : List Nat := [2, 2, 1, 3, 2, 2, 1, 1, 3, 6]
def baseStart_6614348 : Nat := 118140960795 + 6614348 * 2 ^ 59
def prefixEnd_6614348 : Nat := 4983230072969 + 3 ^ 40 * 6614348 * 2
def baseEnd_6614348 : Nat := 1132113246701664188910391

theorem tailTrace_6614348 : CollatzResearch.WordTrace tailWord_6614348 prefixEnd_6614348 1132113246701664188910391 := by
  unfold tailWord_6614348
  simp only [CollatzResearch.WordTrace]
  refine ⟨120622545320677155774109849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160830060427569541032146465 120622545320677155774109849)
  ·
    refine ⟨90466908990507866830582387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120622545320677155774109849 90466908990507866830582387)
    ·
      refine ⟨135700363485761800245873581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90466908990507866830582387 135700363485761800245873581)
      ·
        refine ⟨50887636307160675092202593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135700363485761800245873581 50887636307160675092202593)
        ·
          refine ⟨38165727230370506319151945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50887636307160675092202593 38165727230370506319151945)
          ·
            refine ⟨28624295422777879739363959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38165727230370506319151945 28624295422777879739363959)
            ·
              refine ⟨42936443134166819609045939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28624295422777879739363959 42936443134166819609045939)
              ·
                refine ⟨64404664701250229413568909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42936443134166819609045939 64404664701250229413568909)
                ·
                  refine ⟨24151749262968836030088341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64404664701250229413568909 24151749262968836030088341)
                  ·
                    refine ⟨1132113246701664188910391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24151749262968836030088341 1132113246701664188910391)
                    ·
                      rfl

theorem cell23_6614348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 1, 3, 6].length) (baseStart_6614348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6614348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6614348 prefixEnd_6614348 := by exact prefixLift 6614348
  have htrace : WordTrace (prefixWord ++ tailWord_6614348) baseStart_6614348 baseEnd_6614348 := by
    simpa [prefixWord, tailWord_6614348, baseEnd_6614348] using wordTrace_append hprefix tailTrace_6614348
  have hstable : (prefixWord ++ tailWord_6614348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6614348).length < 2 ^ (prefixWord ++ tailWord_6614348).sum := by decide
  have hdescent : baseEnd_6614348 < baseStart_6614348 := by decide
  rcases family_descends (prefixWord ++ tailWord_6614348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6614405 : List Nat := [1, 3, 1, 1, 3, 1, 4, 2, 1, 3, 3]
def baseStart_6614405 : Nat := 118140960795 + 6614405 * 2 ^ 59
def prefixEnd_6614405 : Nat := 4983230072969 + 3 ^ 40 * 6614405 * 2
def baseEnd_6614405 : Nat := 3396369008502298843718411

theorem tailTrace_6614405 : CollatzResearch.WordTrace tailWord_6614405 prefixEnd_6614405 3396369008502298843718411 := by
  unfold tailWord_6614405
  simp only [CollatzResearch.WordTrace]
  refine ⟨241247169602147810283044669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160831446401431873522029779 241247169602147810283044669)
  ·
    refine ⟨90467688600805428856141751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 241247169602147810283044669 90467688600805428856141751)
    ·
      refine ⟨135701532901208143284212627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90467688600805428856141751 135701532901208143284212627)
      ·
        refine ⟨203552299351812214926318941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135701532901208143284212627 203552299351812214926318941)
        ·
          refine ⟨76332112256929580597369603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 203552299351812214926318941 76332112256929580597369603)
          ·
            refine ⟨114498168385394370896054405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76332112256929580597369603 114498168385394370896054405)
            ·
              refine ⟨21468406572261444543010201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 114498168385394370896054405 21468406572261444543010201)
              ·
                refine ⟨16101304929196083407257651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21468406572261444543010201 16101304929196083407257651)
                ·
                  refine ⟨24151957393794125110886477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16101304929196083407257651 24151957393794125110886477)
                  ·
                    refine ⟨9056984022672796916582429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24151957393794125110886477 9056984022672796916582429)
                    ·
                      refine ⟨3396369008502298843718411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9056984022672796916582429 3396369008502298843718411)
                      ·
                        rfl

theorem cell23_6614405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 2, 1, 3, 3].length) (baseStart_6614405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6614405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6614405 prefixEnd_6614405 := by exact prefixLift 6614405
  have htrace : WordTrace (prefixWord ++ tailWord_6614405) baseStart_6614405 baseEnd_6614405 := by
    simpa [prefixWord, tailWord_6614405, baseEnd_6614405] using wordTrace_append hprefix tailTrace_6614405
  have hstable : (prefixWord ++ tailWord_6614405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6614405).length < 2 ^ (prefixWord ++ tailWord_6614405).sum := by decide
  have hdescent : baseEnd_6614405 < baseStart_6614405 := by decide
  rcases family_descends (prefixWord ++ tailWord_6614405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6614449 : List Nat := [1, 2, 2, 4, 1, 1, 4, 2, 1, 3, 2]
def baseStart_6614449 : Nat := 118140960795 + 6614449 * 2 ^ 59
def prefixEnd_6614449 : Nat := 4983230072969 + 3 ^ 40 * 6614449 * 2
def baseEnd_6614449 : Nat := 3396391601651096671568209

theorem tailTrace_6614449 : CollatzResearch.WordTrace tailWord_6614449 prefixEnd_6614449 3396391601651096671568209 := by
  unfold tailWord_6614449
  simp only [CollatzResearch.WordTrace]
  refine ⟨241248774413988405797646401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160832516275992270531764267 241248774413988405797646401)
  ·
    refine ⟨180936580810491304348234801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241248774413988405797646401 180936580810491304348234801)
    ·
      refine ⟨135702435607868478261176101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180936580810491304348234801 135702435607868478261176101)
      ·
        refine ⟨25444206676475339673970519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 135702435607868478261176101 25444206676475339673970519)
        ·
          refine ⟨38166310014713009510955779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25444206676475339673970519 38166310014713009510955779)
          ·
            refine ⟨57249465022069514266433669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38166310014713009510955779 57249465022069514266433669)
            ·
              refine ⟨10734274691638033924956313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57249465022069514266433669 10734274691638033924956313)
              ·
                refine ⟨8050706018728525443717235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10734274691638033924956313 8050706018728525443717235)
                ·
                  refine ⟨12076059028092788165575853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8050706018728525443717235 12076059028092788165575853)
                  ·
                    refine ⟨4528522135534795562090945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12076059028092788165575853 4528522135534795562090945)
                    ·
                      refine ⟨3396391601651096671568209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4528522135534795562090945 3396391601651096671568209)
                      ·
                        rfl

theorem cell23_6614449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 4, 2, 1, 3, 2].length) (baseStart_6614449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6614449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6614449 prefixEnd_6614449 := by exact prefixLift 6614449
  have htrace : WordTrace (prefixWord ++ tailWord_6614449) baseStart_6614449 baseEnd_6614449 := by
    simpa [prefixWord, tailWord_6614449, baseEnd_6614449] using wordTrace_append hprefix tailTrace_6614449
  have hstable : (prefixWord ++ tailWord_6614449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6614449).length < 2 ^ (prefixWord ++ tailWord_6614449).sum := by decide
  have hdescent : baseEnd_6614449 < baseStart_6614449 := by decide
  rcases family_descends (prefixWord ++ tailWord_6614449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6614462 : List Nat := [4, 2, 1, 1, 1, 1, 1, 3, 3, 4, 2]
def baseStart_6614462 : Nat := 118140960795 + 6614462 * 2 ^ 59
def prefixEnd_6614462 : Nat := 4983230072969 + 3 ^ 40 * 6614462 * 2
def baseEnd_6614462 : Nat := 3396398276899605120705649

theorem tailTrace_6614462 : CollatzResearch.WordTrace tailWord_6614462 prefixEnd_6614462 3396398276899605120705649 := by
  unfold tailWord_6614462
  simp only [CollatzResearch.WordTrace]
  refine ⟨30156156070367663627233705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 160832832375294206011913093 30156156070367663627233705)
  ·
    refine ⟨22617117052775747720425279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30156156070367663627233705 22617117052775747720425279)
    ·
      refine ⟨33925675579163621580637919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22617117052775747720425279 33925675579163621580637919)
      ·
        refine ⟨50888513368745432370956879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33925675579163621580637919 50888513368745432370956879)
        ·
          refine ⟨76332770053118148556435319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50888513368745432370956879 76332770053118148556435319)
          ·
            refine ⟨114499155079677222834652979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76332770053118148556435319 114499155079677222834652979)
            ·
              refine ⟨171748732619515834251979469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114499155079677222834652979 171748732619515834251979469)
              ·
                refine ⟨64405774732318437844492301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 171748732619515834251979469 64405774732318437844492301)
                ·
                  refine ⟨24152165524619414191684613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64405774732318437844492301 24152165524619414191684613)
                  ·
                    refine ⟨4528531035866140160940865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24152165524619414191684613 4528531035866140160940865)
                    ·
                      refine ⟨3396398276899605120705649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4528531035866140160940865 3396398276899605120705649)
                      ·
                        rfl

theorem cell23_6614462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 3, 3, 4, 2].length) (baseStart_6614462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6614462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6614462 prefixEnd_6614462 := by exact prefixLift 6614462
  have htrace : WordTrace (prefixWord ++ tailWord_6614462) baseStart_6614462 baseEnd_6614462 := by
    simpa [prefixWord, tailWord_6614462, baseEnd_6614462] using wordTrace_append hprefix tailTrace_6614462
  have hstable : (prefixWord ++ tailWord_6614462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6614462).length < 2 ^ (prefixWord ++ tailWord_6614462).sum := by decide
  have hdescent : baseEnd_6614462 < baseStart_6614462 := by decide
  rcases family_descends (prefixWord ++ tailWord_6614462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6614495 : List Nat := [1, 1, 2, 3, 3, 1, 2, 1, 1, 5, 3]
def baseStart_6614495 : Nat := 118140960795 + 6614495 * 2 ^ 59
def prefixEnd_6614495 : Nat := 4983230072969 + 3 ^ 40 * 6614495 * 2
def baseEnd_6614495 : Nat := 3396415221761203491592997

theorem tailTrace_6614495 : CollatzResearch.WordTrace tailWord_6614495 prefixEnd_6614495 3396415221761203491592997 := by
  unfold tailWord_6614495
  simp only [CollatzResearch.WordTrace]
  refine ⟨241250452171821755653820939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160833634781214503769213959 241250452171821755653820939)
  ·
    refine ⟨361875678257732633480731409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241250452171821755653820939 361875678257732633480731409)
    ·
      refine ⟨271406758693299475110548557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 361875678257732633480731409 271406758693299475110548557)
      ·
        refine ⟨101777534509987303166455709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 271406758693299475110548557 101777534509987303166455709)
        ·
          refine ⟨38166575441245238687420891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101777534509987303166455709 38166575441245238687420891)
          ·
            refine ⟨57249863161867858031131337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38166575441245238687420891 57249863161867858031131337)
            ·
              refine ⟨42937397371400893523348503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57249863161867858031131337 42937397371400893523348503)
              ·
                refine ⟨64406096057101340285022755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42937397371400893523348503 64406096057101340285022755)
                ·
                  refine ⟨96609144085652010427534133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64406096057101340285022755 96609144085652010427534133)
                  ·
                    refine ⟨9057107258029875977581325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 96609144085652010427534133 9057107258029875977581325)
                    ·
                      refine ⟨3396415221761203491592997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9057107258029875977581325 3396415221761203491592997)
                      ·
                        rfl

theorem cell23_6614495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 1, 1, 5, 3].length) (baseStart_6614495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6614495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6614495 prefixEnd_6614495 := by exact prefixLift 6614495
  have htrace : WordTrace (prefixWord ++ tailWord_6614495) baseStart_6614495 baseEnd_6614495 := by
    simpa [prefixWord, tailWord_6614495, baseEnd_6614495] using wordTrace_append hprefix tailTrace_6614495
  have hstable : (prefixWord ++ tailWord_6614495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6614495).length < 2 ^ (prefixWord ++ tailWord_6614495).sum := by decide
  have hdescent : baseEnd_6614495 < baseStart_6614495 := by decide
  rcases family_descends (prefixWord ++ tailWord_6614495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6614525 : List Nat := [1, 4, 1, 1, 1, 4, 1, 2, 1, 2, 5]
def baseStart_6614525 : Nat := 118140960795 + 6614525 * 2 ^ 59
def prefixEnd_6614525 : Nat := 4983230072969 + 3 ^ 40 * 6614525 * 2
def baseEnd_6614525 : Nat := 3396430626180838374217859

theorem tailTrace_6614525 : CollatzResearch.WordTrace tailWord_6614525 prefixEnd_6614525 3396430626180838374217859 := by
  unfold tailWord_6614525
  simp only [CollatzResearch.WordTrace]
  refine ⟨241251546361713070777413029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160834364241142047184942019 241251546361713070777413029)
  ·
    refine ⟨45234664942821200770764943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 241251546361713070777413029 45234664942821200770764943)
    ·
      refine ⟨67851997414231801156147415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45234664942821200770764943 67851997414231801156147415)
      ·
        refine ⟨101777996121347701734221123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67851997414231801156147415 101777996121347701734221123)
        ·
          refine ⟨152666994182021552601331685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101777996121347701734221123 152666994182021552601331685)
          ·
            refine ⟨28625061409129041112749691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 152666994182021552601331685 28625061409129041112749691)
            ·
              refine ⟨42937592113693561669124537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28625061409129041112749691 42937592113693561669124537)
              ·
                refine ⟨32203194085270171251843403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42937592113693561669124537 32203194085270171251843403)
                ·
                  refine ⟨48304791127905256877765105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32203194085270171251843403 48304791127905256877765105)
                  ·
                    refine ⟨36228593345928942658323829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48304791127905256877765105 36228593345928942658323829)
                    ·
                      refine ⟨3396430626180838374217859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36228593345928942658323829 3396430626180838374217859)
                      ·
                        rfl

theorem cell23_6614525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 2, 1, 2, 5].length) (baseStart_6614525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6614525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6614525 prefixEnd_6614525 := by exact prefixLift 6614525
  have htrace : WordTrace (prefixWord ++ tailWord_6614525) baseStart_6614525 baseEnd_6614525 := by
    simpa [prefixWord, tailWord_6614525, baseEnd_6614525] using wordTrace_append hprefix tailTrace_6614525
  have hstable : (prefixWord ++ tailWord_6614525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6614525).length < 2 ^ (prefixWord ++ tailWord_6614525).sum := by decide
  have hdescent : baseEnd_6614525 < baseStart_6614525 := by decide
  rcases family_descends (prefixWord ++ tailWord_6614525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6614562 : List Nat := [3, 3, 1, 1, 1, 1, 3, 1, 5, 4]
def baseStart_6614562 : Nat := 118140960795 + 6614562 * 2 ^ 59
def prefixEnd_6614562 : Nat := 4983230072969 + 3 ^ 40 * 6614562 * 2
def baseEnd_6614562 : Nat := 1132149874988351576485063

theorem tailTrace_6614562 : CollatzResearch.WordTrace tailWord_6614562 prefixEnd_6614562 1132149874988351576485063 := by
  unfold tailWord_6614562
  simp only [CollatzResearch.WordTrace]
  refine ⟨60313223965644756524127485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160835263908386017397673293 60313223965644756524127485)
  ·
    refine ⟨22617458987116783696547807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60313223965644756524127485 22617458987116783696547807)
    ·
      refine ⟨33926188480675175544821711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22617458987116783696547807 33926188480675175544821711)
      ·
        refine ⟨50889282721012763317232567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33926188480675175544821711 50889282721012763317232567)
        ·
          refine ⟨76333924081519144975848851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50889282721012763317232567 76333924081519144975848851)
          ·
            refine ⟨114500886122278717463773277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76333924081519144975848851 114500886122278717463773277)
            ·
              refine ⟨42937832295854519048914979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 114500886122278717463773277 42937832295854519048914979)
              ·
                refine ⟨64406748443781778573372469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42937832295854519048914979 64406748443781778573372469)
                ·
                  refine ⟨6038132666604541741253669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 64406748443781778573372469 6038132666604541741253669)
                  ·
                    refine ⟨1132149874988351576485063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6038132666604541741253669 1132149874988351576485063)
                    ·
                      rfl

theorem cell23_6614562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 1, 5, 4].length) (baseStart_6614562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6614562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6614562 prefixEnd_6614562 := by exact prefixLift 6614562
  have htrace : WordTrace (prefixWord ++ tailWord_6614562) baseStart_6614562 baseEnd_6614562 := by
    simpa [prefixWord, tailWord_6614562, baseEnd_6614562] using wordTrace_append hprefix tailTrace_6614562
  have hstable : (prefixWord ++ tailWord_6614562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6614562).length < 2 ^ (prefixWord ++ tailWord_6614562).sum := by decide
  have hdescent : baseEnd_6614562 < baseStart_6614562 := by decide
  rcases family_descends (prefixWord ++ tailWord_6614562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6614579 : List Nat := [1, 1, 1, 2, 4, 3, 1, 5, 1, 4]
def baseStart_6614579 : Nat := 118140960795 + 6614579 * 2 ^ 59
def prefixEnd_6614579 : Nat := 4983230072969 + 3 ^ 40 * 6614579 * 2
def baseEnd_6614579 : Nat := 1132152784712060387647537

theorem tailTrace_6614579 : CollatzResearch.WordTrace tailWord_6614579 prefixEnd_6614579 1132152784712060387647537 := by
  unfold tailWord_6614579
  simp only [CollatzResearch.WordTrace]
  refine ⟨241253515903517437999878791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160835677269011625333252527 241253515903517437999878791)
  ·
    refine ⟨361880273855276156999818187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241253515903517437999878791 361880273855276156999818187)
    ·
      refine ⟨542820410782914235499727281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 361880273855276156999818187 542820410782914235499727281)
      ·
        refine ⟨407115308087185676624795461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 542820410782914235499727281 407115308087185676624795461)
        ·
          refine ⟨76334120266347314367149149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 407115308087185676624795461 76334120266347314367149149)
          ·
            refine ⟨28625295099880242887680931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76334120266347314367149149 28625295099880242887680931)
            ·
              refine ⟨42937942649820364331521397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28625295099880242887680931 42937942649820364331521397)
              ·
                refine ⟨4025432123420659156080131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42937942649820364331521397 4025432123420659156080131)
                ·
                  refine ⟨6038148185130988734120197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4025432123420659156080131 6038148185130988734120197)
                  ·
                    refine ⟨1132152784712060387647537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6038148185130988734120197 1132152784712060387647537)
                    ·
                      rfl

theorem cell23_6614579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 5, 1, 4].length) (baseStart_6614579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6614579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6614579 prefixEnd_6614579 := by exact prefixLift 6614579
  have htrace : WordTrace (prefixWord ++ tailWord_6614579) baseStart_6614579 baseEnd_6614579 := by
    simpa [prefixWord, tailWord_6614579, baseEnd_6614579] using wordTrace_append hprefix tailTrace_6614579
  have hstable : (prefixWord ++ tailWord_6614579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6614579).length < 2 ^ (prefixWord ++ tailWord_6614579).sum := by decide
  have hdescent : baseEnd_6614579 < baseStart_6614579 := by decide
  rcases family_descends (prefixWord ++ tailWord_6614579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6614629 : List Nat := [1, 3, 1, 3, 3, 1, 2, 1, 1, 5, 2]
def baseStart_6614629 : Nat := 118140960795 + 6614629 * 2 ^ 59
def prefixEnd_6614629 : Nat := 4983230072969 + 3 ^ 40 * 6614629 * 2
def baseEnd_6614629 : Nat := 3396484028168905967317381

theorem tailTrace_6614629 : CollatzResearch.WordTrace tailWord_6614629 prefixEnd_6614629 3396484028168905967317381 := by
  unfold tailWord_6614629
  simp only [CollatzResearch.WordTrace]
  refine ⟨241255339553336296539198941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160836893035557531026132627 241255339553336296539198941)
  ·
    refine ⟨90470752332501111202199603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 241255339553336296539198941 90470752332501111202199603)
    ·
      refine ⟨135706128498751666803299405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90470752332501111202199603 135706128498751666803299405)
      ·
        refine ⟨50889798187031875051237277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135706128498751666803299405 50889798187031875051237277)
        ·
          refine ⟨19083674320136953144213979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50889798187031875051237277 19083674320136953144213979)
          ·
            refine ⟨28625511480205429716320969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19083674320136953144213979 28625511480205429716320969)
            ·
              refine ⟨21469133610154072287240727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28625511480205429716320969 21469133610154072287240727)
              ·
                refine ⟨32203700415231108430861091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21469133610154072287240727 32203700415231108430861091)
                ·
                  refine ⟨48305550622846662646291637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32203700415231108430861091 48305550622846662646291637)
                  ·
                    refine ⟨4528645370891874623089841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48305550622846662646291637 4528645370891874623089841)
                    ·
                      refine ⟨3396484028168905967317381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4528645370891874623089841 3396484028168905967317381)
                      ·
                        rfl

theorem cell23_6614629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 1, 1, 5, 2].length) (baseStart_6614629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6614629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6614629 prefixEnd_6614629 := by exact prefixLift 6614629
  have htrace : WordTrace (prefixWord ++ tailWord_6614629) baseStart_6614629 baseEnd_6614629 := by
    simpa [prefixWord, tailWord_6614629, baseEnd_6614629] using wordTrace_append hprefix tailTrace_6614629
  have hstable : (prefixWord ++ tailWord_6614629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6614629).length < 2 ^ (prefixWord ++ tailWord_6614629).sum := by decide
  have hdescent : baseEnd_6614629 < baseStart_6614629 := by decide
  rcases family_descends (prefixWord ++ tailWord_6614629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6614646 : List Nat := [5, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2]
def baseStart_6614646 : Nat := 118140960795 + 6614646 * 2 ^ 59
def prefixEnd_6614646 : Nat := 4983230072969 + 3 ^ 40 * 6614646 * 2
def baseEnd_6614646 : Nat := 3396492757340032400804803

theorem tailTrace_6614646 : CollatzResearch.WordTrace tailWord_6614646 prefixEnd_6614646 3396492757340032400804803 := by
  unfold tailWord_6614646
  simp only [CollatzResearch.WordTrace]
  refine ⟨15078497474642169277660487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 160837306396183138961711861 15078497474642169277660487)
  ·
    refine ⟨22617746211963253916490731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15078497474642169277660487 22617746211963253916490731)
    ·
      refine ⟨33926619317944880874736097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22617746211963253916490731 33926619317944880874736097)
      ·
        refine ⟨25444964488458660656052073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33926619317944880874736097 25444964488458660656052073)
        ·
          refine ⟨19083723366343995492039055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25444964488458660656052073 19083723366343995492039055)
          ·
            refine ⟨28625585049515993238058583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19083723366343995492039055 28625585049515993238058583)
            ·
              refine ⟨42938377574273989857087875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28625585049515993238058583 42938377574273989857087875)
              ·
                refine ⟨64407566361410984785631813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42938377574273989857087875 64407566361410984785631813)
                ·
                  refine ⟨12076418692764559647305965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64407566361410984785631813 12076418692764559647305965)
                  ·
                    refine ⟨4528657009786709867739737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12076418692764559647305965 4528657009786709867739737)
                    ·
                      refine ⟨3396492757340032400804803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4528657009786709867739737 3396492757340032400804803)
                      ·
                        rfl

theorem cell23_6614646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2].length) (baseStart_6614646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6614646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6614646 prefixEnd_6614646 := by exact prefixLift 6614646
  have htrace : WordTrace (prefixWord ++ tailWord_6614646) baseStart_6614646 baseEnd_6614646 := by
    simpa [prefixWord, tailWord_6614646, baseEnd_6614646] using wordTrace_append hprefix tailTrace_6614646
  have hstable : (prefixWord ++ tailWord_6614646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6614646).length < 2 ^ (prefixWord ++ tailWord_6614646).sum := by decide
  have hdescent : baseEnd_6614646 < baseStart_6614646 := by decide
  rcases family_descends (prefixWord ++ tailWord_6614646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6614665 : List Nat := [1, 2, 1, 1, 4, 1, 3, 10]
def baseStart_6614665 : Nat := 118140960795 + 6614665 * 2 ^ 59
def prefixEnd_6614665 : Nat := 4983230072969 + 3 ^ 40 * 6614665 * 2
def baseEnd_6614665 : Nat := 125796389387869178758045

theorem tailTrace_6614665 : CollatzResearch.WordTrace tailWord_6614665 prefixEnd_6614665 125796389387869178758045 := by
  unfold tailWord_6614665
  simp only [CollatzResearch.WordTrace]
  refine ⟨241256652581205874687509449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160837768387470583125006299 241256652581205874687509449)
  ·
    refine ⟨180942489435904406015632087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241256652581205874687509449 180942489435904406015632087)
    ·
      refine ⟨271413734153856609023448131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180942489435904406015632087 271413734153856609023448131)
      ·
        refine ⟨407120601230784913535172197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271413734153856609023448131 407120601230784913535172197)
        ·
          refine ⟨76335112730772171287844787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 407120601230784913535172197 76335112730772171287844787)
          ·
            refine ⟨114502669096158256931767181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76335112730772171287844787 114502669096158256931767181)
            ·
              refine ⟨42938500911059346349412693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 114502669096158256931767181 42938500911059346349412693)
              ·
                refine ⟨125796389387869178758045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 42938500911059346349412693 125796389387869178758045)
                ·
                  rfl

theorem cell23_6614665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 10].length) (baseStart_6614665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6614665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6614665 prefixEnd_6614665 := by exact prefixLift 6614665
  have htrace : WordTrace (prefixWord ++ tailWord_6614665) baseStart_6614665 baseEnd_6614665 := by
    simpa [prefixWord, tailWord_6614665, baseEnd_6614665] using wordTrace_append hprefix tailTrace_6614665
  have hstable : (prefixWord ++ tailWord_6614665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6614665).length < 2 ^ (prefixWord ++ tailWord_6614665).sum := by decide
  have hdescent : baseEnd_6614665 < baseStart_6614665 := by decide
  rcases family_descends (prefixWord ++ tailWord_6614665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6614676 : List Nat := [2, 4, 2, 2, 2, 1, 1, 1, 3, 1, 4]
def baseStart_6614676 : Nat := 118140960795 + 6614676 * 2 ^ 59
def prefixEnd_6614676 : Nat := 4983230072969 + 3 ^ 40 * 6614676 * 2
def baseEnd_6614676 : Nat := 3396508161759667283429665

theorem tailTrace_6614676 : CollatzResearch.WordTrace tailWord_6614676 prefixEnd_6614676 3396508161759667283429665 := by
  unfold tailWord_6614676
  simp only [CollatzResearch.WordTrace]
  refine ⟨120628526892083011783079941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160838035856110682377439921 120628526892083011783079941)
  ·
    refine ⟨22617848792265564709327489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 120628526892083011783079941 22617848792265564709327489)
    ·
      refine ⟨16963386594199173531995617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22617848792265564709327489 16963386594199173531995617)
      ·
        refine ⟨12722539945649380148996713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16963386594199173531995617 12722539945649380148996713)
        ·
          refine ⟨9541904959237035111747535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12722539945649380148996713 9541904959237035111747535)
          ·
            refine ⟨14312857438855552667621303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9541904959237035111747535 14312857438855552667621303)
            ·
              refine ⟨21469286158283329001431955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14312857438855552667621303 21469286158283329001431955)
              ·
                refine ⟨32203929237424993502147933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21469286158283329001431955 32203929237424993502147933)
                ·
                  refine ⟨12076473464034372563305475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32203929237424993502147933 12076473464034372563305475)
                  ·
                    refine ⟨18114710196051558844958213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12076473464034372563305475 18114710196051558844958213)
                    ·
                      refine ⟨3396508161759667283429665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18114710196051558844958213 3396508161759667283429665)
                      ·
                        rfl

theorem cell23_6614676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_6614676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6614676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6614676 prefixEnd_6614676 := by exact prefixLift 6614676
  have htrace : WordTrace (prefixWord ++ tailWord_6614676) baseStart_6614676 baseEnd_6614676 := by
    simpa [prefixWord, tailWord_6614676, baseEnd_6614676] using wordTrace_append hprefix tailTrace_6614676
  have hstable : (prefixWord ++ tailWord_6614676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6614676).length < 2 ^ (prefixWord ++ tailWord_6614676).sum := by decide
  have hdescent : baseEnd_6614676 < baseStart_6614676 := by decide
  rcases family_descends (prefixWord ++ tailWord_6614676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6614679 : List Nat := [1, 1, 3, 3, 2, 3, 1, 1, 3, 2, 3]
def baseStart_6614679 : Nat := 118140960795 + 6614679 * 2 ^ 59
def prefixEnd_6614679 : Nat := 4983230072969 + 3 ^ 40 * 6614679 * 2
def baseEnd_6614679 : Nat := 3396509702201630771692151

theorem tailTrace_6614679 : CollatzResearch.WordTrace tailWord_6614679 prefixEnd_6614679 3396509702201630771692151 := by
  unfold tailWord_6614679
  simp only [CollatzResearch.WordTrace]
  refine ⟨241257163203155155078519091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160838108802103436719012727 241257163203155155078519091)
  ·
    refine ⟨361885744804732732617778637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241257163203155155078519091 361885744804732732617778637)
    ·
      refine ⟨135707154301774774731666989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 361885744804732732617778637 135707154301774774731666989)
      ·
        refine ⟨50890182863165540524375121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135707154301774774731666989 50890182863165540524375121)
        ·
          refine ⟨38167637147374155393281341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50890182863165540524375121 38167637147374155393281341)
          ·
            refine ⟨14312863930265308272480503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38167637147374155393281341 14312863930265308272480503)
            ·
              refine ⟨21469295895397962408720755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14312863930265308272480503 21469295895397962408720755)
              ·
                refine ⟨32203943843096943613081133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21469295895397962408720755 32203943843096943613081133)
                ·
                  refine ⟨12076478941161353854905425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32203943843096943613081133 12076478941161353854905425)
                  ·
                    refine ⟨9057359205871015391179069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12076478941161353854905425 9057359205871015391179069)
                    ·
                      refine ⟨3396509702201630771692151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9057359205871015391179069 3396509702201630771692151)
                      ·
                        rfl

theorem cell23_6614679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 1, 3, 2, 3].length) (baseStart_6614679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6614679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6614679 prefixEnd_6614679 := by exact prefixLift 6614679
  have htrace : WordTrace (prefixWord ++ tailWord_6614679) baseStart_6614679 baseEnd_6614679 := by
    simpa [prefixWord, tailWord_6614679, baseEnd_6614679] using wordTrace_append hprefix tailTrace_6614679
  have hstable : (prefixWord ++ tailWord_6614679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6614679).length < 2 ^ (prefixWord ++ tailWord_6614679).sum := by decide
  have hdescent : baseEnd_6614679 < baseStart_6614679 := by decide
  rcases family_descends (prefixWord ++ tailWord_6614679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6614689 : List Nat := [1, 2, 3, 3, 2, 2, 1, 2, 1, 2, 4]
def baseStart_6614689 : Nat := 118140960795 + 6614689 * 2 ^ 59
def prefixEnd_6614689 : Nat := 4983230072969 + 3 ^ 40 * 6614689 * 2
def baseEnd_6614689 : Nat := 3396514837008175732567105

theorem tailTrace_6614689 : CollatzResearch.WordTrace tailWord_6614689 prefixEnd_6614689 3396514837008175732567105 := by
  unfold tailWord_6614689
  simp only [CollatzResearch.WordTrace]
  refine ⟨241257527933118926786383121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160838351955412617857588747 241257527933118926786383121)
  ·
    refine ⟨180943145949839195089787341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241257527933118926786383121 180943145949839195089787341)
    ·
      refine ⟨67853679731189698158670253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180943145949839195089787341 67853679731189698158670253)
      ·
        refine ⟨25445129899196136809501345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67853679731189698158670253 25445129899196136809501345)
        ·
          refine ⟨19083847424397102607126009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25445129899196136809501345 19083847424397102607126009)
          ·
            refine ⟨14312885568297826955344507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19083847424397102607126009 14312885568297826955344507)
            ·
              refine ⟨21469328352446740433016761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14312885568297826955344507 21469328352446740433016761)
              ·
                refine ⟨16101996264335055324762571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21469328352446740433016761 16101996264335055324762571)
                ·
                  refine ⟨24152994396502582987143857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16101996264335055324762571 24152994396502582987143857)
                  ·
                    refine ⟨18114745797376937240357893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24152994396502582987143857 18114745797376937240357893)
                    ·
                      refine ⟨3396514837008175732567105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18114745797376937240357893 3396514837008175732567105)
                      ·
                        rfl

theorem cell23_6614689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_6614689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6614689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6614689 prefixEnd_6614689 := by exact prefixLift 6614689
  have htrace : WordTrace (prefixWord ++ tailWord_6614689) baseStart_6614689 baseEnd_6614689 := by
    simpa [prefixWord, tailWord_6614689, baseEnd_6614689] using wordTrace_append hprefix tailTrace_6614689
  have hstable : (prefixWord ++ tailWord_6614689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6614689).length < 2 ^ (prefixWord ++ tailWord_6614689).sum := by decide
  have hdescent : baseEnd_6614689 < baseStart_6614689 := by decide
  rcases family_descends (prefixWord ++ tailWord_6614689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6614719 : List Nat := [1, 1, 2, 2, 2, 3, 1, 1, 5, 3, 2]
def baseStart_6614719 : Nat := 118140960795 + 6614719 * 2 ^ 59
def prefixEnd_6614719 : Nat := 4983230072969 + 3 ^ 40 * 6614719 * 2
def baseEnd_6614719 : Nat := 3396530241427810615191967

theorem tailTrace_6614719 : CollatzResearch.WordTrace tailWord_6614719 prefixEnd_6614719 3396530241427810615191967 := by
  unfold tailWord_6614719
  simp only [CollatzResearch.WordTrace]
  refine ⟨241258622123010241909975211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160839081415340161273316807 241258622123010241909975211)
  ·
    refine ⟨361887933184515362864962817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241258622123010241909975211 361887933184515362864962817)
    ·
      refine ⟨271415949888386522148722113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 361887933184515362864962817 271415949888386522148722113)
      ·
        refine ⟨203561962416289891611541585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 271415949888386522148722113 203561962416289891611541585)
        ·
          refine ⟨152671471812217418708656189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 203561962416289891611541585 152671471812217418708656189)
          ·
            refine ⟨57251801929581532015746071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 152671471812217418708656189 57251801929581532015746071)
            ·
              refine ⟨85877702894372298023619107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57251801929581532015746071 85877702894372298023619107)
              ·
                refine ⟨128816554341558447035428661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85877702894372298023619107 128816554341558447035428661)
                ·
                  refine ⟨12076551969521104409571437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 128816554341558447035428661 12076551969521104409571437)
                  ·
                    refine ⟨4528706988570414153589289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12076551969521104409571437 4528706988570414153589289)
                    ·
                      refine ⟨3396530241427810615191967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4528706988570414153589289 3396530241427810615191967)
                      ·
                        rfl

theorem cell23_6614719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 1, 5, 3, 2].length) (baseStart_6614719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6614719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6614719 prefixEnd_6614719 := by exact prefixLift 6614719
  have htrace : WordTrace (prefixWord ++ tailWord_6614719) baseStart_6614719 baseEnd_6614719 := by
    simpa [prefixWord, tailWord_6614719, baseEnd_6614719] using wordTrace_append hprefix tailTrace_6614719
  have hstable : (prefixWord ++ tailWord_6614719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6614719).length < 2 ^ (prefixWord ++ tailWord_6614719).sum := by decide
  have hdescent : baseEnd_6614719 < baseStart_6614719 := by decide
  rcases family_descends (prefixWord ++ tailWord_6614719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6614752 : List Nat := [2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 5]
def baseStart_6614752 : Nat := 118140960795 + 6614752 * 2 ^ 59
def prefixEnd_6614752 : Nat := 4983230072969 + 3 ^ 40 * 6614752 * 2
def baseEnd_6614752 : Nat := 3396547186289408986079315

theorem tailTrace_6614752 : CollatzResearch.WordTrace tailWord_6614752 prefixEnd_6614752 3396547186289408986079315 := by
  unfold tailWord_6614752
  simp only [CollatzResearch.WordTrace]
  refine ⟨120629912865945344272963255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160839883821260459030617673 120629912865945344272963255)
  ·
    refine ⟨180944869298918016409444883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120629912865945344272963255 180944869298918016409444883)
    ·
      refine ⟨271417303948377024614167325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180944869298918016409444883 271417303948377024614167325)
      ·
        refine ⟨101781488980641384230312747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 271417303948377024614167325 101781488980641384230312747)
        ·
          refine ⟨152672233470962076345469121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101781488980641384230312747 152672233470962076345469121)
          ·
            refine ⟨114504175103221557259101841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152672233470962076345469121 114504175103221557259101841)
            ·
              refine ⟨85878131327416167944326381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114504175103221557259101841 85878131327416167944326381)
              ·
                refine ⟨32204299247781062979122393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85878131327416167944326381 32204299247781062979122393)
                ·
                  refine ⟨24153224435835797234341795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32204299247781062979122393 24153224435835797234341795)
                  ·
                    refine ⟨36229836653753695851512693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24153224435835797234341795 36229836653753695851512693)
                    ·
                      refine ⟨3396547186289408986079315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36229836653753695851512693 3396547186289408986079315)
                      ·
                        rfl

theorem cell23_6614752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 5].length) (baseStart_6614752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6614752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6614752 prefixEnd_6614752 := by exact prefixLift 6614752
  have htrace : WordTrace (prefixWord ++ tailWord_6614752) baseStart_6614752 baseEnd_6614752 := by
    simpa [prefixWord, tailWord_6614752, baseEnd_6614752] using wordTrace_append hprefix tailTrace_6614752
  have hstable : (prefixWord ++ tailWord_6614752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6614752).length < 2 ^ (prefixWord ++ tailWord_6614752).sum := by decide
  have hdescent : baseEnd_6614752 < baseStart_6614752 := by decide
  rcases family_descends (prefixWord ++ tailWord_6614752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6614753 : List Nat := [1, 2, 3, 1, 5, 1, 1, 3, 1, 3, 2]
def baseStart_6614753 : Nat := 118140960795 + 6614753 * 2 ^ 59
def prefixEnd_6614753 : Nat := 4983230072969 + 3 ^ 40 * 6614753 * 2
def baseEnd_6614753 : Nat := 3396547699770063482166811

theorem tailTrace_6614753 : CollatzResearch.WordTrace tailWord_6614753 prefixEnd_6614753 3396547699770063482166811 := by
  unfold tailWord_6614753
  simp only [CollatzResearch.WordTrace]
  refine ⟨241259862204887065716712913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160839908136591377144475275 241259862204887065716712913)
  ·
    refine ⟨180944896653665299287534685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241259862204887065716712913 180944896653665299287534685)
    ·
      refine ⟨67854336245124487232825507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180944896653665299287534685 67854336245124487232825507)
      ·
        refine ⟨101781504367686730849238261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67854336245124487232825507 101781504367686730849238261)
        ·
          refine ⟨9542016034470631017116087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 101781504367686730849238261 9542016034470631017116087)
          ·
            refine ⟨14313024051705946525674131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9542016034470631017116087 14313024051705946525674131)
            ·
              refine ⟨21469536077558919788511197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14313024051705946525674131 21469536077558919788511197)
              ·
                refine ⟨8051076029084594920691699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21469536077558919788511197 8051076029084594920691699)
                ·
                  refine ⟨12076614043626892381037549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8051076029084594920691699 12076614043626892381037549)
                  ·
                    refine ⟨4528730266360084642889081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12076614043626892381037549 4528730266360084642889081)
                    ·
                      refine ⟨3396547699770063482166811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4528730266360084642889081 3396547699770063482166811)
                      ·
                        rfl

theorem cell23_6614753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 3, 1, 3, 2].length) (baseStart_6614753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6614753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6614753 prefixEnd_6614753 := by exact prefixLift 6614753
  have htrace : WordTrace (prefixWord ++ tailWord_6614753) baseStart_6614753 baseEnd_6614753 := by
    simpa [prefixWord, tailWord_6614753, baseEnd_6614753] using wordTrace_append hprefix tailTrace_6614753
  have hstable : (prefixWord ++ tailWord_6614753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6614753).length < 2 ^ (prefixWord ++ tailWord_6614753).sum := by decide
  have hdescent : baseEnd_6614753 < baseStart_6614753 := by decide
  rcases family_descends (prefixWord ++ tailWord_6614753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6614856 : List Nat := [2, 1, 3, 1, 1, 5, 2, 1, 2, 1, 4]
def baseStart_6614856 : Nat := 118140960795 + 6614856 * 2 ^ 59
def prefixEnd_6614856 : Nat := 4983230072969 + 3 ^ 40 * 6614856 * 2
def baseEnd_6614856 : Nat := 3396600588277476579178837

theorem tailTrace_6614856 : CollatzResearch.WordTrace tailWord_6614856 prefixEnd_6614856 3396600588277476579178837 := by
  unfold tailWord_6614856
  simp only [CollatzResearch.WordTrace]
  refine ⟨120631809461756957153856211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160842412615675942871808281 120631809461756957153856211)
  ·
    refine ⟨180947714192635435730784317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120631809461756957153856211 180947714192635435730784317)
    ·
      refine ⟨67855392822238288399044119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180947714192635435730784317 67855392822238288399044119)
      ·
        refine ⟨101783089233357432598566179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67855392822238288399044119 101783089233357432598566179)
        ·
          refine ⟨152674633850036148897849269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101783089233357432598566179 152674633850036148897849269)
          ·
            refine ⟨14313246923440888959173369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 152674633850036148897849269 14313246923440888959173369)
            ·
              refine ⟨10734935192580666719380027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14313246923440888959173369 10734935192580666719380027)
              ·
                refine ⟨16102402788871000079070041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10734935192580666719380027 16102402788871000079070041)
                ·
                  refine ⟨12076802091653250059302531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16102402788871000079070041 12076802091653250059302531)
                  ·
                    refine ⟨18115203137479875088953797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12076802091653250059302531 18115203137479875088953797)
                    ·
                      refine ⟨3396600588277476579178837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18115203137479875088953797 3396600588277476579178837)
                      ·
                        rfl

theorem cell23_6614856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 2, 1, 2, 1, 4].length) (baseStart_6614856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6614856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6614856 prefixEnd_6614856 := by exact prefixLift 6614856
  have htrace : WordTrace (prefixWord ++ tailWord_6614856) baseStart_6614856 baseEnd_6614856 := by
    simpa [prefixWord, tailWord_6614856, baseEnd_6614856] using wordTrace_append hprefix tailTrace_6614856
  have hstable : (prefixWord ++ tailWord_6614856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6614856).length < 2 ^ (prefixWord ++ tailWord_6614856).sum := by decide
  have hdescent : baseEnd_6614856 < baseStart_6614856 := by decide
  rcases family_descends (prefixWord ++ tailWord_6614856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6614879 : List Nat := [1, 1, 2, 3, 1, 4, 1, 4, 6]
def baseStart_6614879 : Nat := 118140960795 + 6614879 * 2 ^ 59
def prefixEnd_6614879 : Nat := 4983230072969 + 3 ^ 40 * 6614879 * 2
def baseEnd_6614879 : Nat := 377401377592503332132359

theorem tailTrace_6614879 : CollatzResearch.WordTrace tailWord_6614879 prefixEnd_6614879 377401377592503332132359 := by
  unfold tailWord_6614879
  simp only [CollatzResearch.WordTrace]
  refine ⟨241264457802430589235799691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160842971868287059490533127 241264457802430589235799691)
  ·
    refine ⟨361896686703645883853699537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241264457802430589235799691 361896686703645883853699537)
    ·
      refine ⟨271422515027734412890274653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 361896686703645883853699537 271422515027734412890274653)
      ·
        refine ⟨101783443135400404833852995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 271422515027734412890274653 101783443135400404833852995)
        ·
          refine ⟨152675164703100607250779493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101783443135400404833852995 152675164703100607250779493)
          ·
            refine ⟨28626593381831363859521155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 152675164703100607250779493 28626593381831363859521155)
            ·
              refine ⟨42939890072747045789281733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28626593381831363859521155 42939890072747045789281733)
              ·
                refine ⟨8051229388640071085490325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42939890072747045789281733 8051229388640071085490325)
                ·
                  refine ⟨377401377592503332132359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8051229388640071085490325 377401377592503332132359)
                  ·
                    rfl

theorem cell23_6614879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 4, 6].length) (baseStart_6614879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6614879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6614879 prefixEnd_6614879 := by exact prefixLift 6614879
  have htrace : WordTrace (prefixWord ++ tailWord_6614879) baseStart_6614879 baseEnd_6614879 := by
    simpa [prefixWord, tailWord_6614879, baseEnd_6614879] using wordTrace_append hprefix tailTrace_6614879
  have hstable : (prefixWord ++ tailWord_6614879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6614879).length < 2 ^ (prefixWord ++ tailWord_6614879).sum := by decide
  have hdescent : baseEnd_6614879 < baseStart_6614879 := by decide
  rcases family_descends (prefixWord ++ tailWord_6614879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6614890 : List Nat := [3, 1, 3, 4, 1, 1, 1, 1, 2, 4, 2]
def baseStart_6614890 : Nat := 118140960795 + 6614890 * 2 ^ 59
def prefixEnd_6614890 : Nat := 4983230072969 + 3 ^ 40 * 6614890 * 2
def baseEnd_6614890 : Nat := 3396618046619729446153681

theorem tailTrace_6614890 : CollatzResearch.WordTrace tailWord_6614890 prefixEnd_6614890 3396618046619729446153681 := by
  unfold tailWord_6614890
  simp only [CollatzResearch.WordTrace]
  refine ⟨60316214751347684528612531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160843239336927158742966749 60316214751347684528612531)
  ·
    refine ⟨90474322127021526792918797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60316214751347684528612531 90474322127021526792918797)
    ·
      refine ⟨33927870797633072547344549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90474322127021526792918797 33927870797633072547344549)
      ·
        refine ⟨6361475774556201102627103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33927870797633072547344549 6361475774556201102627103)
        ·
          refine ⟨9542213661834301653940655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6361475774556201102627103 9542213661834301653940655)
          ·
            refine ⟨14313320492751452480910983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9542213661834301653940655 14313320492751452480910983)
            ·
              refine ⟨21469980739127178721366475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14313320492751452480910983 21469980739127178721366475)
              ·
                refine ⟨32204971108690768082049713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21469980739127178721366475 32204971108690768082049713)
                ·
                  refine ⟨24153728331518076061537285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32204971108690768082049713 24153728331518076061537285)
                  ·
                    refine ⟨4528824062159639261538241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24153728331518076061537285 4528824062159639261538241)
                    ·
                      refine ⟨3396618046619729446153681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4528824062159639261538241 3396618046619729446153681)
                      ·
                        rfl

theorem cell23_6614890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_6614890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6614890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6614890 prefixEnd_6614890 := by exact prefixLift 6614890
  have htrace : WordTrace (prefixWord ++ tailWord_6614890) baseStart_6614890 baseEnd_6614890 := by
    simpa [prefixWord, tailWord_6614890, baseEnd_6614890] using wordTrace_append hprefix tailTrace_6614890
  have hstable : (prefixWord ++ tailWord_6614890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6614890).length < 2 ^ (prefixWord ++ tailWord_6614890).sum := by decide
  have hdescent : baseEnd_6614890 < baseStart_6614890 := by decide
  rcases family_descends (prefixWord ++ tailWord_6614890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6614906 : List Nat := [3, 1, 1, 1, 1, 1, 5, 1, 5, 1, 3]
def baseStart_6614906 : Nat := 118140960795 + 6614906 * 2 ^ 59
def prefixEnd_6614906 : Nat := 4983230072969 + 3 ^ 40 * 6614906 * 2
def baseEnd_6614906 : Nat := 3396626262310201383553607

theorem tailTrace_6614906 : CollatzResearch.WordTrace tailWord_6614906 prefixEnd_6614906 3396626262310201383553607 := by
  unfold tailWord_6614906
  simp only [CollatzResearch.WordTrace]
  refine ⟨60316360643333193211758143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160843628382221848564688381 60316360643333193211758143)
  ·
    refine ⟨90474540964999789817637215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60316360643333193211758143 90474540964999789817637215)
    ·
      refine ⟨135711811447499684726455823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90474540964999789817637215 135711811447499684726455823)
      ·
        refine ⟨203567717171249527089683735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135711811447499684726455823 203567717171249527089683735)
        ·
          refine ⟨305351575756874290634525603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203567717171249527089683735 305351575756874290634525603)
          ·
            refine ⟨458027363635311435951788405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 305351575756874290634525603 458027363635311435951788405)
            ·
              refine ⟨42940065340810447120480163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 458027363635311435951788405 42940065340810447120480163)
              ·
                refine ⟨64410098011215670680720245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42940065340810447120480163 64410098011215670680720245)
                ·
                  refine ⟨6038446688551469126317523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 64410098011215670680720245 6038446688551469126317523)
                  ·
                    refine ⟨9057670032827203689476285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6038446688551469126317523 9057670032827203689476285)
                    ·
                      refine ⟨3396626262310201383553607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9057670032827203689476285 3396626262310201383553607)
                      ·
                        rfl

theorem cell23_6614906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 1, 5, 1, 3].length) (baseStart_6614906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6614906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6614906 prefixEnd_6614906 := by exact prefixLift 6614906
  have htrace : WordTrace (prefixWord ++ tailWord_6614906) baseStart_6614906 baseEnd_6614906 := by
    simpa [prefixWord, tailWord_6614906, baseEnd_6614906] using wordTrace_append hprefix tailTrace_6614906
  have hstable : (prefixWord ++ tailWord_6614906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6614906).length < 2 ^ (prefixWord ++ tailWord_6614906).sum := by decide
  have hdescent : baseEnd_6614906 < baseStart_6614906 := by decide
  rcases family_descends (prefixWord ++ tailWord_6614906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6614910 : List Nat := [4, 2, 3, 1, 1, 1, 3, 1, 2, 2, 3]
def baseStart_6614910 : Nat := 118140960795 + 6614910 * 2 ^ 59
def prefixEnd_6614910 : Nat := 4983230072969 + 3 ^ 40 * 6614910 * 2
def baseEnd_6614910 : Nat := 3396628316232819367903589

theorem tailTrace_6614910 : CollatzResearch.WordTrace tailWord_6614910 prefixEnd_6614910 3396628316232819367903589 := by
  unfold tailWord_6614910
  simp only [CollatzResearch.WordTrace]
  refine ⟨30158198558164785191272273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 160843725643545521020118789 30158198558164785191272273)
  ·
    refine ⟨22618648918623588893454205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30158198558164785191272273 22618648918623588893454205)
    ·
      refine ⟨8481993344483845835045327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22618648918623588893454205 8481993344483845835045327)
      ·
        refine ⟨12722990016725768752567991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8481993344483845835045327 12722990016725768752567991)
        ·
          refine ⟨19084485025088653128851987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12722990016725768752567991 19084485025088653128851987)
          ·
            refine ⟨28626727537632979693277981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19084485025088653128851987 28626727537632979693277981)
            ·
              refine ⟨10735022826612367384979243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28626727537632979693277981 10735022826612367384979243)
              ·
                refine ⟨16102534239918551077468865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10735022826612367384979243 16102534239918551077468865)
                ·
                  refine ⟨12076900679938913308101649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16102534239918551077468865 12076900679938913308101649)
                  ·
                    refine ⟨9057675509954184981076237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12076900679938913308101649 9057675509954184981076237)
                    ·
                      refine ⟨3396628316232819367903589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9057675509954184981076237 3396628316232819367903589)
                      ·
                        rfl

theorem cell23_6614910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_6614910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6614910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6614910 prefixEnd_6614910 := by exact prefixLift 6614910
  have htrace : WordTrace (prefixWord ++ tailWord_6614910) baseStart_6614910 baseEnd_6614910 := by
    simpa [prefixWord, tailWord_6614910, baseEnd_6614910] using wordTrace_append hprefix tailTrace_6614910
  have hstable : (prefixWord ++ tailWord_6614910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6614910).length < 2 ^ (prefixWord ++ tailWord_6614910).sum := by decide
  have hdescent : baseEnd_6614910 < baseStart_6614910 := by decide
  rcases family_descends (prefixWord ++ tailWord_6614910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6614940 : List Nat := [2, 2, 3, 3, 1, 2, 2, 1, 3, 1, 3]
def baseStart_6614940 : Nat := 118140960795 + 6614940 * 2 ^ 59
def prefixEnd_6614940 : Nat := 4983230072969 + 3 ^ 40 * 6614940 * 2
def baseEnd_6614940 : Nat := 3396643720652454250528451

theorem tailTrace_6614940 : CollatzResearch.WordTrace tailWord_6614940 prefixEnd_6614940 3396643720652454250528451 := by
  unfold tailWord_6614940
  simp only [CollatzResearch.WordTrace]
  refine ⟨120633341327604798326885137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160844455103473064435846849 120633341327604798326885137)
  ·
    refine ⟨90475005995703598745163853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120633341327604798326885137 90475005995703598745163853)
    ·
      refine ⟨33928127248388849529436445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90475005995703598745163853 33928127248388849529436445)
      ·
        refine ⟨12723047718145818573538667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33928127248388849529436445 12723047718145818573538667)
        ·
          refine ⟨19084571577218727860308001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12723047718145818573538667 19084571577218727860308001)
          ·
            refine ⟨14313428682914045895231001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19084571577218727860308001 14313428682914045895231001)
            ·
              refine ⟨10735071512185534421423251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14313428682914045895231001 10735071512185534421423251)
              ·
                refine ⟨16102607268278301632134877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10735071512185534421423251 16102607268278301632134877)
                ·
                  refine ⟨6038477725604363112050579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16102607268278301632134877 6038477725604363112050579)
                  ·
                    refine ⟨9057716588406544668075869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6038477725604363112050579 9057716588406544668075869)
                    ·
                      refine ⟨3396643720652454250528451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9057716588406544668075869 3396643720652454250528451)
                      ·
                        rfl

theorem cell23_6614940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_6614940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6614940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6614940 prefixEnd_6614940 := by exact prefixLift 6614940
  have htrace : WordTrace (prefixWord ++ tailWord_6614940) baseStart_6614940 baseEnd_6614940 := by
    simpa [prefixWord, tailWord_6614940, baseEnd_6614940] using wordTrace_append hprefix tailTrace_6614940
  have hstable : (prefixWord ++ tailWord_6614940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6614940).length < 2 ^ (prefixWord ++ tailWord_6614940).sum := by decide
  have hdescent : baseEnd_6614940 < baseStart_6614940 := by decide
  rcases family_descends (prefixWord ++ tailWord_6614940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6614959 : List Nat := [1, 1, 2, 1, 2, 2, 5, 1, 1, 1, 6]
def baseStart_6614959 : Nat := 118140960795 + 6614959 * 2 ^ 59
def prefixEnd_6614959 : Nat := 4983230072969 + 3 ^ 40 * 6614959 * 2
def baseEnd_6614959 : Nat := 3396653476784889676190863

theorem tailTrace_6614959 : CollatzResearch.WordTrace tailWord_6614959 prefixEnd_6614959 3396653476784889676190863 := by
  unfold tailWord_6614959
  simp only [CollatzResearch.WordTrace]
  refine ⟨241267375642140762898711931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160844917094760508599141287 241267375642140762898711931)
  ·
    refine ⟨361901063463211144348067897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241267375642140762898711931 361901063463211144348067897)
    ·
      refine ⟨271425797597408358261050923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 361901063463211144348067897 271425797597408358261050923)
      ·
        refine ⟨407138696396112537391576385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271425797597408358261050923 407138696396112537391576385)
        ·
          refine ⟨305354022297084403043682289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 407138696396112537391576385 305354022297084403043682289)
          ·
            refine ⟨229015516722813302282761717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 305354022297084403043682289 229015516722813302282761717)
            ·
              refine ⟨21470204692763747089008911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 229015516722813302282761717 21470204692763747089008911)
              ·
                refine ⟨32205307039145620633513367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21470204692763747089008911 32205307039145620633513367)
                ·
                  refine ⟨48307960558718430950270051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32205307039145620633513367 48307960558718430950270051)
                  ·
                    refine ⟨72461940838077646425405077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48307960558718430950270051 72461940838077646425405077)
                    ·
                      refine ⟨3396653476784889676190863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72461940838077646425405077 3396653476784889676190863)
                      ·
                        rfl

theorem cell23_6614959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 1, 1, 1, 6].length) (baseStart_6614959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6614959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6614959 prefixEnd_6614959 := by exact prefixLift 6614959
  have htrace : WordTrace (prefixWord ++ tailWord_6614959) baseStart_6614959 baseEnd_6614959 := by
    simpa [prefixWord, tailWord_6614959, baseEnd_6614959] using wordTrace_append hprefix tailTrace_6614959
  have hstable : (prefixWord ++ tailWord_6614959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6614959).length < 2 ^ (prefixWord ++ tailWord_6614959).sum := by decide
  have hdescent : baseEnd_6614959 < baseStart_6614959 := by decide
  rcases family_descends (prefixWord ++ tailWord_6614959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6614963 : List Nat := [1, 1, 1, 2, 3, 1, 3, 4, 3, 2, 2]
def baseStart_6614963 : Nat := 118140960795 + 6614963 * 2 ^ 59
def prefixEnd_6614963 : Nat := 4983230072969 + 3 ^ 40 * 6614963 * 2
def baseEnd_6614963 : Nat := 3396655530707507660540845

theorem tailTrace_6614963 : CollatzResearch.WordTrace tailWord_6614963 prefixEnd_6614963 3396655530707507660540845 := by
  unfold tailWord_6614963
  simp only [CollatzResearch.WordTrace]
  refine ⟨241267521534126271581857543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160845014356084181054571695 241267521534126271581857543)
  ·
    refine ⟨361901282301189407372786315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241267521534126271581857543 361901282301189407372786315)
    ·
      refine ⟨542851923451784111059179473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 361901282301189407372786315 542851923451784111059179473)
      ·
        refine ⟨407138942588838083294384605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 542851923451784111059179473 407138942588838083294384605)
        ·
          refine ⟨152677103470814281235394227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 407138942588838083294384605 152677103470814281235394227)
          ·
            refine ⟨229015655206221421853091341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152677103470814281235394227 229015655206221421853091341)
            ·
              refine ⟨85880870702333033194909253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 229015655206221421853091341 85880870702333033194909253)
              ·
                refine ⟨16102663256687443724045485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 85880870702333033194909253 16102663256687443724045485)
                ·
                  refine ⟨6038498721257791396517057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16102663256687443724045485 6038498721257791396517057)
                  ·
                    refine ⟨4528874040943343547387793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6038498721257791396517057 4528874040943343547387793)
                    ·
                      refine ⟨3396655530707507660540845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4528874040943343547387793 3396655530707507660540845)
                      ·
                        rfl

theorem cell23_6614963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 4, 3, 2, 2].length) (baseStart_6614963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6614963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6614963 prefixEnd_6614963 := by exact prefixLift 6614963
  have htrace : WordTrace (prefixWord ++ tailWord_6614963) baseStart_6614963 baseEnd_6614963 := by
    simpa [prefixWord, tailWord_6614963, baseEnd_6614963] using wordTrace_append hprefix tailTrace_6614963
  have hstable : (prefixWord ++ tailWord_6614963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6614963).length < 2 ^ (prefixWord ++ tailWord_6614963).sum := by decide
  have hdescent : baseEnd_6614963 < baseStart_6614963 := by decide
  rcases family_descends (prefixWord ++ tailWord_6614963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6614969 : List Nat := [1, 2, 1, 4, 2, 1, 3, 9]
def baseStart_6614969 : Nat := 118140960795 + 6614969 * 2 ^ 59
def prefixEnd_6614969 : Nat := 4983230072969 + 3 ^ 40 * 6614969 * 2
def baseEnd_6614969 : Nat := 125802170799682764335771

theorem tailTrace_6614969 : CollatzResearch.WordTrace tailWord_6614969 prefixEnd_6614969 125802170799682764335771 := by
  unfold tailWord_6614969
  simp only [CollatzResearch.WordTrace]
  refine ⟨241267740372104534606575961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160845160248069689737717307 241267740372104534606575961)
  ·
    refine ⟨180950805279078400954931971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241267740372104534606575961 180950805279078400954931971)
    ·
      refine ⟨271426207918617601432397957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180950805279078400954931971 271426207918617601432397957)
      ·
        refine ⟨50892413984740800268574617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 271426207918617601432397957 50892413984740800268574617)
        ·
          refine ⟨38169310488555600201430963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50892413984740800268574617 38169310488555600201430963)
          ·
            refine ⟨57253965732833400302146445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38169310488555600201430963 57253965732833400302146445)
            ·
              refine ⟨21470237149812525113304917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57253965732833400302146445 21470237149812525113304917)
              ·
                refine ⟨125802170799682764335771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21470237149812525113304917 125802170799682764335771)
                ·
                  rfl

theorem cell23_6614969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 9].length) (baseStart_6614969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6614969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6614969 prefixEnd_6614969 := by exact prefixLift 6614969
  have htrace : WordTrace (prefixWord ++ tailWord_6614969) baseStart_6614969 baseEnd_6614969 := by
    simpa [prefixWord, tailWord_6614969, baseEnd_6614969] using wordTrace_append hprefix tailTrace_6614969
  have hstable : (prefixWord ++ tailWord_6614969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6614969).length < 2 ^ (prefixWord ++ tailWord_6614969).sum := by decide
  have hdescent : baseEnd_6614969 < baseStart_6614969 := by decide
  rcases family_descends (prefixWord ++ tailWord_6614969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6614997 : List Nat := [1, 3, 2, 3, 2, 3, 1, 1, 3, 2, 2]
def baseStart_6614997 : Nat := 118140960795 + 6614997 * 2 ^ 59
def prefixEnd_6614997 : Nat := 4983230072969 + 3 ^ 40 * 6614997 * 2
def baseEnd_6614997 : Nat := 3396672989049760527515689

theorem tailTrace_6614997 : CollatzResearch.WordTrace tailWord_6614997 prefixEnd_6614997 3396672989049760527515689 := by
  unfold tailWord_6614997
  simp only [CollatzResearch.WordTrace]
  refine ⟨241268761616003095388595245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160845841077335396925730163 241268761616003095388595245)
  ·
    refine ⟨90475785606001160770723217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 241268761616003095388595245 90475785606001160770723217)
    ·
      refine ⟨67856839204500870578042413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90475785606001160770723217 67856839204500870578042413)
      ·
        refine ⟨25446314701687826466765905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67856839204500870578042413 25446314701687826466765905)
        ·
          refine ⟨19084736026265869850074429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25446314701687826466765905 19084736026265869850074429)
          ·
            refine ⟨7156776009849701193777911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19084736026265869850074429 7156776009849701193777911)
            ·
              refine ⟨10735164014774551790666867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7156776009849701193777911 10735164014774551790666867)
              ·
                refine ⟨16102746022161827686000301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10735164014774551790666867 16102746022161827686000301)
                ·
                  refine ⟨6038529758310685382250113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16102746022161827686000301 6038529758310685382250113)
                  ·
                    refine ⟨4528897318733014036687585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6038529758310685382250113 4528897318733014036687585)
                    ·
                      refine ⟨3396672989049760527515689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4528897318733014036687585 3396672989049760527515689)
                      ·
                        rfl

theorem cell23_6614997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 1, 1, 3, 2, 2].length) (baseStart_6614997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6614997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6614997 prefixEnd_6614997 := by exact prefixLift 6614997
  have htrace : WordTrace (prefixWord ++ tailWord_6614997) baseStart_6614997 baseEnd_6614997 := by
    simpa [prefixWord, tailWord_6614997, baseEnd_6614997] using wordTrace_append hprefix tailTrace_6614997
  have hstable : (prefixWord ++ tailWord_6614997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6614997).length < 2 ^ (prefixWord ++ tailWord_6614997).sum := by decide
  have hdescent : baseEnd_6614997 < baseStart_6614997 := by decide
  rcases family_descends (prefixWord ++ tailWord_6614997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6614999 : List Nat := [1, 1, 3, 2, 1, 1, 4, 1, 2, 7]
def baseStart_6614999 : Nat := 118140960795 + 6614999 * 2 ^ 59
def prefixEnd_6614999 : Nat := 4983230072969 + 3 ^ 40 * 6614999 * 2
def baseEnd_6614999 : Nat := 1132224672003689839896893

theorem tailTrace_6614999 : CollatzResearch.WordTrace tailWord_6614999 prefixEnd_6614999 1132224672003689839896893 := by
  unfold tailWord_6614999
  simp only [CollatzResearch.WordTrace]
  refine ⟨241268834561995849730168051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160845889707997233153445367 241268834561995849730168051)
  ·
    refine ⟨361903251842993774595252077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241268834561995849730168051 361903251842993774595252077)
    ·
      refine ⟨135713719441122665473219529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 361903251842993774595252077 135713719441122665473219529)
      ·
        refine ⟨101785289580841999104914647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135713719441122665473219529 101785289580841999104914647)
        ·
          refine ⟨152677934371262998657371971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101785289580841999104914647 152677934371262998657371971)
          ·
            refine ⟨229016901556894497986057957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152677934371262998657371971 229016901556894497986057957)
            ·
              refine ⟨42940669041917718372385867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 229016901556894497986057957 42940669041917718372385867)
              ·
                refine ⟨64411003562876577558578801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42940669041917718372385867 64411003562876577558578801)
                ·
                  refine ⟨48308252672157433168934101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64411003562876577558578801 48308252672157433168934101)
                  ·
                    refine ⟨1132224672003689839896893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48308252672157433168934101 1132224672003689839896893)
                    ·
                      rfl

theorem cell23_6614999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 1, 2, 7].length) (baseStart_6614999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6614999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6614999 prefixEnd_6614999 := by exact prefixLift 6614999
  have htrace : WordTrace (prefixWord ++ tailWord_6614999) baseStart_6614999 baseEnd_6614999 := by
    simpa [prefixWord, tailWord_6614999, baseEnd_6614999] using wordTrace_append hprefix tailTrace_6614999
  have hstable : (prefixWord ++ tailWord_6614999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6614999).length < 2 ^ (prefixWord ++ tailWord_6614999).sum := by decide
  have hdescent : baseEnd_6614999 < baseStart_6614999 := by decide
  rcases family_descends (prefixWord ++ tailWord_6614999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6615023 : List Nat := [1, 1, 2, 1, 4, 2, 3, 1, 3, 3, 2]
def baseStart_6615023 : Nat := 118140960795 + 6615023 * 2 ^ 59
def prefixEnd_6615023 : Nat := 4983230072969 + 3 ^ 40 * 6615023 * 2
def baseEnd_6615023 : Nat := 3396686339546777425790569

theorem tailTrace_6615023 : CollatzResearch.WordTrace tailWord_6615023 prefixEnd_6615023 3396686339546777425790569 := by
  unfold tailWord_6615023
  simp only [CollatzResearch.WordTrace]
  refine ⟨241269709913908901829041723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160846473275939267886027815 241269709913908901829041723)
  ·
    refine ⟨361904564870863352743562585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241269709913908901829041723 361904564870863352743562585)
    ·
      refine ⟨271428423653147514557671939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 361904564870863352743562585 271428423653147514557671939)
      ·
        refine ⟨407142635479721271836507909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271428423653147514557671939 407142635479721271836507909)
        ·
          refine ⟨76339244152447738469345233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 407142635479721271836507909 76339244152447738469345233)
          ·
            refine ⟨57254433114335803852008925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76339244152447738469345233 57254433114335803852008925)
            ·
              refine ⟨21470412417875926444503347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57254433114335803852008925 21470412417875926444503347)
              ·
                refine ⟨32205618626813889666755021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21470412417875926444503347 32205618626813889666755021)
                ·
                  refine ⟨12077106985055208625033133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32205618626813889666755021 12077106985055208625033133)
                  ·
                    refine ⟨4528915119395703234387425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12077106985055208625033133 4528915119395703234387425)
                    ·
                      refine ⟨3396686339546777425790569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4528915119395703234387425 3396686339546777425790569)
                      ·
                        rfl

theorem cell23_6615023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 1, 3, 3, 2].length) (baseStart_6615023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6615023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6615023 prefixEnd_6615023 := by exact prefixLift 6615023
  have htrace : WordTrace (prefixWord ++ tailWord_6615023) baseStart_6615023 baseEnd_6615023 := by
    simpa [prefixWord, tailWord_6615023, baseEnd_6615023] using wordTrace_append hprefix tailTrace_6615023
  have hstable : (prefixWord ++ tailWord_6615023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6615023).length < 2 ^ (prefixWord ++ tailWord_6615023).sum := by decide
  have hdescent : baseEnd_6615023 < baseStart_6615023 := by decide
  rcases family_descends (prefixWord ++ tailWord_6615023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6615030 : List Nat := [5, 1, 1, 1, 4, 1, 1, 2, 1, 3, 3]
def baseStart_6615030 : Nat := 118140960795 + 6615030 * 2 ^ 59
def prefixEnd_6615030 : Nat := 4983230072969 + 3 ^ 40 * 6615030 * 2
def baseEnd_6615030 : Nat := 3396689933911358898403037

theorem tailTrace_6615030 : CollatzResearch.WordTrace tailWord_6615030 prefixEnd_6615030 3396689933911358898403037 := by
  unfold tailWord_6615030
  simp only [CollatzResearch.WordTrace]
  refine ⟨15079372826555221376534159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 160846643483255694683031029 15079372826555221376534159)
  ·
    refine ⟨22619059239832832064801239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15079372826555221376534159 22619059239832832064801239)
    ·
      refine ⟨33928588859749248097201859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22619059239832832064801239 33928588859749248097201859)
      ·
        refine ⟨50892883289623872145802789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33928588859749248097201859 50892883289623872145802789)
        ·
          refine ⟨9542415616804476027338023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50892883289623872145802789 9542415616804476027338023)
          ·
            refine ⟨14313623425206714041007035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9542415616804476027338023 14313623425206714041007035)
            ·
              refine ⟨21470435137810071061510553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14313623425206714041007035 21470435137810071061510553)
              ·
                refine ⟨16102826353357553296132915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21470435137810071061510553 16102826353357553296132915)
                ·
                  refine ⟨24154239530036329944199373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16102826353357553296132915 24154239530036329944199373)
                  ·
                    refine ⟨9057839823763623729074765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24154239530036329944199373 9057839823763623729074765)
                    ·
                      refine ⟨3396689933911358898403037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9057839823763623729074765 3396689933911358898403037)
                      ·
                        rfl

theorem cell23_6615030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 2, 1, 3, 3].length) (baseStart_6615030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6615030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6615030 prefixEnd_6615030 := by exact prefixLift 6615030
  have htrace : WordTrace (prefixWord ++ tailWord_6615030) baseStart_6615030 baseEnd_6615030 := by
    simpa [prefixWord, tailWord_6615030, baseEnd_6615030] using wordTrace_append hprefix tailTrace_6615030
  have hstable : (prefixWord ++ tailWord_6615030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6615030).length < 2 ^ (prefixWord ++ tailWord_6615030).sum := by decide
  have hdescent : baseEnd_6615030 < baseStart_6615030 := by decide
  rcases family_descends (prefixWord ++ tailWord_6615030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6615049 : List Nat := [1, 2, 1, 1, 3, 1, 1, 1, 1, 5, 6]
def baseStart_6615049 : Nat := 118140960795 + 6615049 * 2 ^ 59
def prefixEnd_6615049 : Nat := 4983230072969 + 3 ^ 40 * 6615049 * 2
def baseEnd_6615049 : Nat := 3396699690043794324065449

theorem tailTrace_6615049 : CollatzResearch.WordTrace tailWord_6615049 prefixEnd_6615049 3396699690043794324065449 := by
  unfold tailWord_6615049
  simp only [CollatzResearch.WordTrace]
  refine ⟨241270658211814708269488201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160847105474543138846325467 241270658211814708269488201)
  ·
    refine ⟨180952993658861031202116151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241270658211814708269488201 180952993658861031202116151)
    ·
      refine ⟨271429490488291546803174227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180952993658861031202116151 271429490488291546803174227)
      ·
        refine ⟨407144235732437320204761341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271429490488291546803174227 407144235732437320204761341)
        ·
          refine ⟨152679088399663995076785503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 407144235732437320204761341 152679088399663995076785503)
          ·
            refine ⟨229018632599495992615178255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152679088399663995076785503 229018632599495992615178255)
            ·
              refine ⟨343527948899243988922767383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 229018632599495992615178255 343527948899243988922767383)
              ·
                refine ⟨515291923348865983384151075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 343527948899243988922767383 515291923348865983384151075)
                ·
                  refine ⟨772937885023298975076226613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 515291923348865983384151075 772937885023298975076226613)
                  ·
                    refine ⟨72462926720934278913396245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 772937885023298975076226613 72462926720934278913396245)
                    ·
                      refine ⟨3396699690043794324065449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72462926720934278913396245 3396699690043794324065449)
                      ·
                        rfl

theorem cell23_6615049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 5, 6].length) (baseStart_6615049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6615049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6615049 prefixEnd_6615049 := by exact prefixLift 6615049
  have htrace : WordTrace (prefixWord ++ tailWord_6615049) baseStart_6615049 baseEnd_6615049 := by
    simpa [prefixWord, tailWord_6615049, baseEnd_6615049] using wordTrace_append hprefix tailTrace_6615049
  have hstable : (prefixWord ++ tailWord_6615049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6615049).length < 2 ^ (prefixWord ++ tailWord_6615049).sum := by decide
  have hdescent : baseEnd_6615049 < baseStart_6615049 := by decide
  rcases family_descends (prefixWord ++ tailWord_6615049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6615063 : List Nat := [1, 1, 3, 5, 2, 1, 1, 1, 2, 6]
def baseStart_6615063 : Nat := 118140960795 + 6615063 * 2 ^ 59
def prefixEnd_6615063 : Nat := 4983230072969 + 3 ^ 40 * 6615063 * 2
def baseEnd_6615063 : Nat := 1132235626257652423096795

theorem tailTrace_6615063 : CollatzResearch.WordTrace tailWord_6615063 prefixEnd_6615063 1132235626257652423096795 := by
  unfold tailWord_6615063
  simp only [CollatzResearch.WordTrace]
  refine ⟨241271168833763988660497843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160847445889175992440331895 241271168833763988660497843)
  ·
    refine ⟨361906753250645982990746765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241271168833763988660497843 361906753250645982990746765)
    ·
      refine ⟨135715032468992243621530037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 361906753250645982990746765 135715032468992243621530037)
      ·
        refine ⟨12723284293968022839518441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 135715032468992243621530037 12723284293968022839518441)
        ·
          refine ⟨9542463220476017129638831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12723284293968022839518441 9542463220476017129638831)
          ·
            refine ⟨14313694830714025694458247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9542463220476017129638831 14313694830714025694458247)
            ·
              refine ⟨21470542246071038541687371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14313694830714025694458247 21470542246071038541687371)
              ·
                refine ⟨32205813369106557812531057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21470542246071038541687371 32205813369106557812531057)
                ·
                  refine ⟨24154360026829918359398293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32205813369106557812531057 24154360026829918359398293)
                  ·
                    refine ⟨1132235626257652423096795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24154360026829918359398293 1132235626257652423096795)
                    ·
                      rfl

theorem cell23_6615063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 1, 2, 6].length) (baseStart_6615063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6615063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6615063 prefixEnd_6615063 := by exact prefixLift 6615063
  have htrace : WordTrace (prefixWord ++ tailWord_6615063) baseStart_6615063 baseEnd_6615063 := by
    simpa [prefixWord, tailWord_6615063, baseEnd_6615063] using wordTrace_append hprefix tailTrace_6615063
  have hstable : (prefixWord ++ tailWord_6615063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6615063).length < 2 ^ (prefixWord ++ tailWord_6615063).sum := by decide
  have hdescent : baseEnd_6615063 < baseStart_6615063 := by decide
  rcases family_descends (prefixWord ++ tailWord_6615063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6615066 : List Nat := [3, 1, 1, 3, 1, 3, 1, 1, 1, 4, 4]
def baseStart_6615066 : Nat := 118140960795 + 6615066 * 2 ^ 59
def prefixEnd_6615066 : Nat := 4983230072969 + 3 ^ 40 * 6615066 * 2
def baseEnd_6615066 : Nat := 3396708419214920757552871

theorem tailTrace_6615066 : CollatzResearch.WordTrace tailWord_6615066 prefixEnd_6615066 3396708419214920757552871 := by
  unfold tailWord_6615066
  simp only [CollatzResearch.WordTrace]
  refine ⟨60317819563188280043214263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160847518835168746781904701 60317819563188280043214263)
  ·
    refine ⟨90476729344782420064821395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60317819563188280043214263 90476729344782420064821395)
    ·
      refine ⟨135715094017173630097232093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90476729344782420064821395 135715094017173630097232093)
      ·
        refine ⟨50893160256440111286462035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135715094017173630097232093 50893160256440111286462035)
        ·
          refine ⟨76339740384660166929693053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50893160256440111286462035 76339740384660166929693053)
          ·
            refine ⟨28627402644247562598634895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76339740384660166929693053 28627402644247562598634895)
            ·
              refine ⟨42941103966371343897952343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28627402644247562598634895 42941103966371343897952343)
              ·
                refine ⟨64411655949557015846928515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42941103966371343897952343 64411655949557015846928515)
                ·
                  refine ⟨96617483924335523770392773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64411655949557015846928515 96617483924335523770392773)
                  ·
                    refine ⟨18115778235812910706948645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 96617483924335523770392773 18115778235812910706948645)
                    ·
                      refine ⟨3396708419214920757552871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18115778235812910706948645 3396708419214920757552871)
                      ·
                        rfl

theorem cell23_6615066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 1, 1, 4, 4].length) (baseStart_6615066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6615066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6615066 prefixEnd_6615066 := by exact prefixLift 6615066
  have htrace : WordTrace (prefixWord ++ tailWord_6615066) baseStart_6615066 baseEnd_6615066 := by
    simpa [prefixWord, tailWord_6615066, baseEnd_6615066] using wordTrace_append hprefix tailTrace_6615066
  have hstable : (prefixWord ++ tailWord_6615066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6615066).length < 2 ^ (prefixWord ++ tailWord_6615066).sum := by decide
  have hdescent : baseEnd_6615066 < baseStart_6615066 := by decide
  rcases family_descends (prefixWord ++ tailWord_6615066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6615093 : List Nat := [1, 3, 3, 1, 1, 1, 3, 5, 5]
def baseStart_6615093 : Nat := 118140960795 + 6615093 * 2 ^ 59
def prefixEnd_6615093 : Nat := 4983230072969 + 3 ^ 40 * 6615093 * 2
def baseEnd_6615093 : Nat := 377413587021399127990583

theorem tailTrace_6615093 : CollatzResearch.WordTrace tailWord_6615093 prefixEnd_6615093 377413587021399127990583 := by
  unfold tailWord_6615093
  simp only [CollatzResearch.WordTrace]
  refine ⟨241272263023655303784089933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160848175349103535856059955 241272263023655303784089933)
  ·
    refine ⟨90477098633870738919033725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 241272263023655303784089933 90477098633870738919033725)
    ·
      refine ⟨33928911987701527094637647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90477098633870738919033725 33928911987701527094637647)
      ·
        refine ⟨50893367981552290641956471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33928911987701527094637647 50893367981552290641956471)
        ·
          refine ⟨76340051972328435962934707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50893367981552290641956471 76340051972328435962934707)
          ·
            refine ⟨114510077958492653944402061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76340051972328435962934707 114510077958492653944402061)
            ·
              refine ⟨42941279234434745229150773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 114510077958492653944402061 42941279234434745229150773)
              ·
                refine ⟨4025744928228257365232885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42941279234434745229150773 4025744928228257365232885)
                ·
                  refine ⟨377413587021399127990583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4025744928228257365232885 377413587021399127990583)
                  ·
                    rfl

theorem cell23_6615093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 5, 5].length) (baseStart_6615093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6615093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6615093 prefixEnd_6615093 := by exact prefixLift 6615093
  have htrace : WordTrace (prefixWord ++ tailWord_6615093) baseStart_6615093 baseEnd_6615093 := by
    simpa [prefixWord, tailWord_6615093, baseEnd_6615093] using wordTrace_append hprefix tailTrace_6615093
  have hstable : (prefixWord ++ tailWord_6615093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6615093).length < 2 ^ (prefixWord ++ tailWord_6615093).sum := by decide
  have hdescent : baseEnd_6615093 < baseStart_6615093 := by decide
  rcases family_descends (prefixWord ++ tailWord_6615093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6615110 : List Nat := [6, 1, 1, 1, 1, 1, 4, 1, 7]
def baseStart_6615110 : Nat := 118140960795 + 6615110 * 2 ^ 59
def prefixEnd_6615110 : Nat := 4983230072969 + 3 ^ 40 * 6615110 * 2
def baseEnd_6615110 : Nat := 377414556929302065044741

theorem tailTrace_6615110 : CollatzResearch.WordTrace tailWord_6615110 prefixEnd_6615110 377414556929302065044741 := by
  unfold tailWord_6615110
  simp only [CollatzResearch.WordTrace]
  refine ⟨7539777595768553615233087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 160848588709729143791639189 7539777595768553615233087)
  ·
    refine ⟨11309666393652830422849631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7539777595768553615233087 11309666393652830422849631)
    ·
      refine ⟨16964499590479245634274447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11309666393652830422849631 16964499590479245634274447)
      ·
        refine ⟨25446749385718868451411671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16964499590479245634274447 25446749385718868451411671)
        ·
          refine ⟨38170124078578302677117507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25446749385718868451411671 38170124078578302677117507)
          ·
            refine ⟨57255186117867454015676261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38170124078578302677117507 57255186117867454015676261)
            ·
              refine ⟨10735347397100147627939299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57255186117867454015676261 10735347397100147627939299)
              ·
                refine ⟨16103021095650221441908949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10735347397100147627939299 16103021095650221441908949)
                ·
                  refine ⟨377414556929302065044741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16103021095650221441908949 377414556929302065044741)
                  ·
                    rfl

theorem cell23_6615110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 4, 1, 7].length) (baseStart_6615110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6615110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6615110 prefixEnd_6615110 := by exact prefixLift 6615110
  have htrace : WordTrace (prefixWord ++ tailWord_6615110) baseStart_6615110 baseEnd_6615110 := by
    simpa [prefixWord, tailWord_6615110, baseEnd_6615110] using wordTrace_append hprefix tailTrace_6615110
  have hstable : (prefixWord ++ tailWord_6615110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6615110).length < 2 ^ (prefixWord ++ tailWord_6615110).sum := by decide
  have hdescent : baseEnd_6615110 < baseStart_6615110 := by decide
  rcases family_descends (prefixWord ++ tailWord_6615110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6615116 : List Nat := [2, 2, 1, 3, 1, 1, 2, 3, 1, 2, 5]
def baseStart_6615116 : Nat := 118140960795 + 6615116 * 2 ^ 59
def prefixEnd_6615116 : Nat := 4983230072969 + 3 ^ 40 * 6615116 * 2
def baseEnd_6615116 : Nat := 3396734093247645561927641

theorem tailTrace_6615116 : CollatzResearch.WordTrace tailWord_6615116 prefixEnd_6615116 3396734093247645561927641 := by
  unfold tailWord_6615116
  simp only [CollatzResearch.WordTrace]
  refine ⟨120636550951285989356088601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160848734601714652474784801 120636550951285989356088601)
  ·
    refine ⟨90477413213464492017066451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120636550951285989356088601 90477413213464492017066451)
    ·
      refine ⟨135716119820196738025599677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90477413213464492017066451 135716119820196738025599677)
      ·
        refine ⟨50893544932573776759599879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135716119820196738025599677 50893544932573776759599879)
        ·
          refine ⟨76340317398860665139399819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50893544932573776759599879 76340317398860665139399819)
          ·
            refine ⟨114510476098290997709099729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76340317398860665139399819 114510476098290997709099729)
            ·
              refine ⟨85882857073718248281824797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114510476098290997709099729 85882857073718248281824797)
              ·
                refine ⟨32206071402644343105684299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85882857073718248281824797 32206071402644343105684299)
                ·
                  refine ⟨48309107103966514658526449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32206071402644343105684299 48309107103966514658526449)
                  ·
                    refine ⟨36231830327974885993894837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48309107103966514658526449 36231830327974885993894837)
                    ·
                      refine ⟨3396734093247645561927641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36231830327974885993894837 3396734093247645561927641)
                      ·
                        rfl

theorem cell23_6615116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 3, 1, 2, 5].length) (baseStart_6615116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6615116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6615116 prefixEnd_6615116 := by exact prefixLift 6615116
  have htrace : WordTrace (prefixWord ++ tailWord_6615116) baseStart_6615116 baseEnd_6615116 := by
    simpa [prefixWord, tailWord_6615116, baseEnd_6615116] using wordTrace_append hprefix tailTrace_6615116
  have hstable : (prefixWord ++ tailWord_6615116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6615116).length < 2 ^ (prefixWord ++ tailWord_6615116).sum := by decide
  have hdescent : baseEnd_6615116 < baseStart_6615116 := by decide
  rcases family_descends (prefixWord ++ tailWord_6615116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6615143 : List Nat := [1, 1, 5, 1, 1, 2, 2, 3, 2, 1, 4]
def baseStart_6615143 : Nat := 118140960795 + 6615143 * 2 ^ 59
def prefixEnd_6615143 : Nat := 4983230072969 + 3 ^ 40 * 6615143 * 2
def baseEnd_6615143 : Nat := 3396747957225316956290017

theorem tailTrace_6615143 : CollatzResearch.WordTrace tailWord_6615143 prefixEnd_6615143 3396747957225316956290017 := by
  unfold tailWord_6615143
  simp only [CollatzResearch.WordTrace]
  refine ⟨241274086673474162323410083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160849391115649441548940055 241274086673474162323410083)
  ·
    refine ⟨361911130010211243485115125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241274086673474162323410083 361911130010211243485115125)
    ·
      refine ⟨33929168438457304076729543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 361911130010211243485115125 33929168438457304076729543)
      ·
        refine ⟨50893752657685956115094315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33929168438457304076729543 50893752657685956115094315)
        ·
          refine ⟨76340628986528934172641473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50893752657685956115094315 76340628986528934172641473)
          ·
            refine ⟨57255471739896700629481105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76340628986528934172641473 57255471739896700629481105)
            ·
              refine ⟨42941603804922525472110829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57255471739896700629481105 42941603804922525472110829)
              ·
                refine ⟨16103101426845947052041561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42941603804922525472110829 16103101426845947052041561)
                ·
                  refine ⟨12077326070134460289031171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16103101426845947052041561 12077326070134460289031171)
                  ·
                    refine ⟨18115989105201690433546757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12077326070134460289031171 18115989105201690433546757)
                    ·
                      refine ⟨3396747957225316956290017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18115989105201690433546757 3396747957225316956290017)
                      ·
                        rfl

theorem cell23_6615143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 3, 2, 1, 4].length) (baseStart_6615143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6615143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6615143 prefixEnd_6615143 := by exact prefixLift 6615143
  have htrace : WordTrace (prefixWord ++ tailWord_6615143) baseStart_6615143 baseEnd_6615143 := by
    simpa [prefixWord, tailWord_6615143, baseEnd_6615143] using wordTrace_append hprefix tailTrace_6615143
  have hstable : (prefixWord ++ tailWord_6615143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6615143).length < 2 ^ (prefixWord ++ tailWord_6615143).sum := by decide
  have hdescent : baseEnd_6615143 < baseStart_6615143 := by decide
  rcases family_descends (prefixWord ++ tailWord_6615143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6615227 : List Nat := [1, 1, 1, 1, 1, 2, 7, 4, 1, 1, 3]
def baseStart_6615227 : Nat := 118140960795 + 6615227 * 2 ^ 59
def prefixEnd_6615227 : Nat := 4983230072969 + 3 ^ 40 * 6615227 * 2
def baseEnd_6615227 : Nat := 3396791089600294627639631

theorem tailTrace_6615227 : CollatzResearch.WordTrace tailWord_6615227 prefixEnd_6615227 3396791089600294627639631 := by
  unfold tailWord_6615227
  simp only [CollatzResearch.WordTrace]
  refine ⟨241277150405169844669467935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160851433603446563112978623 241277150405169844669467935)
  ·
    refine ⟨361915725607754767004201903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241277150405169844669467935 361915725607754767004201903)
    ·
      refine ⟨542873588411632150506302855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 361915725607754767004201903 542873588411632150506302855)
      ·
        refine ⟨814310382617448225759454283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 542873588411632150506302855 814310382617448225759454283)
        ·
          refine ⟨1221465573926172338639181425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 814310382617448225759454283 1221465573926172338639181425)
          ·
            refine ⟨916099180444629253979386069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1221465573926172338639181425 916099180444629253979386069)
            ·
              refine ⟨21471074541670998140141861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 916099180444629253979386069 21471074541670998140141861)
              ·
                refine ⟨4025826476563312151276599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21471074541670998140141861 4025826476563312151276599)
                ·
                  refine ⟨6038739714844968226914899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4025826476563312151276599 6038739714844968226914899)
                  ·
                    refine ⟨9058109572267452340372349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6038739714844968226914899 9058109572267452340372349)
                    ·
                      refine ⟨3396791089600294627639631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9058109572267452340372349 3396791089600294627639631)
                      ·
                        rfl

theorem cell23_6615227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 4, 1, 1, 3].length) (baseStart_6615227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6615227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6615227 prefixEnd_6615227 := by exact prefixLift 6615227
  have htrace : WordTrace (prefixWord ++ tailWord_6615227) baseStart_6615227 baseEnd_6615227 := by
    simpa [prefixWord, tailWord_6615227, baseEnd_6615227] using wordTrace_append hprefix tailTrace_6615227
  have hstable : (prefixWord ++ tailWord_6615227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6615227).length < 2 ^ (prefixWord ++ tailWord_6615227).sum := by decide
  have hdescent : baseEnd_6615227 < baseStart_6615227 := by decide
  rcases family_descends (prefixWord ++ tailWord_6615227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6615243 : List Nat := [1, 1, 1, 1, 3, 2, 6, 1, 1, 6]
def baseStart_6615243 : Nat := 118140960795 + 6615243 * 2 ^ 59
def prefixEnd_6615243 : Nat := 4983230072969 + 3 ^ 40 * 6615243 * 2
def baseEnd_6615243 : Nat := 1132266435096922188346519

theorem tailTrace_6615243 : CollatzResearch.WordTrace tailWord_6615243 prefixEnd_6615243 1132266435096922188346519 := by
  unfold tailWord_6615243
  simp only [CollatzResearch.WordTrace]
  refine ⟨241277733973111879402050383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160851822648741252934700255 241277733973111879402050383)
  ·
    refine ⟨361916600959667819103075575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241277733973111879402050383 361916600959667819103075575)
    ·
      refine ⟨542874901439501728654613363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 361916600959667819103075575 542874901439501728654613363)
      ·
        refine ⟨814312352159252592981920045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 542874901439501728654613363 814312352159252592981920045)
        ·
          refine ⟨305367132059719722368220017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 814312352159252592981920045 305367132059719722368220017)
          ·
            refine ⟨229025349044789791776165013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 305367132059719722368220017 229025349044789791776165013)
            ·
              refine ⟨10735563236474521489507735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 229025349044789791776165013 10735563236474521489507735)
              ·
                refine ⟨16103344854711782234261603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10735563236474521489507735 16103344854711782234261603)
                ·
                  refine ⟨24155017282067673351392405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16103344854711782234261603 24155017282067673351392405)
                  ·
                    refine ⟨1132266435096922188346519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24155017282067673351392405 1132266435096922188346519)
                    ·
                      rfl

theorem cell23_6615243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 6, 1, 1, 6].length) (baseStart_6615243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6615243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6615243 prefixEnd_6615243 := by exact prefixLift 6615243
  have htrace : WordTrace (prefixWord ++ tailWord_6615243) baseStart_6615243 baseEnd_6615243 := by
    simpa [prefixWord, tailWord_6615243, baseEnd_6615243] using wordTrace_append hprefix tailTrace_6615243
  have hstable : (prefixWord ++ tailWord_6615243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6615243).length < 2 ^ (prefixWord ++ tailWord_6615243).sum := by decide
  have hdescent : baseEnd_6615243 < baseStart_6615243 := by decide
  rcases family_descends (prefixWord ++ tailWord_6615243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6615244 : List Nat := [2, 2, 1, 6, 1, 1, 1, 2, 3, 1, 3]
def baseStart_6615244 : Nat := 118140960795 + 6615244 * 2 ^ 59
def prefixEnd_6615244 : Nat := 4983230072969 + 3 ^ 40 * 6615244 * 2
def baseEnd_6615244 : Nat := 3396799818771421061127053

theorem tailTrace_6615244 : CollatzResearch.WordTrace tailWord_6615244 prefixEnd_6615244 3396799818771421061127053 := by
  unfold tailWord_6615244
  simp only [CollatzResearch.WordTrace]
  refine ⟨120638885223054128286418393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160851846964072171048557857 120638885223054128286418393)
  ·
    refine ⟨90479163917290596214813795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120638885223054128286418393 90479163917290596214813795)
    ·
      refine ⟨135718745875935894322220693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90479163917290596214813795 135718745875935894322220693)
      ·
        refine ⟨6361816212934495046354095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 135718745875935894322220693 6361816212934495046354095)
        ·
          refine ⟨9542724319401742569531143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6361816212934495046354095 9542724319401742569531143)
          ·
            refine ⟨14314086479102613854296715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9542724319401742569531143 14314086479102613854296715)
            ·
              refine ⟨21471129718653920781445073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14314086479102613854296715 21471129718653920781445073)
              ·
                refine ⟨16103347288990440586083805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21471129718653920781445073 16103347288990440586083805)
                ·
                  refine ⟨6038755233371415219781427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16103347288990440586083805 6038755233371415219781427)
                  ·
                    refine ⟨9058132850057122829672141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6038755233371415219781427 9058132850057122829672141)
                    ·
                      refine ⟨3396799818771421061127053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9058132850057122829672141 3396799818771421061127053)
                      ·
                        rfl

theorem cell23_6615244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_6615244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6615244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6615244 prefixEnd_6615244 := by exact prefixLift 6615244
  have htrace : WordTrace (prefixWord ++ tailWord_6615244) baseStart_6615244 baseEnd_6615244 := by
    simpa [prefixWord, tailWord_6615244, baseEnd_6615244] using wordTrace_append hprefix tailTrace_6615244
  have hstable : (prefixWord ++ tailWord_6615244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6615244).length < 2 ^ (prefixWord ++ tailWord_6615244).sum := by decide
  have hdescent : baseEnd_6615244 < baseStart_6615244 := by decide
  rcases family_descends (prefixWord ++ tailWord_6615244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6615250 : List Nat := [3, 2, 2, 2, 1, 2, 2, 1, 3, 1, 4]
def baseStart_6615250 : Nat := 118140960795 + 6615250 * 2 ^ 59
def prefixEnd_6615250 : Nat := 4983230072969 + 3 ^ 40 * 6615250 * 2
def baseEnd_6615250 : Nat := 3396802899655348037652025

theorem tailTrace_6615250 : CollatzResearch.WordTrace tailWord_6615250 prefixEnd_6615250 3396802899655348037652025 := by
  unfold tailWord_6615250
  simp only [CollatzResearch.WordTrace]
  refine ⟨60319497321021629899388801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160851992856057679731703469 60319497321021629899388801)
  ·
    refine ⟨45239622990766222424541601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60319497321021629899388801 45239622990766222424541601)
    ·
      refine ⟨33929717243074666818406201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45239622990766222424541601 33929717243074666818406201)
      ·
        refine ⟨25447287932306000113804651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33929717243074666818406201 25447287932306000113804651)
        ·
          refine ⟨38170931898459000170706977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25447287932306000113804651 38170931898459000170706977)
          ·
            refine ⟨28628198923844250128030233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38170931898459000170706977 28628198923844250128030233)
            ·
              refine ⟨21471149192883187596022675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28628198923844250128030233 21471149192883187596022675)
              ·
                refine ⟨32206723789324781394034013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21471149192883187596022675 32206723789324781394034013)
                ·
                  refine ⟨12077521420996793022762755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32206723789324781394034013 12077521420996793022762755)
                  ·
                    refine ⟨18116282131495189534144133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12077521420996793022762755 18116282131495189534144133)
                    ·
                      refine ⟨3396802899655348037652025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18116282131495189534144133 3396802899655348037652025)
                      ·
                        rfl

theorem cell23_6615250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_6615250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6615250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6615250 prefixEnd_6615250 := by exact prefixLift 6615250
  have htrace : WordTrace (prefixWord ++ tailWord_6615250) baseStart_6615250 baseEnd_6615250 := by
    simpa [prefixWord, tailWord_6615250, baseEnd_6615250] using wordTrace_append hprefix tailTrace_6615250
  have hstable : (prefixWord ++ tailWord_6615250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6615250).length < 2 ^ (prefixWord ++ tailWord_6615250).sum := by decide
  have hdescent : baseEnd_6615250 < baseStart_6615250 := by decide
  rcases family_descends (prefixWord ++ tailWord_6615250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6615254 : List Nat := [5, 2, 1, 2, 1, 2, 1, 1, 1, 5, 2]
def baseStart_6615254 : Nat := 118140960795 + 6615254 * 2 ^ 59
def prefixEnd_6615254 : Nat := 4983230072969 + 3 ^ 40 * 6615254 * 2
def baseEnd_6615254 : Nat := 3396804953577966022002007

theorem tailTrace_6615254 : CollatzResearch.WordTrace tailWord_6615254 prefixEnd_6615254 3396804953577966022002007 := by
  unfold tailWord_6615254
  simp only [CollatzResearch.WordTrace]
  refine ⟨15079883448504501767543801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 160852090117381352187133877 15079883448504501767543801)
  ·
    refine ⟨11309912586378376325657851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15079883448504501767543801 11309912586378376325657851)
    ·
      refine ⟨16964868879567564488486777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11309912586378376325657851 16964868879567564488486777)
      ·
        refine ⟨12723651659675673366365083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16964868879567564488486777 12723651659675673366365083)
        ·
          refine ⟨19085477489513510049547625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12723651659675673366365083 19085477489513510049547625)
          ·
            refine ⟨14314108117135132537160719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19085477489513510049547625 14314108117135132537160719)
            ·
              refine ⟨21471162175702698805741079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14314108117135132537160719 21471162175702698805741079)
              ·
                refine ⟨32206743263554048208611619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21471162175702698805741079 32206743263554048208611619)
                ·
                  refine ⟨48310114895331072312917429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32206743263554048208611619 48310114895331072312917429)
                  ·
                    refine ⟨4529073271437288029336009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48310114895331072312917429 4529073271437288029336009)
                    ·
                      refine ⟨3396804953577966022002007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4529073271437288029336009 3396804953577966022002007)
                      ·
                        rfl

theorem cell23_6615254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 1, 1, 5, 2].length) (baseStart_6615254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6615254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6615254 prefixEnd_6615254 := by exact prefixLift 6615254
  have htrace : WordTrace (prefixWord ++ tailWord_6615254) baseStart_6615254 baseEnd_6615254 := by
    simpa [prefixWord, tailWord_6615254, baseEnd_6615254] using wordTrace_append hprefix tailTrace_6615254
  have hstable : (prefixWord ++ tailWord_6615254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6615254).length < 2 ^ (prefixWord ++ tailWord_6615254).sum := by decide
  have hdescent : baseEnd_6615254 < baseStart_6615254 := by decide
  rcases family_descends (prefixWord ++ tailWord_6615254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6615261 : List Nat := [1, 4, 3, 2, 1, 2, 2, 3, 1, 1, 3]
def baseStart_6615261 : Nat := 118140960795 + 6615261 * 2 ^ 59
def prefixEnd_6615261 : Nat := 4983230072969 + 3 ^ 40 * 6615261 * 2
def baseEnd_6615261 : Nat := 3396808547942547494614475

theorem tailTrace_6615261 : CollatzResearch.WordTrace tailWord_6615261 prefixEnd_6615261 3396808547942547494614475 := by
  unfold tailWord_6615261
  simp only [CollatzResearch.WordTrace]
  refine ⟨241278390487046668476205637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160852260324697778984137091 241278390487046668476205637)
  ·
    refine ⟨45239698216321250339288557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 241278390487046668476205637 45239698216321250339288557)
    ·
      refine ⟨16964886831120468877233209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45239698216321250339288557 16964886831120468877233209)
      ·
        refine ⟨12723665123340351657924907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16964886831120468877233209 12723665123340351657924907)
        ·
          refine ⟨19085497685010527486887361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12723665123340351657924907 19085497685010527486887361)
          ·
            refine ⟨14314123263757895615165521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19085497685010527486887361 14314123263757895615165521)
            ·
              refine ⟨10735592447818421711374141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14314123263757895615165521 10735592447818421711374141)
              ·
                refine ⟨4025847167931908141765303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10735592447818421711374141 4025847167931908141765303)
                ·
                  refine ⟨6038770751897862212647955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4025847167931908141765303 6038770751897862212647955)
                  ·
                    refine ⟨9058156127846793318971933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6038770751897862212647955 9058156127846793318971933)
                    ·
                      refine ⟨3396808547942547494614475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9058156127846793318971933 3396808547942547494614475)
                      ·
                        rfl

theorem cell23_6615261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 2, 3, 1, 1, 3].length) (baseStart_6615261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6615261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6615261 prefixEnd_6615261 := by exact prefixLift 6615261
  have htrace : WordTrace (prefixWord ++ tailWord_6615261) baseStart_6615261 baseEnd_6615261 := by
    simpa [prefixWord, tailWord_6615261, baseEnd_6615261] using wordTrace_append hprefix tailTrace_6615261
  have hstable : (prefixWord ++ tailWord_6615261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6615261).length < 2 ^ (prefixWord ++ tailWord_6615261).sum := by decide
  have hdescent : baseEnd_6615261 < baseStart_6615261 := by decide
  rcases family_descends (prefixWord ++ tailWord_6615261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6615277 : List Nat := [1, 5, 1, 2, 3, 1, 1, 1, 4, 4]
def baseStart_6615277 : Nat := 118140960795 + 6615277 * 2 ^ 59
def prefixEnd_6615277 : Nat := 4983230072969 + 3 ^ 40 * 6615277 * 2
def baseEnd_6615277 : Nat := 1132272254544339810671467

theorem tailTrace_6615277 : CollatzResearch.WordTrace tailWord_6615277 prefixEnd_6615277 1132272254544339810671467 := by
  unfold tailWord_6615277
  simp only [CollatzResearch.WordTrace]
  refine ⟨241278974054988703208788085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160852649369992468805858723 241278974054988703208788085)
  ·
    refine ⟨22619903817655190925823883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 241278974054988703208788085 22619903817655190925823883)
    ·
      refine ⟨33929855726482786388735825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22619903817655190925823883 33929855726482786388735825)
      ·
        refine ⟨25447391794862089791551869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33929855726482786388735825 25447391794862089791551869)
        ·
          refine ⟨9542771923073283671831951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25447391794862089791551869 9542771923073283671831951)
          ·
            refine ⟨14314157884609925507747927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9542771923073283671831951 14314157884609925507747927)
            ·
              refine ⟨21471236826914888261621891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14314157884609925507747927 21471236826914888261621891)
              ·
                refine ⟨32206855240372332392432837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21471236826914888261621891 32206855240372332392432837)
                ·
                  refine ⟨6038785357569812323581157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32206855240372332392432837 6038785357569812323581157)
                  ·
                    refine ⟨1132272254544339810671467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6038785357569812323581157 1132272254544339810671467)
                    ·
                      rfl

theorem cell23_6615277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 1, 4, 4].length) (baseStart_6615277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6615277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6615277 prefixEnd_6615277 := by exact prefixLift 6615277
  have htrace : WordTrace (prefixWord ++ tailWord_6615277) baseStart_6615277 baseEnd_6615277 := by
    simpa [prefixWord, tailWord_6615277, baseEnd_6615277] using wordTrace_append hprefix tailTrace_6615277
  have hstable : (prefixWord ++ tailWord_6615277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6615277).length < 2 ^ (prefixWord ++ tailWord_6615277).sum := by decide
  have hdescent : baseEnd_6615277 < baseStart_6615277 := by decide
  rcases family_descends (prefixWord ++ tailWord_6615277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6615294 : List Nat := [4, 2, 2, 1, 1, 1, 5, 1, 2, 4]
def baseStart_6615294 : Nat := 118140960795 + 6615294 * 2 ^ 59
def prefixEnd_6615294 : Nat := 4983230072969 + 3 ^ 40 * 6615294 * 2
def baseEnd_6615294 : Nat := 1132275164268048621833941

theorem tailTrace_6615294 : CollatzResearch.WordTrace tailWord_6615294 prefixEnd_6615294 1132275164268048621833941 := by
  unfold tailWord_6615294
  simp only [CollatzResearch.WordTrace]
  refine ⟨30159949261990889389019617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 160853062730618076741437957 30159949261990889389019617)
  ·
    refine ⟨22619961946493167041764713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30159949261990889389019617 22619961946493167041764713)
    ·
      refine ⟨16964971459869875281323535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22619961946493167041764713 16964971459869875281323535)
      ·
        refine ⟨25447457189804812921985303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16964971459869875281323535 25447457189804812921985303)
        ·
          refine ⟨38171185784707219382977955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25447457189804812921985303 38171185784707219382977955)
          ·
            refine ⟨57256778677060829074466933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38171185784707219382977955 57256778677060829074466933)
            ·
              refine ⟨5367823000974452725731275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57256778677060829074466933 5367823000974452725731275)
              ·
                refine ⟨8051734501461679088596913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5367823000974452725731275 8051734501461679088596913)
                ·
                  refine ⟨6038800876096259316447685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8051734501461679088596913 6038800876096259316447685)
                  ·
                    refine ⟨1132275164268048621833941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6038800876096259316447685 1132275164268048621833941)
                    ·
                      rfl

theorem cell23_6615294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 5, 1, 2, 4].length) (baseStart_6615294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6615294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6615294 prefixEnd_6615294 := by exact prefixLift 6615294
  have htrace : WordTrace (prefixWord ++ tailWord_6615294) baseStart_6615294 baseEnd_6615294 := by
    simpa [prefixWord, tailWord_6615294, baseEnd_6615294] using wordTrace_append hprefix tailTrace_6615294
  have hstable : (prefixWord ++ tailWord_6615294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6615294).length < 2 ^ (prefixWord ++ tailWord_6615294).sum := by decide
  have hdescent : baseEnd_6615294 < baseStart_6615294 := by decide
  rcases family_descends (prefixWord ++ tailWord_6615294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6615313 : List Nat := [1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 5]
def baseStart_6615313 : Nat := 118140960795 + 6615313 * 2 ^ 59
def prefixEnd_6615313 : Nat := 4983230072969 + 3 ^ 40 * 6615313 * 2
def baseEnd_6615313 : Nat := 3396835248936581291164235

theorem tailTrace_6615313 : CollatzResearch.WordTrace tailWord_6615313 prefixEnd_6615313 3396835248936581291164235 := by
  unfold tailWord_6615313
  simp only [CollatzResearch.WordTrace]
  refine ⟨241280287082858281357098593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160853524721905520904732395 241280287082858281357098593)
  ·
    refine ⟨180960215312143711017823945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241280287082858281357098593 180960215312143711017823945)
    ·
      refine ⟨135720161484107783263367959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180960215312143711017823945 135720161484107783263367959)
      ·
        refine ⟨203580242226161674895051939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135720161484107783263367959 203580242226161674895051939)
        ·
          refine ⟨305370363339242512342577909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203580242226161674895051939 305370363339242512342577909)
          ·
            refine ⟨28628471563053985532116679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 305370363339242512342577909 28628471563053985532116679)
            ·
              refine ⟨42942707344580978298175019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28628471563053985532116679 42942707344580978298175019)
              ·
                refine ⟨64414061016871467447262529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42942707344580978298175019 64414061016871467447262529)
                ·
                  refine ⟨48310545762653600585446897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64414061016871467447262529 48310545762653600585446897)
                  ·
                    refine ⟨36232909321990200439085173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48310545762653600585446897 36232909321990200439085173)
                    ·
                      refine ⟨3396835248936581291164235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36232909321990200439085173 3396835248936581291164235)
                      ·
                        rfl

theorem cell23_6615313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 5].length) (baseStart_6615313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6615313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6615313 prefixEnd_6615313 := by exact prefixLift 6615313
  have htrace : WordTrace (prefixWord ++ tailWord_6615313) baseStart_6615313 baseEnd_6615313 := by
    simpa [prefixWord, tailWord_6615313, baseEnd_6615313] using wordTrace_append hprefix tailTrace_6615313
  have hstable : (prefixWord ++ tailWord_6615313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6615313).length < 2 ^ (prefixWord ++ tailWord_6615313).sum := by decide
  have hdescent : baseEnd_6615313 < baseStart_6615313 := by decide
  rcases family_descends (prefixWord ++ tailWord_6615313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6615335 : List Nat := [1, 1, 8, 1, 1, 2, 1, 1, 3, 2, 2]
def baseStart_6615335 : Nat := 118140960795 + 6615335 * 2 ^ 59
def prefixEnd_6615335 : Nat := 4983230072969 + 3 ^ 40 * 6615335 * 2
def baseEnd_6615335 : Nat := 3396846545510980205089135

theorem tailTrace_6615335 : CollatzResearch.WordTrace tailWord_6615335 prefixEnd_6615335 3396846545510980205089135 := by
  unfold tailWord_6615335
  simp only [CollatzResearch.WordTrace]
  refine ⟨241281089488778579114399459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160854059659185719409599639 241281089488778579114399459)
  ·
    refine ⟨361921634233167868671599189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241281089488778579114399459 361921634233167868671599189)
    ·
      refine ⟨4241269151169935960995303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 361921634233167868671599189 4241269151169935960995303)
      ·
        refine ⟨6361903726754903941492955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4241269151169935960995303 6361903726754903941492955)
        ·
          refine ⟨9542855590132355912239433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6361903726754903941492955 9542855590132355912239433)
          ·
            refine ⟨7157141692599266934179575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9542855590132355912239433 7157141692599266934179575)
            ·
              refine ⟨10735712538898900401269363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7157141692599266934179575 10735712538898900401269363)
              ·
                refine ⟨16103568808348350601904045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10735712538898900401269363 16103568808348350601904045)
                ·
                  refine ⟨6038838303130631475714017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16103568808348350601904045 6038838303130631475714017)
                  ·
                    refine ⟨4529128727347973606785513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6038838303130631475714017 4529128727347973606785513)
                    ·
                      refine ⟨3396846545510980205089135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4529128727347973606785513 3396846545510980205089135)
                      ·
                        rfl

theorem cell23_6615335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_6615335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6615335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6615335 prefixEnd_6615335 := by exact prefixLift 6615335
  have htrace : WordTrace (prefixWord ++ tailWord_6615335) baseStart_6615335 baseEnd_6615335 := by
    simpa [prefixWord, tailWord_6615335, baseEnd_6615335] using wordTrace_append hprefix tailTrace_6615335
  have hstable : (prefixWord ++ tailWord_6615335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6615335).length < 2 ^ (prefixWord ++ tailWord_6615335).sum := by decide
  have hdescent : baseEnd_6615335 < baseStart_6615335 := by decide
  rcases family_descends (prefixWord ++ tailWord_6615335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6615363 : List Nat := [1, 1, 1, 3, 1, 3, 2, 4, 7]
def baseStart_6615363 : Nat := 118140960795 + 6615363 * 2 ^ 59
def prefixEnd_6615363 : Nat := 4983230072969 + 3 ^ 40 * 6615363 * 2
def baseEnd_6615363 : Nat := 377428991441034010615445

theorem tailTrace_6615363 : CollatzResearch.WordTrace tailWord_6615363 prefixEnd_6615363 377428991441034010615445 := by
  unfold tailWord_6615363
  simp only [CollatzResearch.WordTrace]
  refine ⟨241282110732677139896418743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160854740488451426597612495 241282110732677139896418743)
  ·
    refine ⟨361923166099015709844628115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241282110732677139896418743 361923166099015709844628115)
    ·
      refine ⟨542884749148523564766942173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 361923166099015709844628115 542884749148523564766942173)
      ·
        refine ⟨203581780930696336787603315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 542884749148523564766942173 203581780930696336787603315)
        ·
          refine ⟨305372671396044505181404973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203581780930696336787603315 305372671396044505181404973)
          ·
            refine ⟨114514751773516689443026865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 305372671396044505181404973 114514751773516689443026865)
            ·
              refine ⟨85886063830137517082270149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114514751773516689443026865 85886063830137517082270149)
              ·
                refine ⟨16103636968150784452925653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 85886063830137517082270149 16103636968150784452925653)
                ·
                  refine ⟨377428991441034010615445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16103636968150784452925653 377428991441034010615445)
                  ·
                    rfl

theorem cell23_6615363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 4, 7].length) (baseStart_6615363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6615363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6615363 prefixEnd_6615363 := by exact prefixLift 6615363
  have htrace : WordTrace (prefixWord ++ tailWord_6615363) baseStart_6615363 baseEnd_6615363 := by
    simpa [prefixWord, tailWord_6615363, baseEnd_6615363] using wordTrace_append hprefix tailTrace_6615363
  have hstable : (prefixWord ++ tailWord_6615363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6615363).length < 2 ^ (prefixWord ++ tailWord_6615363).sum := by decide
  have hdescent : baseEnd_6615363 < baseStart_6615363 := by decide
  rcases family_descends (prefixWord ++ tailWord_6615363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6615393 : List Nat := [1, 2, 3, 1, 1, 1, 1, 1, 5, 7]
def baseStart_6615393 : Nat := 118140960795 + 6615393 * 2 ^ 59
def prefixEnd_6615393 : Nat := 4983230072969 + 3 ^ 40 * 6615393 * 2
def baseEnd_6615393 : Nat := 1132292109129646992721289

theorem tailTrace_6615393 : CollatzResearch.WordTrace tailWord_6615393 prefixEnd_6615393 1132292109129646992721289 := by
  unfold tailWord_6615393
  simp only [CollatzResearch.WordTrace]
  refine ⟨241283204922568455020010833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160855469948378970013340555 241283204922568455020010833)
  ·
    refine ⟨180962403691926341265008125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241283204922568455020010833 180962403691926341265008125)
    ·
      refine ⟨67860901384472377974378047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180962403691926341265008125 67860901384472377974378047)
      ·
        refine ⟨101791352076708566961567071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67860901384472377974378047 101791352076708566961567071)
        ·
          refine ⟨152687028115062850442350607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101791352076708566961567071 152687028115062850442350607)
          ·
            refine ⟨229030542172594275663525911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152687028115062850442350607 229030542172594275663525911)
            ·
              refine ⟨343545813258891413495288867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 229030542172594275663525911 343545813258891413495288867)
              ·
                refine ⟨515318719888337120242933301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 343545813258891413495288867 515318719888337120242933301)
                ·
                  refine ⟨48311129989531605022774997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 515318719888337120242933301 48311129989531605022774997)
                  ·
                    refine ⟨1132292109129646992721289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48311129989531605022774997 1132292109129646992721289)
                    ·
                      rfl

theorem cell23_6615393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 5, 7].length) (baseStart_6615393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6615393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6615393 prefixEnd_6615393 := by exact prefixLift 6615393
  have htrace : WordTrace (prefixWord ++ tailWord_6615393) baseStart_6615393 baseEnd_6615393 := by
    simpa [prefixWord, tailWord_6615393, baseEnd_6615393] using wordTrace_append hprefix tailTrace_6615393
  have hstable : (prefixWord ++ tailWord_6615393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6615393).length < 2 ^ (prefixWord ++ tailWord_6615393).sum := by decide
  have hdescent : baseEnd_6615393 < baseStart_6615393 := by decide
  rcases family_descends (prefixWord ++ tailWord_6615393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6615397 : List Nat := [1, 3, 1, 3, 1, 4, 1, 4, 5]
def baseStart_6615397 : Nat := 118140960795 + 6615397 * 2 ^ 59
def prefixEnd_6615397 : Nat := 4983230072969 + 3 ^ 40 * 6615397 * 2
def baseEnd_6615397 : Nat := 377430931256839884723761

theorem tailTrace_6615397 : CollatzResearch.WordTrace tailWord_6615397 prefixEnd_6615397 377430931256839884723761 := by
  unfold tailWord_6615397
  simp only [CollatzResearch.WordTrace]
  refine ⟨241283350814553963703156445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160855567209702642468770963 241283350814553963703156445)
  ·
    refine ⟨90481256555457736388683667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 241283350814553963703156445 90481256555457736388683667)
    ·
      refine ⟨135721884833186604583025501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90481256555457736388683667 135721884833186604583025501)
      ·
        refine ⟨50895706812444976718634563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135721884833186604583025501 50895706812444976718634563)
        ·
          refine ⟨76343560218667465077951845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50895706812444976718634563 76343560218667465077951845)
          ·
            refine ⟨14314417541000149702115971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76343560218667465077951845 14314417541000149702115971)
            ·
              refine ⟨21471626311500224553173957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14314417541000149702115971 21471626311500224553173957)
              ·
                refine ⟨4025929933406292103720117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21471626311500224553173957 4025929933406292103720117)
                ·
                  refine ⟨377430931256839884723761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4025929933406292103720117 377430931256839884723761)
                  ·
                    rfl

theorem cell23_6615397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 4, 5].length) (baseStart_6615397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6615397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6615397 prefixEnd_6615397 := by exact prefixLift 6615397
  have htrace : WordTrace (prefixWord ++ tailWord_6615397) baseStart_6615397 baseEnd_6615397 := by
    simpa [prefixWord, tailWord_6615397, baseEnd_6615397] using wordTrace_append hprefix tailTrace_6615397
  have hstable : (prefixWord ++ tailWord_6615397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6615397).length < 2 ^ (prefixWord ++ tailWord_6615397).sum := by decide
  have hdescent : baseEnd_6615397 < baseStart_6615397 := by decide
  rcases family_descends (prefixWord ++ tailWord_6615397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6615414 : List Nat := [5, 1, 1, 4, 1, 1, 1, 2, 7]
def baseStart_6615414 : Nat := 118140960795 + 6615414 * 2 ^ 59
def prefixEnd_6615414 : Nat := 4983230072969 + 3 ^ 40 * 6615414 * 2
def baseEnd_6615414 : Nat := 377431901164742821777919

theorem tailTrace_6615414 : CollatzResearch.WordTrace tailWord_6615414 prefixEnd_6615414 377431901164742821777919 := by
  unfold tailWord_6615414
  simp only [CollatzResearch.WordTrace]
  refine ⟨15080248178468273475407831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 160855980570328250404350197 15080248178468273475407831)
  ·
    refine ⟨22620372267702410213111747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15080248178468273475407831 22620372267702410213111747)
    ·
      refine ⟨33930558401553615319667621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22620372267702410213111747 33930558401553615319667621)
      ·
        refine ⟨6361979700291302872437679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33930558401553615319667621 6361979700291302872437679)
        ·
          refine ⟨9542969550436954308656519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6361979700291302872437679 9542969550436954308656519)
          ·
            refine ⟨14314454325655431462984779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9542969550436954308656519 14314454325655431462984779)
            ·
              refine ⟨21471681488483147194477169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14314454325655431462984779 21471681488483147194477169)
              ·
                refine ⟨16103761116362360395857877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21471681488483147194477169 16103761116362360395857877)
                ·
                  refine ⟨377431901164742821777919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16103761116362360395857877 377431901164742821777919)
                  ·
                    rfl

theorem cell23_6615414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 2, 7].length) (baseStart_6615414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6615414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6615414 prefixEnd_6615414 := by exact prefixLift 6615414
  have htrace : WordTrace (prefixWord ++ tailWord_6615414) baseStart_6615414 baseEnd_6615414 := by
    simpa [prefixWord, tailWord_6615414, baseEnd_6615414] using wordTrace_append hprefix tailTrace_6615414
  have hstable : (prefixWord ++ tailWord_6615414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6615414).length < 2 ^ (prefixWord ++ tailWord_6615414).sum := by decide
  have hdescent : baseEnd_6615414 < baseStart_6615414 := by decide
  rcases family_descends (prefixWord ++ tailWord_6615414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6615423 : List Nat := [1, 1, 2, 2, 1, 1, 2, 3, 2, 8]
def baseStart_6615423 : Nat := 118140960795 + 6615423 * 2 ^ 59
def prefixEnd_6615423 : Nat := 4983230072969 + 3 ^ 40 * 6615423 * 2
def baseEnd_6615423 : Nat := 1132297243936191953596243

theorem tailTrace_6615423 : CollatzResearch.WordTrace tailWord_6615423 prefixEnd_6615423 1132297243936191953596243 := by
  unfold tailWord_6615423
  simp only [CollatzResearch.WordTrace]
  refine ⟨241284299112459770143602923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160856199408306513429068615 241284299112459770143602923)
  ·
    refine ⟨361926448668689655215404385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241284299112459770143602923 361926448668689655215404385)
    ·
      refine ⟨271444836501517241411553289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 361926448668689655215404385 271444836501517241411553289)
      ·
        refine ⟨203583627376137931058664967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 271444836501517241411553289 203583627376137931058664967)
        ·
          refine ⟨305375441064206896587997451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203583627376137931058664967 305375441064206896587997451)
          ·
            refine ⟨458063161596310344881996177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 305375441064206896587997451 458063161596310344881996177)
            ·
              refine ⟨343547371197232758661497133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 458063161596310344881996177 343547371197232758661497133)
              ·
                refine ⟨128830264198962284498061425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 343547371197232758661497133 128830264198962284498061425)
                ·
                  refine ⟨96622698149221713373546069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 128830264198962284498061425 96622698149221713373546069)
                  ·
                    refine ⟨1132297243936191953596243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 96622698149221713373546069 1132297243936191953596243)
                    ·
                      rfl

theorem cell23_6615423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 3, 2, 8].length) (baseStart_6615423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6615423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6615423 prefixEnd_6615423 := by exact prefixLift 6615423
  have htrace : WordTrace (prefixWord ++ tailWord_6615423) baseStart_6615423 baseEnd_6615423 := by
    simpa [prefixWord, tailWord_6615423, baseEnd_6615423] using wordTrace_append hprefix tailTrace_6615423
  have hstable : (prefixWord ++ tailWord_6615423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6615423).length < 2 ^ (prefixWord ++ tailWord_6615423).sum := by decide
  have hdescent : baseEnd_6615423 < baseStart_6615423 := by decide
  rcases family_descends (prefixWord ++ tailWord_6615423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6615447 : List Nat := [1, 1, 3, 3, 1, 1, 3, 2, 2, 4, 2]
def baseStart_6615447 : Nat := 118140960795 + 6615447 * 2 ^ 59
def prefixEnd_6615447 : Nat := 4983230072969 + 3 ^ 40 * 6615447 * 2
def baseEnd_6615447 : Nat := 3396904055344283766888619

theorem tailTrace_6615447 : CollatzResearch.WordTrace tailWord_6615447 prefixEnd_6615447 3396904055344283766888619 := by
  unfold tailWord_6615447
  simp only [CollatzResearch.WordTrace]
  refine ⟨241285174464372822242476595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160856782976248548161651063 241285174464372822242476595)
  ·
    refine ⟨361927761696559233363714893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241285174464372822242476595 361927761696559233363714893)
    ·
      refine ⟨135722910636209712511393085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 361927761696559233363714893 135722910636209712511393085)
      ·
        refine ⟨50896091488578642191772407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135722910636209712511393085 50896091488578642191772407)
        ·
          refine ⟨76344137232867963287658611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50896091488578642191772407 76344137232867963287658611)
          ·
            refine ⟨114516205849301944931487917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76344137232867963287658611 114516205849301944931487917)
            ·
              refine ⟨42943577193488229349307969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 114516205849301944931487917 42943577193488229349307969)
              ·
                refine ⟨32207682895116172011980977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42943577193488229349307969 32207682895116172011980977)
                ·
                  refine ⟨24155762171337129008985733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32207682895116172011980977 24155762171337129008985733)
                  ·
                    refine ⟨4529205407125711689184825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24155762171337129008985733 4529205407125711689184825)
                    ·
                      refine ⟨3396904055344283766888619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4529205407125711689184825 3396904055344283766888619)
                      ·
                        rfl

theorem cell23_6615447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 2, 2, 4, 2].length) (baseStart_6615447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6615447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6615447 prefixEnd_6615447 := by exact prefixLift 6615447
  have htrace : WordTrace (prefixWord ++ tailWord_6615447) baseStart_6615447 baseEnd_6615447 := by
    simpa [prefixWord, tailWord_6615447, baseEnd_6615447] using wordTrace_append hprefix tailTrace_6615447
  have hstable : (prefixWord ++ tailWord_6615447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6615447).length < 2 ^ (prefixWord ++ tailWord_6615447).sum := by decide
  have hdescent : baseEnd_6615447 < baseStart_6615447 := by decide
  rcases family_descends (prefixWord ++ tailWord_6615447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6615480 : List Nat := [2, 1, 2, 1, 2, 2, 1, 1, 1, 7, 3]
def baseStart_6615480 : Nat := 118140960795 + 6615480 * 2 ^ 59
def prefixEnd_6615480 : Nat := 4983230072969 + 3 ^ 40 * 6615480 * 2
def baseEnd_6615480 : Nat := 3396921000205882137775967

theorem tailTrace_6615480 : CollatzResearch.WordTrace tailWord_6615480 prefixEnd_6615480 3396921000205882137775967 := by
  unfold tailWord_6615480
  simp only [CollatzResearch.WordTrace]
  refine ⟨120643189036626634439213947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160857585382168845918951929 120643189036626634439213947)
  ·
    refine ⟨180964783554939951658820921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120643189036626634439213947 180964783554939951658820921)
    ·
      refine ⟨135723587666204963744115691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180964783554939951658820921 135723587666204963744115691)
      ·
        refine ⟨203585381499307445616173537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135723587666204963744115691 203585381499307445616173537)
        ·
          refine ⟨152689036124480584212130153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 203585381499307445616173537 152689036124480584212130153)
          ·
            refine ⟨114516777093360438159097615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152689036124480584212130153 114516777093360438159097615)
            ·
              refine ⟨171775165640040657238646423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114516777093360438159097615 171775165640040657238646423)
              ·
                refine ⟨257662748460060985857969635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 171775165640040657238646423 257662748460060985857969635)
                ·
                  refine ⟨386494122690091478786954453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 257662748460060985857969635 386494122690091478786954453)
                  ·
                    refine ⟨9058456000549019034069245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 386494122690091478786954453 9058456000549019034069245)
                    ·
                      refine ⟨3396921000205882137775967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9058456000549019034069245 3396921000205882137775967)
                      ·
                        rfl

theorem cell23_6615480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 1, 7, 3].length) (baseStart_6615480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6615480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6615480 prefixEnd_6615480 := by exact prefixLift 6615480
  have htrace : WordTrace (prefixWord ++ tailWord_6615480) baseStart_6615480 baseEnd_6615480 := by
    simpa [prefixWord, tailWord_6615480, baseEnd_6615480] using wordTrace_append hprefix tailTrace_6615480
  have hstable : (prefixWord ++ tailWord_6615480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6615480).length < 2 ^ (prefixWord ++ tailWord_6615480).sum := by decide
  have hdescent : baseEnd_6615480 < baseStart_6615480 := by decide
  rcases family_descends (prefixWord ++ tailWord_6615480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6615497 : List Nat := [1, 2, 1, 1, 2, 1, 4, 2, 5, 1, 3]
def baseStart_6615497 : Nat := 118140960795 + 6615497 * 2 ^ 59
def prefixEnd_6615497 : Nat := 4983230072969 + 3 ^ 40 * 6615497 * 2
def baseEnd_6615497 : Nat := 3396929729377008571263389

theorem tailTrace_6615497 : CollatzResearch.WordTrace tailWord_6615497 prefixEnd_6615497 3396929729377008571263389 := by
  unfold tailWord_6615497
  simp only [CollatzResearch.WordTrace]
  refine ⟨241286998114191680781796745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160857998742794453854531163 241286998114191680781796745)
  ·
    refine ⟨180965248585643760586347559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241286998114191680781796745 180965248585643760586347559)
    ·
      refine ⟨271447872878465640879521339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180965248585643760586347559 271447872878465640879521339)
      ·
        refine ⟨407171809317698461319282009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271447872878465640879521339 407171809317698461319282009)
        ·
          refine ⟨305378856988273845989461507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 407171809317698461319282009 305378856988273845989461507)
          ·
            refine ⟨458068285482410768984192261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 305378856988273845989461507 458068285482410768984192261)
            ·
              refine ⟨85887803527952019184536049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 458068285482410768984192261 85887803527952019184536049)
              ·
                refine ⟨64415852645964014388402037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85887803527952019184536049 64415852645964014388402037)
                ·
                  refine ⟨6038986185559126348912691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 64415852645964014388402037 6038986185559126348912691)
                  ·
                    refine ⟨9058479278338689523369037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6038986185559126348912691 9058479278338689523369037)
                    ·
                      refine ⟨3396929729377008571263389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9058479278338689523369037 3396929729377008571263389)
                      ·
                        rfl

theorem cell23_6615497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 2, 5, 1, 3].length) (baseStart_6615497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6615497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6615497 prefixEnd_6615497 := by exact prefixLift 6615497
  have htrace : WordTrace (prefixWord ++ tailWord_6615497) baseStart_6615497 baseEnd_6615497 := by
    simpa [prefixWord, tailWord_6615497, baseEnd_6615497] using wordTrace_append hprefix tailTrace_6615497
  have hstable : (prefixWord ++ tailWord_6615497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6615497).length < 2 ^ (prefixWord ++ tailWord_6615497).sum := by decide
  have hdescent : baseEnd_6615497 < baseStart_6615497 := by decide
  rcases family_descends (prefixWord ++ tailWord_6615497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6615508 : List Nat := [2, 4, 1, 2, 2, 2, 3, 2, 1, 4]
def baseStart_6615508 : Nat := 118140960795 + 6615508 * 2 ^ 59
def prefixEnd_6615508 : Nat := 4983230072969 + 3 ^ 40 * 6615508 * 2
def baseEnd_6615508 : Nat := 1132311792554736009408613

theorem tailTrace_6615508 : CollatzResearch.WordTrace tailWord_6615508 prefixEnd_6615508 1132311792554736009408613 := by
  unfold tailWord_6615508
  simp only [CollatzResearch.WordTrace]
  refine ⟨120643699658575914830223589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160858266211434553106964785 120643699658575914830223589)
  ·
    refine ⟨22620693685982984030666923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 120643699658575914830223589 22620693685982984030666923)
    ·
      refine ⟨33931040528974476046000385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22620693685982984030666923 33931040528974476046000385)
      ·
        refine ⟨25448280396730857034500289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33931040528974476046000385 25448280396730857034500289)
        ·
          refine ⟨19086210297548142775875217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25448280396730857034500289 19086210297548142775875217)
          ·
            refine ⟨14314657723161107081906413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19086210297548142775875217 14314657723161107081906413)
            ·
              refine ⟨5367996646185415155714905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14314657723161107081906413 5367996646185415155714905)
              ·
                refine ⟨4025997484639061366786179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5367996646185415155714905 4025997484639061366786179)
                ·
                  refine ⟨6038996226958592050179269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4025997484639061366786179 6038996226958592050179269)
                  ·
                    refine ⟨1132311792554736009408613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6038996226958592050179269 1132311792554736009408613)
                    ·
                      rfl

theorem cell23_6615508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 3, 2, 1, 4].length) (baseStart_6615508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6615508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6615508 prefixEnd_6615508 := by exact prefixLift 6615508
  have htrace : WordTrace (prefixWord ++ tailWord_6615508) baseStart_6615508 baseEnd_6615508 := by
    simpa [prefixWord, tailWord_6615508, baseEnd_6615508] using wordTrace_append hprefix tailTrace_6615508
  have hstable : (prefixWord ++ tailWord_6615508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6615508).length < 2 ^ (prefixWord ++ tailWord_6615508).sum := by decide
  have hdescent : baseEnd_6615508 < baseStart_6615508 := by decide
  rcases family_descends (prefixWord ++ tailWord_6615508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6615517 : List Nat := [1, 4, 3, 1, 1, 1, 2, 2, 3, 5]
def baseStart_6615517 : Nat := 118140960795 + 6615517 * 2 ^ 59
def prefixEnd_6615517 : Nat := 4983230072969 + 3 ^ 40 * 6615517 * 2
def baseEnd_6615517 : Nat := 1132313332996699497671099

theorem tailTrace_6615517 : CollatzResearch.WordTrace tailWord_6615517 prefixEnd_6615517 1132313332996699497671099 := by
  unfold tailWord_6615517
  simp only [CollatzResearch.WordTrace]
  refine ⟨241287727574119224197524805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160858485049412816131683203 241287727574119224197524805)
  ·
    refine ⟨45241448920147354537035901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 241287727574119224197524805 45241448920147354537035901)
    ·
      refine ⟨16965543345055257951388463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45241448920147354537035901 16965543345055257951388463)
      ·
        refine ⟨25448315017582886927082695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16965543345055257951388463 25448315017582886927082695)
        ·
          refine ⟨38172472526374330390624043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25448315017582886927082695 38172472526374330390624043)
          ·
            refine ⟨57258708789561495585936065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38172472526374330390624043 57258708789561495585936065)
            ·
              refine ⟨42944031592171121689452049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57258708789561495585936065 42944031592171121689452049)
              ·
                refine ⟨32208023694128341267089037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42944031592171121689452049 32208023694128341267089037)
                ·
                  refine ⟨12078008885298127975158389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32208023694128341267089037 12078008885298127975158389)
                  ·
                    refine ⟨1132313332996699497671099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12078008885298127975158389 1132313332996699497671099)
                    ·
                      rfl

theorem cell23_6615517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 2, 3, 5].length) (baseStart_6615517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6615517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6615517 prefixEnd_6615517 := by exact prefixLift 6615517
  have htrace : WordTrace (prefixWord ++ tailWord_6615517) baseStart_6615517 baseEnd_6615517 := by
    simpa [prefixWord, tailWord_6615517, baseEnd_6615517] using wordTrace_append hprefix tailTrace_6615517
  have hstable : (prefixWord ++ tailWord_6615517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6615517).length < 2 ^ (prefixWord ++ tailWord_6615517).sum := by decide
  have hdescent : baseEnd_6615517 < baseStart_6615517 := by decide
  rcases family_descends (prefixWord ++ tailWord_6615517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6615534 : List Nat := [4, 1, 2, 1, 2, 2, 3, 2, 1, 5]
def baseStart_6615534 : Nat := 118140960795 + 6615534 * 2 ^ 59
def prefixEnd_6615534 : Nat := 4983230072969 + 3 ^ 40 * 6615534 * 2
def baseEnd_6615534 : Nat := 1132316242720408308833573

theorem tailTrace_6615534 : CollatzResearch.WordTrace tailWord_6615534 prefixEnd_6615534 1132316242720408308833573 := by
  unfold tailWord_6615534
  simp only [CollatzResearch.WordTrace]
  refine ⟨30161043451882204512611707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 160858898410038424067262437 30161043451882204512611707)
  ·
    refine ⟨45241565177823306768917561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30161043451882204512611707 45241565177823306768917561)
    ·
      refine ⟨33931173883367480076688171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45241565177823306768917561 33931173883367480076688171)
      ·
        refine ⟨50896760825051220115032257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33931173883367480076688171 50896760825051220115032257)
        ·
          refine ⟨38172570618788415086274193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50896760825051220115032257 38172570618788415086274193)
          ·
            refine ⟨28629427964091311314705645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38172570618788415086274193 28629427964091311314705645)
            ·
              refine ⟨10736035486534241743014617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28629427964091311314705645 10736035486534241743014617)
              ·
                refine ⟨8052026614900681307260963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10736035486534241743014617 8052026614900681307260963)
                ·
                  refine ⟨12078039922351021960891445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8052026614900681307260963 12078039922351021960891445)
                  ·
                    refine ⟨1132316242720408308833573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12078039922351021960891445 1132316242720408308833573)
                    ·
                      rfl

theorem cell23_6615534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 3, 2, 1, 5].length) (baseStart_6615534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6615534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6615534 prefixEnd_6615534 := by exact prefixLift 6615534
  have htrace : WordTrace (prefixWord ++ tailWord_6615534) baseStart_6615534 baseEnd_6615534 := by
    simpa [prefixWord, tailWord_6615534, baseEnd_6615534] using wordTrace_append hprefix tailTrace_6615534
  have hstable : (prefixWord ++ tailWord_6615534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6615534).length < 2 ^ (prefixWord ++ tailWord_6615534).sum := by decide
  have hdescent : baseEnd_6615534 < baseStart_6615534 := by decide
  rcases family_descends (prefixWord ++ tailWord_6615534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6615537 : List Nat := [1, 2, 2, 2, 3, 1, 3, 1, 3, 1, 4]
def baseStart_6615537 : Nat := 118140960795 + 6615537 * 2 ^ 59
def prefixEnd_6615537 : Nat := 4983230072969 + 3 ^ 40 * 6615537 * 2
def baseEnd_6615537 : Nat := 3396950268603188414763205

theorem tailTrace_6615537 : CollatzResearch.WordTrace tailWord_6615537 prefixEnd_6615537 3396950268603188414763205 := by
  unfold tailWord_6615537
  simp only [CollatzResearch.WordTrace]
  refine ⟨241288457034046767613252865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160858971356031178408835243 241288457034046767613252865)
  ·
    refine ⟨180966342775535075709939649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241288457034046767613252865 180966342775535075709939649)
    ·
      refine ⟨135724757081651306782454737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180966342775535075709939649 135724757081651306782454737)
      ·
        refine ⟨101793567811238480086841053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135724757081651306782454737 101793567811238480086841053)
        ·
          refine ⟨38172587929214430032565395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101793567811238480086841053 38172587929214430032565395)
          ·
            refine ⟨57258881893821645048848093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38172587929214430032565395 57258881893821645048848093)
            ·
              refine ⟨21472080710183116893318035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57258881893821645048848093 21472080710183116893318035)
              ·
                refine ⟨32208121065274675339977053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21472080710183116893318035 32208121065274675339977053)
                ·
                  refine ⟨12078045399478003252491395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32208121065274675339977053 12078045399478003252491395)
                  ·
                    refine ⟨18117068099217004878737093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12078045399478003252491395 18117068099217004878737093)
                    ·
                      refine ⟨3396950268603188414763205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18117068099217004878737093 3396950268603188414763205)
                      ·
                        rfl

theorem cell23_6615537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 1, 3, 1, 4].length) (baseStart_6615537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6615537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6615537 prefixEnd_6615537 := by exact prefixLift 6615537
  have htrace : WordTrace (prefixWord ++ tailWord_6615537) baseStart_6615537 baseEnd_6615537 := by
    simpa [prefixWord, tailWord_6615537, baseEnd_6615537] using wordTrace_append hprefix tailTrace_6615537
  have hstable : (prefixWord ++ tailWord_6615537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6615537).length < 2 ^ (prefixWord ++ tailWord_6615537).sum := by decide
  have hdescent : baseEnd_6615537 < baseStart_6615537 := by decide
  rcases family_descends (prefixWord ++ tailWord_6615537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6615557 : List Nat := [1, 3, 1, 1, 2, 2, 5, 1, 1, 1, 5]
def baseStart_6615557 : Nat := 118140960795 + 6615557 * 2 ^ 59
def prefixEnd_6615557 : Nat := 4983230072969 + 3 ^ 40 * 6615557 * 2
def baseEnd_6615557 : Nat := 3396960538216278336513113

theorem tailTrace_6615557 : CollatzResearch.WordTrace tailWord_6615557 prefixEnd_6615557 3396960538216278336513113 := by
  unfold tailWord_6615557
  simp only [CollatzResearch.WordTrace]
  refine ⟨241289186493974311028980925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160859457662649540685987283 241289186493974311028980925)
  ·
    refine ⟨90483444935240366635867847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 241289186493974311028980925 90483444935240366635867847)
    ·
      refine ⟨135725167402860549953801771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90483444935240366635867847 135725167402860549953801771)
      ·
        refine ⟨203587751104290824930702657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135725167402860549953801771 203587751104290824930702657)
        ·
          refine ⟨152690813328218118698026993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 203587751104290824930702657 152690813328218118698026993)
          ·
            refine ⟨114518109996163589023520245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152690813328218118698026993 114518109996163589023520245)
            ·
              refine ⟨10736072812140336470955023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 114518109996163589023520245 10736072812140336470955023)
              ·
                refine ⟨16104109218210504706432535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10736072812140336470955023 16104109218210504706432535)
                ·
                  refine ⟨24156163827315757059648803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16104109218210504706432535 24156163827315757059648803)
                  ·
                    refine ⟨36234245740973635589473205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24156163827315757059648803 36234245740973635589473205)
                    ·
                      refine ⟨3396960538216278336513113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36234245740973635589473205 3396960538216278336513113)
                      ·
                        rfl

theorem cell23_6615557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 5, 1, 1, 1, 5].length) (baseStart_6615557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6615557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6615557 prefixEnd_6615557 := by exact prefixLift 6615557
  have htrace : WordTrace (prefixWord ++ tailWord_6615557) baseStart_6615557 baseEnd_6615557 := by
    simpa [prefixWord, tailWord_6615557, baseEnd_6615557] using wordTrace_append hprefix tailTrace_6615557
  have hstable : (prefixWord ++ tailWord_6615557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6615557).length < 2 ^ (prefixWord ++ tailWord_6615557).sum := by decide
  have hdescent : baseEnd_6615557 < baseStart_6615557 := by decide
  rcases family_descends (prefixWord ++ tailWord_6615557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6615564 : List Nat := [2, 2, 1, 2, 4, 1, 1, 4, 2, 4]
def baseStart_6615564 : Nat := 118140960795 + 6615564 * 2 ^ 59
def prefixEnd_6615564 : Nat := 4983230072969 + 3 ^ 40 * 6615564 * 2
def baseEnd_6615564 : Nat := 1132321377526953269708527

theorem tailTrace_6615564 : CollatzResearch.WordTrace tailWord_6615564 prefixEnd_6615564 1132321377526953269708527 := by
  unfold tailWord_6615564
  simp only [CollatzResearch.WordTrace]
  refine ⟨120644720902474475612242873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160859627869965967482990497 120644720902474475612242873)
  ·
    refine ⟨90483540676855856709182155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120644720902474475612242873 90483540676855856709182155)
    ·
      refine ⟨135725311015283785063773233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90483540676855856709182155 135725311015283785063773233)
      ·
        refine ⟨101793983261462838797829925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135725311015283785063773233 101793983261462838797829925)
        ·
          refine ⟨19086371861524282274593111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 101793983261462838797829925 19086371861524282274593111)
          ·
            refine ⟨28629557792286423411889667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19086371861524282274593111 28629557792286423411889667)
            ·
              refine ⟨42944336688429635117834501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28629557792286423411889667 42944336688429635117834501)
              ·
                refine ⟨8052063129080556584593969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42944336688429635117834501 8052063129080556584593969)
                ·
                  refine ⟨6039047346810417438445477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8052063129080556584593969 6039047346810417438445477)
                  ·
                    refine ⟨1132321377526953269708527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6039047346810417438445477 1132321377526953269708527)
                    ·
                      rfl

theorem cell23_6615564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 4, 2, 4].length) (baseStart_6615564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6615564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6615564 prefixEnd_6615564 := by exact prefixLift 6615564
  have htrace : WordTrace (prefixWord ++ tailWord_6615564) baseStart_6615564 baseEnd_6615564 := by
    simpa [prefixWord, tailWord_6615564, baseEnd_6615564] using wordTrace_append hprefix tailTrace_6615564
  have hstable : (prefixWord ++ tailWord_6615564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6615564).length < 2 ^ (prefixWord ++ tailWord_6615564).sum := by decide
  have hdescent : baseEnd_6615564 < baseStart_6615564 := by decide
  rcases family_descends (prefixWord ++ tailWord_6615564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6615594 : List Nat := [3, 1, 4, 1, 1, 3, 3, 7]
def baseStart_6615594 : Nat := 118140960795 + 6615594 * 2 ^ 59
def prefixEnd_6615594 : Nat := 4983230072969 + 3 ^ 40 * 6615594 * 2
def baseEnd_6615594 : Nat := 125814056925944247842609

theorem tailTrace_6615594 : CollatzResearch.WordTrace tailWord_6615594 prefixEnd_6615594 125814056925944247842609 := by
  unfold tailWord_6615594
  simp only [CollatzResearch.WordTrace]
  refine ⟨60322633998710066587019459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160860357329893510898718557 60322633998710066587019459)
  ·
    refine ⟨90483950998065099880529189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60322633998710066587019459 90483950998065099880529189)
    ·
      refine ⟨16965740812137206227599223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90483950998065099880529189 16965740812137206227599223)
      ·
        refine ⟨25448611218205809341398835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16965740812137206227599223 25448611218205809341398835)
        ·
          refine ⟨38172916827308714012098253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25448611218205809341398835 38172916827308714012098253)
          ·
            refine ⟨14314843810240767754536845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38172916827308714012098253 14314843810240767754536845)
            ·
              refine ⟨5368066428840287907951317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14314843810240767754536845 5368066428840287907951317)
              ·
                refine ⟨125814056925944247842609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5368066428840287907951317 125814056925944247842609)
                ·
                  rfl

theorem cell23_6615594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 3, 7].length) (baseStart_6615594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6615594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6615594 prefixEnd_6615594 := by exact prefixLift 6615594
  have htrace : WordTrace (prefixWord ++ tailWord_6615594) baseStart_6615594 baseEnd_6615594 := by
    simpa [prefixWord, tailWord_6615594, baseEnd_6615594] using wordTrace_append hprefix tailTrace_6615594
  have hstable : (prefixWord ++ tailWord_6615594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6615594).length < 2 ^ (prefixWord ++ tailWord_6615594).sum := by decide
  have hdescent : baseEnd_6615594 < baseStart_6615594 := by decide
  rcases family_descends (prefixWord ++ tailWord_6615594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6615621 : List Nat := [1, 3, 1, 1, 1, 5, 3, 2, 2, 1, 3]
def baseStart_6615621 : Nat := 118140960795 + 6615621 * 2 ^ 59
def prefixEnd_6615621 : Nat := 4983230072969 + 3 ^ 40 * 6615621 * 2
def baseEnd_6615621 : Nat := 3396993400978166086112819

theorem tailTrace_6615621 : CollatzResearch.WordTrace tailWord_6615621 prefixEnd_6615621 3396993400978166086112819 := by
  unfold tailWord_6615621
  simp only [CollatzResearch.WordTrace]
  refine ⟨241291520765742449959310717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160861013843828299972873811 241291520765742449959310717)
  ·
    refine ⟨90484320287153418734741519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 241291520765742449959310717 90484320287153418734741519)
    ·
      refine ⟨135726480430730128102112279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90484320287153418734741519 135726480430730128102112279)
      ·
        refine ⟨203589720646095192153168419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135726480430730128102112279 203589720646095192153168419)
        ·
          refine ⟨305384580969142788229752629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203589720646095192153168419 305384580969142788229752629)
          ·
            refine ⟨28629804465857136396539309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 305384580969142788229752629 28629804465857136396539309)
            ·
              refine ⟨10736176674696426148702241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28629804465857136396539309 10736176674696426148702241)
              ·
                refine ⟨8052132506022319611526681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10736176674696426148702241 8052132506022319611526681)
                ·
                  refine ⟨6039099379516739708645011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8052132506022319611526681 6039099379516739708645011)
                  ·
                    refine ⟨9058649069275109562967517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6039099379516739708645011 9058649069275109562967517)
                    ·
                      refine ⟨3396993400978166086112819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9058649069275109562967517 3396993400978166086112819)
                      ·
                        rfl

theorem cell23_6615621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 3, 2, 2, 1, 3].length) (baseStart_6615621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6615621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6615621 prefixEnd_6615621 := by exact prefixLift 6615621
  have htrace : WordTrace (prefixWord ++ tailWord_6615621) baseStart_6615621 baseEnd_6615621 := by
    simpa [prefixWord, tailWord_6615621, baseEnd_6615621] using wordTrace_append hprefix tailTrace_6615621
  have hstable : (prefixWord ++ tailWord_6615621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6615621).length < 2 ^ (prefixWord ++ tailWord_6615621).sum := by decide
  have hdescent : baseEnd_6615621 < baseStart_6615621 := by decide
  rcases family_descends (prefixWord ++ tailWord_6615621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6615622 : List Nat := [6, 1, 1, 1, 2, 1, 2, 4, 1, 2, 2]
def baseStart_6615622 : Nat := 118140960795 + 6615622 * 2 ^ 59
def prefixEnd_6615622 : Nat := 4983230072969 + 3 ^ 40 * 6615622 * 2
def baseEnd_6615622 : Nat := 3396993914458820582200315

theorem tailTrace_6615622 : CollatzResearch.WordTrace tailWord_6615622 prefixEnd_6615622 3396993914458820582200315 := by
  unfold tailWord_6615622
  simp only [CollatzResearch.WordTrace]
  refine ⟨7540361163710588347815535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 160861038159159218086731413 7540361163710588347815535)
  ·
    refine ⟨11310541745565882521723303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7540361163710588347815535 11310541745565882521723303)
    ·
      refine ⟨16965812618348823782584955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11310541745565882521723303 16965812618348823782584955)
      ·
        refine ⟨25448718927523235673877433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16965812618348823782584955 25448718927523235673877433)
        ·
          refine ⟨19086539195642426755408075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25448718927523235673877433 19086539195642426755408075)
          ·
            refine ⟨28629808793463640133112113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19086539195642426755408075 28629808793463640133112113)
            ·
              refine ⟨21472356595097730099834085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28629808793463640133112113 21472356595097730099834085)
              ·
                refine ⟨4026066861580824393718891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21472356595097730099834085 4026066861580824393718891)
                ·
                  refine ⟨6039100292371236590578337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4026066861580824393718891 6039100292371236590578337)
                  ·
                    refine ⟨4529325219278427442933753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6039100292371236590578337 4529325219278427442933753)
                    ·
                      refine ⟨3396993914458820582200315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4529325219278427442933753 3396993914458820582200315)
                      ·
                        rfl

theorem cell23_6615622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 4, 1, 2, 2].length) (baseStart_6615622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6615622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6615622 prefixEnd_6615622 := by exact prefixLift 6615622
  have htrace : WordTrace (prefixWord ++ tailWord_6615622) baseStart_6615622 baseEnd_6615622 := by
    simpa [prefixWord, tailWord_6615622, baseEnd_6615622] using wordTrace_append hprefix tailTrace_6615622
  have hstable : (prefixWord ++ tailWord_6615622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6615622).length < 2 ^ (prefixWord ++ tailWord_6615622).sum := by decide
  have hdescent : baseEnd_6615622 < baseStart_6615622 := by decide
  rcases family_descends (prefixWord ++ tailWord_6615622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6615637 : List Nat := [1, 3, 2, 2, 1, 1, 4, 1, 2, 6]
def baseStart_6615637 : Nat := 118140960795 + 6615637 * 2 ^ 59
def prefixEnd_6615637 : Nat := 4983230072969 + 3 ^ 40 * 6615637 * 2
def baseEnd_6615637 : Nat := 1132333872222879341170915

theorem tailTrace_6615637 : CollatzResearch.WordTrace tailWord_6615637 prefixEnd_6615637 1132333872222879341170915 := by
  unfold tailWord_6615637
  simp only [CollatzResearch.WordTrace]
  refine ⟨241292104333684484691893165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160861402889122989794595443 241292104333684484691893165)
  ·
    refine ⟨90484539125131681759459937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 241292104333684484691893165 90484539125131681759459937)
    ·
      refine ⟨67863404343848761319594953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90484539125131681759459937 67863404343848761319594953)
      ·
        refine ⟨50897553257886570989696215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67863404343848761319594953 50897553257886570989696215)
        ·
          refine ⟨76346329886829856484544323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50897553257886570989696215 76346329886829856484544323)
          ·
            refine ⟨114519494830244784726816485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76346329886829856484544323 114519494830244784726816485)
            ·
              refine ⟨21472405280670897136278091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 114519494830244784726816485 21472405280670897136278091)
              ·
                refine ⟨32208607921006345704417137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21472405280670897136278091 32208607921006345704417137)
                ·
                  refine ⟨24156455940754759278312853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32208607921006345704417137 24156455940754759278312853)
                  ·
                    refine ⟨1132333872222879341170915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24156455940754759278312853 1132333872222879341170915)
                    ·
                      rfl

theorem cell23_6615637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 1, 2, 6].length) (baseStart_6615637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6615637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6615637 prefixEnd_6615637 := by exact prefixLift 6615637
  have htrace : WordTrace (prefixWord ++ tailWord_6615637) baseStart_6615637 baseEnd_6615637 := by
    simpa [prefixWord, tailWord_6615637, baseEnd_6615637] using wordTrace_append hprefix tailTrace_6615637
  have hstable : (prefixWord ++ tailWord_6615637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6615637).length < 2 ^ (prefixWord ++ tailWord_6615637).sum := by decide
  have hdescent : baseEnd_6615637 < baseStart_6615637 := by decide
  rcases family_descends (prefixWord ++ tailWord_6615637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6615647 : List Nat := [1, 1, 2, 3, 1, 1, 1, 4, 2, 4, 3]
def baseStart_6615647 : Nat := 118140960795 + 6615647 * 2 ^ 59
def prefixEnd_6615647 : Nat := 4983230072969 + 3 ^ 40 * 6615647 * 2
def baseEnd_6615647 : Nat := 3397006751475182984387699

theorem tailTrace_6615647 : CollatzResearch.WordTrace tailWord_6615647 prefixEnd_6615647 3397006751475182984387699 := by
  unfold tailWord_6615647
  simp only [CollatzResearch.WordTrace]
  refine ⟨241292469063648256399757195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160861646042432170933171463 241292469063648256399757195)
  ·
    refine ⟨361938703595472384599635793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241292469063648256399757195 361938703595472384599635793)
    ·
      refine ⟨271454027696604288449726845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 361938703595472384599635793 271454027696604288449726845)
      ·
        refine ⟨101795260386226608168647567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 271454027696604288449726845 101795260386226608168647567)
        ·
          refine ⟨152692890579339912252971351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101795260386226608168647567 152692890579339912252971351)
          ·
            refine ⟨229039335869009868379457027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152692890579339912252971351 229039335869009868379457027)
            ·
              refine ⟨343559003803514802569185541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 229039335869009868379457027 343559003803514802569185541)
              ·
                refine ⟨64417313213159025481722289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 343559003803514802569185541 64417313213159025481722289)
                ·
                  refine ⟨48312984909869269111291717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64417313213159025481722289 48312984909869269111291717)
                  ·
                    refine ⟨9058684670600487958367197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48312984909869269111291717 9058684670600487958367197)
                    ·
                      refine ⟨3397006751475182984387699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9058684670600487958367197 3397006751475182984387699)
                      ·
                        rfl

theorem cell23_6615647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 4, 2, 4, 3].length) (baseStart_6615647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6615647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6615647 prefixEnd_6615647 := by exact prefixLift 6615647
  have htrace : WordTrace (prefixWord ++ tailWord_6615647) baseStart_6615647 baseEnd_6615647 := by
    simpa [prefixWord, tailWord_6615647, baseEnd_6615647] using wordTrace_append hprefix tailTrace_6615647
  have hstable : (prefixWord ++ tailWord_6615647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6615647).length < 2 ^ (prefixWord ++ tailWord_6615647).sum := by decide
  have hdescent : baseEnd_6615647 < baseStart_6615647 := by decide
  rcases family_descends (prefixWord ++ tailWord_6615647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6615664 : List Nat := [2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 5]
def baseStart_6615664 : Nat := 118140960795 + 6615664 * 2 ^ 59
def prefixEnd_6615664 : Nat := 4983230072969 + 3 ^ 40 * 6615664 * 2
def baseEnd_6615664 : Nat := 3397015480646309417875121

theorem tailTrace_6615664 : CollatzResearch.WordTrace tailWord_6615664 prefixEnd_6615664 3397015480646309417875121 := by
  unfold tailWord_6615664
  simp only [CollatzResearch.WordTrace]
  refine ⟨120646544552293334151563023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160862059403057778868750697 120646544552293334151563023)
  ·
    refine ⟨180969816828440001227344535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120646544552293334151563023 180969816828440001227344535)
    ·
      refine ⟨271454725242660001841016803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180969816828440001227344535 271454725242660001841016803)
      ·
        refine ⟨407182087863990002761525205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271454725242660001841016803 407182087863990002761525205)
        ·
          refine ⟨9543330184312265689723247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 407182087863990002761525205 9543330184312265689723247)
          ·
            refine ⟨14314995276468398534584871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9543330184312265689723247 14314995276468398534584871)
            ·
              refine ⟨21472492914702597801877307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14314995276468398534584871 21472492914702597801877307)
              ·
                refine ⟨32208739372053896702815961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21472492914702597801877307 32208739372053896702815961)
                ·
                  refine ⟨24156554529040422527111971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32208739372053896702815961 24156554529040422527111971)
                  ·
                    refine ⟨36234831793560633790667957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24156554529040422527111971 36234831793560633790667957)
                    ·
                      refine ⟨3397015480646309417875121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36234831793560633790667957 3397015480646309417875121)
                      ·
                        rfl

theorem cell23_6615664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 5].length) (baseStart_6615664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6615664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6615664 prefixEnd_6615664 := by exact prefixLift 6615664
  have htrace : WordTrace (prefixWord ++ tailWord_6615664) baseStart_6615664 baseEnd_6615664 := by
    simpa [prefixWord, tailWord_6615664, baseEnd_6615664] using wordTrace_append hprefix tailTrace_6615664
  have hstable : (prefixWord ++ tailWord_6615664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6615664).length < 2 ^ (prefixWord ++ tailWord_6615664).sum := by decide
  have hdescent : baseEnd_6615664 < baseStart_6615664 := by decide
  rcases family_descends (prefixWord ++ tailWord_6615664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6615684 : List Nat := [2, 3, 2, 1, 3, 1, 3, 1, 7]
def baseStart_6615684 : Nat := 118140960795 + 6615684 * 2 ^ 59
def prefixEnd_6615684 : Nat := 4983230072969 + 3 ^ 40 * 6615684 * 2
def baseEnd_6615684 : Nat := 377447305584377704402781

theorem tailTrace_6615684 : CollatzResearch.WordTrace tailWord_6615684 prefixEnd_6615684 377447305584377704402781 := by
  unfold tailWord_6615684
  simp only [CollatzResearch.WordTrace]
  refine ⟨120646909282257105859427053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160862545709676141145902737 120646909282257105859427053)
  ·
    refine ⟨45242590980846414697285145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120646909282257105859427053 45242590980846414697285145)
    ·
      refine ⟨33931943235634811022963859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45242590980846414697285145 33931943235634811022963859)
      ·
        refine ⟨50897914853452216534445789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33931943235634811022963859 50897914853452216534445789)
        ·
          refine ⟨19086718070044581200417171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50897914853452216534445789 19086718070044581200417171)
          ·
            refine ⟨28630077105066871800625757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19086718070044581200417171 28630077105066871800625757)
            ·
              refine ⟨10736278914400076925234659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28630077105066871800625757 10736278914400076925234659)
              ·
                refine ⟨16104418371600115387851989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10736278914400076925234659 16104418371600115387851989)
                ·
                  refine ⟨377447305584377704402781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16104418371600115387851989 377447305584377704402781)
                  ·
                    rfl

theorem cell23_6615684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 3, 1, 7].length) (baseStart_6615684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6615684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6615684 prefixEnd_6615684 := by exact prefixLift 6615684
  have htrace : WordTrace (prefixWord ++ tailWord_6615684) baseStart_6615684 baseEnd_6615684 := by
    simpa [prefixWord, tailWord_6615684, baseEnd_6615684] using wordTrace_append hprefix tailTrace_6615684
  have hstable : (prefixWord ++ tailWord_6615684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6615684).length < 2 ^ (prefixWord ++ tailWord_6615684).sum := by decide
  have hdescent : baseEnd_6615684 < baseStart_6615684 := by decide
  rcases family_descends (prefixWord ++ tailWord_6615684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6615694 : List Nat := [4, 1, 1, 3, 1, 1, 2, 1, 1, 5, 3]
def baseStart_6615694 : Nat := 118140960795 + 6615694 * 2 ^ 59
def prefixEnd_6615694 : Nat := 4983230072969 + 3 ^ 40 * 6615694 * 2
def baseEnd_6615694 : Nat := 3397030885065944300499983

theorem tailTrace_6615694 : CollatzResearch.WordTrace tailWord_6615694 prefixEnd_6615694 3397030885065944300499983 := by
  unfold tailWord_6615694
  simp only [CollatzResearch.WordTrace]
  refine ⟨30161772911809747928339767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 160862788862985322284478757 30161772911809747928339767)
  ·
    refine ⟨45242659367714621892509651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30161772911809747928339767 45242659367714621892509651)
    ·
      refine ⟨67863989051571932838764477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45242659367714621892509651 67863989051571932838764477)
      ·
        refine ⟨25448995894339474814536679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67863989051571932838764477 25448995894339474814536679)
        ·
          refine ⟨38173493841509212221805019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25448995894339474814536679 38173493841509212221805019)
          ·
            refine ⟨57260240762263818332707529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38173493841509212221805019 57260240762263818332707529)
            ·
              refine ⟨42945180571697863749530647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57260240762263818332707529 42945180571697863749530647)
              ·
                refine ⟨64417770857546795624295971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42945180571697863749530647 64417770857546795624295971)
                ·
                  refine ⟨96626656286320193436443957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64417770857546795624295971 96626656286320193436443957)
                  ·
                    refine ⟨9058749026842518134666621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 96626656286320193436443957 9058749026842518134666621)
                    ·
                      refine ⟨3397030885065944300499983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9058749026842518134666621 3397030885065944300499983)
                      ·
                        rfl

theorem cell23_6615694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 1, 1, 5, 3].length) (baseStart_6615694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6615694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6615694 prefixEnd_6615694 := by exact prefixLift 6615694
  have htrace : WordTrace (prefixWord ++ tailWord_6615694) baseStart_6615694 baseEnd_6615694 := by
    simpa [prefixWord, tailWord_6615694, baseEnd_6615694] using wordTrace_append hprefix tailTrace_6615694
  have hstable : (prefixWord ++ tailWord_6615694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6615694).length < 2 ^ (prefixWord ++ tailWord_6615694).sum := by decide
  have hdescent : baseEnd_6615694 < baseStart_6615694 := by decide
  rcases family_descends (prefixWord ++ tailWord_6615694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6615735 : List Nat := [1, 1, 3, 1, 7, 1, 2, 2, 5]
def baseStart_6615735 : Nat := 118140960795 + 6615735 * 2 ^ 59
def prefixEnd_6615735 : Nat := 4983230072969 + 3 ^ 40 * 6615735 * 2
def baseEnd_6615735 : Nat := 377450215308086515565255

theorem tailTrace_6615735 : CollatzResearch.WordTrace tailWord_6615735 prefixEnd_6615735 377450215308086515565255 := by
  unfold tailWord_6615735
  simp only [CollatzResearch.WordTrace]
  refine ⟨241295678687329447428960659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160863785791552964952640439 241295678687329447428960659)
  ·
    refine ⟨361943518030994171143440989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241295678687329447428960659 361943518030994171143440989)
    ·
      refine ⟨135728819261622814178790371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 361943518030994171143440989 135728819261622814178790371)
      ·
        refine ⟨203593228892434221268185557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135728819261622814178790371 203593228892434221268185557)
        ·
          refine ⟨4771716302166427060973099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 203593228892434221268185557 4771716302166427060973099)
          ·
            refine ⟨7157574453249640591459649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4771716302166427060973099 7157574453249640591459649)
            ·
              refine ⟨5368180839937230443594737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7157574453249640591459649 5368180839937230443594737)
              ·
                refine ⟨4026135629952922832696053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5368180839937230443594737 4026135629952922832696053)
                ·
                  refine ⟨377450215308086515565255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4026135629952922832696053 377450215308086515565255)
                  ·
                    rfl

theorem cell23_6615735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 2, 2, 5].length) (baseStart_6615735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6615735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6615735 prefixEnd_6615735 := by exact prefixLift 6615735
  have htrace : WordTrace (prefixWord ++ tailWord_6615735) baseStart_6615735 baseEnd_6615735 := by
    simpa [prefixWord, tailWord_6615735, baseEnd_6615735] using wordTrace_append hprefix tailTrace_6615735
  have hstable : (prefixWord ++ tailWord_6615735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6615735).length < 2 ^ (prefixWord ++ tailWord_6615735).sum := by decide
  have hdescent : baseEnd_6615735 < baseStart_6615735 := by decide
  rcases family_descends (prefixWord ++ tailWord_6615735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6615737 : List Nat := [1, 2, 1, 4, 1, 1, 1, 1, 1, 5, 5]
def baseStart_6615737 : Nat := 118140960795 + 6615737 * 2 ^ 59
def prefixEnd_6615737 : Nat := 4983230072969 + 3 ^ 40 * 6615737 * 2
def baseEnd_6615737 : Nat := 3397052964734087632262285

theorem tailTrace_6615737 : CollatzResearch.WordTrace tailWord_6615737 prefixEnd_6615737 3397052964734087632262285 := by
  unfold tailWord_6615737
  simp only [CollatzResearch.WordTrace]
  refine ⟨241295751633322201770533465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160863834422214801180355643 241295751633322201770533465)
  ·
    refine ⟨180971813724991651327900099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241295751633322201770533465 180971813724991651327900099)
    ·
      refine ⟨271457720587487476991850149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180971813724991651327900099 271457720587487476991850149)
      ·
        refine ⟨50898322610153901935971903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 271457720587487476991850149 50898322610153901935971903)
        ·
          refine ⟨76347483915230852903957855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50898322610153901935971903 76347483915230852903957855)
          ·
            refine ⟨114521225872846279355936783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76347483915230852903957855 114521225872846279355936783)
            ·
              refine ⟨171781838809269419033905175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114521225872846279355936783 171781838809269419033905175)
              ·
                refine ⟨257672758213904128550857763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 171781838809269419033905175 257672758213904128550857763)
                ·
                  refine ⟨386509137320856192826286645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 257672758213904128550857763 386509137320856192826286645)
                  ·
                    refine ⟨36235231623830268077464373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 386509137320856192826286645 36235231623830268077464373)
                    ·
                      refine ⟨3397052964734087632262285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36235231623830268077464373 3397052964734087632262285)
                      ·
                        rfl

theorem cell23_6615737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 5, 5].length) (baseStart_6615737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6615737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6615737 prefixEnd_6615737 := by exact prefixLift 6615737
  have htrace : WordTrace (prefixWord ++ tailWord_6615737) baseStart_6615737 baseEnd_6615737 := by
    simpa [prefixWord, tailWord_6615737, baseEnd_6615737] using wordTrace_append hprefix tailTrace_6615737
  have hstable : (prefixWord ++ tailWord_6615737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6615737).length < 2 ^ (prefixWord ++ tailWord_6615737).sum := by decide
  have hdescent : baseEnd_6615737 < baseStart_6615737 := by decide
  rcases family_descends (prefixWord ++ tailWord_6615737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6615765 : List Nat := [1, 3, 2, 5, 2, 1, 1, 1, 2, 5]
def baseStart_6615765 : Nat := 118140960795 + 6615765 * 2 ^ 59
def prefixEnd_6615765 : Nat := 4983230072969 + 3 ^ 40 * 6615765 * 2
def baseEnd_6615765 : Nat := 1132355780730804507570719

theorem tailTrace_6615765 : CollatzResearch.WordTrace tailWord_6615765 prefixEnd_6615765 1132355780730804507570719 := by
  unfold tailWord_6615765
  simp only [CollatzResearch.WordTrace]
  refine ⟨241296772877220762552552749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160864515251480508368368499 241296772877220762552552749)
  ·
    refine ⟨90486289828957785957207281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 241296772877220762552552749 90486289828957785957207281)
    ·
      refine ⟨67864717371718339467905461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90486289828957785957207281 67864717371718339467905461)
      ·
        refine ⟨6362317253598594325116137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 67864717371718339467905461 6362317253598594325116137)
        ·
          refine ⟨4771737940198945743837103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6362317253598594325116137 4771737940198945743837103)
          ·
            refine ⟨7157606910298418615755655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4771737940198945743837103 7157606910298418615755655)
            ·
              refine ⟨10736410365447627923633483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7157606910298418615755655 10736410365447627923633483)
              ·
                refine ⟨16104615548171441885450225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10736410365447627923633483 16104615548171441885450225)
                ·
                  refine ⟨12078461661128581414087669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16104615548171441885450225 12078461661128581414087669)
                  ·
                    refine ⟨1132355780730804507570719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12078461661128581414087669 1132355780730804507570719)
                    ·
                      rfl

theorem cell23_6615765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 1, 1, 2, 5].length) (baseStart_6615765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6615765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6615765 prefixEnd_6615765 := by exact prefixLift 6615765
  have htrace : WordTrace (prefixWord ++ tailWord_6615765) baseStart_6615765 baseEnd_6615765 := by
    simpa [prefixWord, tailWord_6615765, baseEnd_6615765] using wordTrace_append hprefix tailTrace_6615765
  have hstable : (prefixWord ++ tailWord_6615765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6615765).length < 2 ^ (prefixWord ++ tailWord_6615765).sum := by decide
  have hdescent : baseEnd_6615765 < baseStart_6615765 := by decide
  rcases family_descends (prefixWord ++ tailWord_6615765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6615791 : List Nat := [1, 1, 2, 1, 5, 4, 1, 2, 6]
def baseStart_6615791 : Nat := 118140960795 + 6615791 * 2 ^ 59
def prefixEnd_6615791 : Nat := 4983230072969 + 3 ^ 40 * 6615791 * 2
def baseEnd_6615791 : Nat := 377453410298825602331893

theorem tailTrace_6615791 : CollatzResearch.WordTrace tailWord_6615791 prefixEnd_6615791 377453410298825602331893 := by
  unfold tailWord_6615791
  simp only [CollatzResearch.WordTrace]
  refine ⟨241297721175126568992999227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160865147450084379328666151 241297721175126568992999227)
  ·
    refine ⟨361946581762689853489498841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241297721175126568992999227 361946581762689853489498841)
    ·
      refine ⟨271459936322017390117124131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 361946581762689853489498841 271459936322017390117124131)
      ·
        refine ⟨407189904483026085175686197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271459936322017390117124131 407189904483026085175686197)
        ·
          refine ⟨38174053545283695485220581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 407189904483026085175686197 38174053545283695485220581)
          ·
            refine ⟨7157635039740692903478859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38174053545283695485220581 7157635039740692903478859)
            ·
              refine ⟨10736452559611039355218289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7157635039740692903478859 10736452559611039355218289)
              ·
                refine ⟨8052339419708279516413717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10736452559611039355218289 8052339419708279516413717)
                ·
                  refine ⟨377453410298825602331893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8052339419708279516413717 377453410298825602331893)
                  ·
                    rfl

theorem cell23_6615791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 1, 2, 6].length) (baseStart_6615791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6615791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6615791 prefixEnd_6615791 := by exact prefixLift 6615791
  have htrace : WordTrace (prefixWord ++ tailWord_6615791) baseStart_6615791 baseEnd_6615791 := by
    simpa [prefixWord, tailWord_6615791, baseEnd_6615791] using wordTrace_append hprefix tailTrace_6615791
  have hstable : (prefixWord ++ tailWord_6615791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6615791).length < 2 ^ (prefixWord ++ tailWord_6615791).sum := by decide
  have hdescent : baseEnd_6615791 < baseStart_6615791 := by decide
  rcases family_descends (prefixWord ++ tailWord_6615791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6615794 : List Nat := [3, 2, 1, 3, 1, 2, 1, 1, 1, 2, 6]
def baseStart_6615794 : Nat := 118140960795 + 6615794 * 2 ^ 59
def prefixEnd_6615794 : Nat := 4983230072969 + 3 ^ 40 * 6615794 * 2
def baseEnd_6615794 : Nat := 3397082233131393909249523

theorem tailTrace_6615794 : CollatzResearch.WordTrace tailWord_6615794 prefixEnd_6615794 3397082233131393909249523 := by
  unfold tailWord_6615794
  simp only [CollatzResearch.WordTrace]
  refine ⟨60324457648528925126339609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160865220396077133670238957 60324457648528925126339609)
  ·
    refine ⟨45243343236396693844754707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60324457648528925126339609 45243343236396693844754707)
    ·
      refine ⟨67865014854595040767132061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45243343236396693844754707 67865014854595040767132061)
      ·
        refine ⟨25449380570473140287674523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67865014854595040767132061 25449380570473140287674523)
        ·
          refine ⟨38174070855709710431511785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25449380570473140287674523 38174070855709710431511785)
          ·
            refine ⟨28630553141782282823633839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38174070855709710431511785 28630553141782282823633839)
            ·
              refine ⟨42945829712673424235450759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28630553141782282823633839 42945829712673424235450759)
              ·
                refine ⟨64418744569010136353176139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42945829712673424235450759 64418744569010136353176139)
                ·
                  refine ⟨96628116853515204529764209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64418744569010136353176139 96628116853515204529764209)
                  ·
                    refine ⟨72471087640136403397323157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 96628116853515204529764209 72471087640136403397323157)
                    ·
                      refine ⟨3397082233131393909249523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72471087640136403397323157 3397082233131393909249523)
                      ·
                        rfl

theorem cell23_6615794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_6615794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6615794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6615794 prefixEnd_6615794 := by exact prefixLift 6615794
  have htrace : WordTrace (prefixWord ++ tailWord_6615794) baseStart_6615794 baseEnd_6615794 := by
    simpa [prefixWord, tailWord_6615794, baseEnd_6615794] using wordTrace_append hprefix tailTrace_6615794
  have hstable : (prefixWord ++ tailWord_6615794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6615794).length < 2 ^ (prefixWord ++ tailWord_6615794).sum := by decide
  have hdescent : baseEnd_6615794 < baseStart_6615794 := by decide
  rcases family_descends (prefixWord ++ tailWord_6615794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6615834 : List Nat := [3, 1, 1, 3, 2, 1, 2, 1, 3, 6]
def baseStart_6615834 : Nat := 118140960795 + 6615834 * 2 ^ 59
def prefixEnd_6615834 : Nat := 4983230072969 + 3 ^ 40 * 6615834 * 2
def baseEnd_6615834 : Nat := 1132367590785857917583113

theorem tailTrace_6615834 : CollatzResearch.WordTrace tailWord_6615834 prefixEnd_6615834 1132367590785857917583113 := by
  unfold tailWord_6615834
  simp only [CollatzResearch.WordTrace]
  refine ⟨60324822378492696834203639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160866193009313858224543037 60324822378492696834203639)
  ·
    refine ⟨90487233567739045251305459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60324822378492696834203639 90487233567739045251305459)
    ·
      refine ⟨135730850351608567876958189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90487233567739045251305459 135730850351608567876958189)
      ·
        refine ⟨50899068881853212953859321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135730850351608567876958189 50899068881853212953859321)
        ·
          refine ⟨38174301661389909715394491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50899068881853212953859321 38174301661389909715394491)
          ·
            refine ⟨57261452492084864573091737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38174301661389909715394491 57261452492084864573091737)
            ·
              refine ⟨42946089369063648429818803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57261452492084864573091737 42946089369063648429818803)
              ·
                refine ⟨64419134053595472644728205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42946089369063648429818803 64419134053595472644728205)
                ·
                  refine ⟨24157175270098302241773077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64419134053595472644728205 24157175270098302241773077)
                  ·
                    refine ⟨1132367590785857917583113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24157175270098302241773077 1132367590785857917583113)
                    ·
                      rfl

theorem cell23_6615834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 1, 3, 6].length) (baseStart_6615834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6615834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6615834 prefixEnd_6615834 := by exact prefixLift 6615834
  have htrace : WordTrace (prefixWord ++ tailWord_6615834) baseStart_6615834 baseEnd_6615834 := by
    simpa [prefixWord, tailWord_6615834, baseEnd_6615834] using wordTrace_append hprefix tailTrace_6615834
  have hstable : (prefixWord ++ tailWord_6615834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6615834).length < 2 ^ (prefixWord ++ tailWord_6615834).sum := by decide
  have hdescent : baseEnd_6615834 < baseStart_6615834 := by decide
  rcases family_descends (prefixWord ++ tailWord_6615834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6615841 : List Nat := [1, 2, 3, 2, 1, 2, 1, 5, 1, 1, 4]
def baseStart_6615841 : Nat := 118140960795 + 6615841 * 2 ^ 59
def prefixEnd_6615841 : Nat := 4983230072969 + 3 ^ 40 * 6615841 * 2
def baseEnd_6615841 : Nat := 3397106366722155225361807

theorem tailTrace_6615841 : CollatzResearch.WordTrace tailWord_6615841 prefixEnd_6615841 3397106366722155225361807 := by
  unfold tailWord_6615841
  simp only [CollatzResearch.WordTrace]
  refine ⟨241299544824945427532319377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160866363216630285021546251 241299544824945427532319377)
  ·
    refine ⟨180974658618709070649239533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241299544824945427532319377 180974658618709070649239533)
    ·
      refine ⟨67865496982015901493464825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180974658618709070649239533 67865496982015901493464825)
      ·
        refine ⟨50899122736511926120098619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67865496982015901493464825 50899122736511926120098619)
        ·
          refine ⟨76348684104767889180147929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50899122736511926120098619 76348684104767889180147929)
          ·
            refine ⟨57261513078575916885110947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76348684104767889180147929 57261513078575916885110947)
            ·
              refine ⟨85892269617863875327666421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57261513078575916885110947 85892269617863875327666421)
              ·
                refine ⟨8052400276674738311968727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 85892269617863875327666421 8052400276674738311968727)
                ·
                  refine ⟨12078600415012107467953091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8052400276674738311968727 12078600415012107467953091)
                  ·
                    refine ⟨18117900622518161201929637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12078600415012107467953091 18117900622518161201929637)
                    ·
                      refine ⟨3397106366722155225361807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18117900622518161201929637 3397106366722155225361807)
                      ·
                        rfl

theorem cell23_6615841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 5, 1, 1, 4].length) (baseStart_6615841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6615841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6615841 prefixEnd_6615841 := by exact prefixLift 6615841
  have htrace : WordTrace (prefixWord ++ tailWord_6615841) baseStart_6615841 baseEnd_6615841 := by
    simpa [prefixWord, tailWord_6615841, baseEnd_6615841] using wordTrace_append hprefix tailTrace_6615841
  have hstable : (prefixWord ++ tailWord_6615841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6615841).length < 2 ^ (prefixWord ++ tailWord_6615841).sum := by decide
  have hdescent : baseEnd_6615841 < baseStart_6615841 := by decide
  rcases family_descends (prefixWord ++ tailWord_6615841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6615861 : List Nat := [1, 3, 3, 1, 3, 1, 2, 2, 1, 1, 5]
def baseStart_6615861 : Nat := 118140960795 + 6615861 * 2 ^ 59
def prefixEnd_6615861 : Nat := 4983230072969 + 3 ^ 40 * 6615861 * 2
def baseEnd_6615861 : Nat := 3397116636335245147111715

theorem tailTrace_6615861 : CollatzResearch.WordTrace tailWord_6615861 prefixEnd_6615861 3397116636335245147111715 := by
  unfold tailWord_6615861
  simp only [CollatzResearch.WordTrace]
  refine ⟨241300274284872970948047437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160866849523248647298698291 241300274284872970948047437)
  ·
    refine ⟨90487602856827364105517789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 241300274284872970948047437 90487602856827364105517789)
    ·
      refine ⟨33932851071310261539569171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90487602856827364105517789 33932851071310261539569171)
      ·
        refine ⟨50899276606965392309353757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33932851071310261539569171 50899276606965392309353757)
        ·
          refine ⟨19087228727612022116007659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50899276606965392309353757 19087228727612022116007659)
          ·
            refine ⟨28630843091418033174011489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19087228727612022116007659 28630843091418033174011489)
            ·
              refine ⟨21473132318563524880508617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28630843091418033174011489 21473132318563524880508617)
              ·
                refine ⟨16104849238922643660381463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21473132318563524880508617 16104849238922643660381463)
                ·
                  refine ⟨24157273858383965490572195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16104849238922643660381463 24157273858383965490572195)
                  ·
                    refine ⟨36235910787575948235858293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24157273858383965490572195 36235910787575948235858293)
                    ·
                      refine ⟨3397116636335245147111715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36235910787575948235858293 3397116636335245147111715)
                      ·
                        rfl

theorem cell23_6615861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 2, 1, 1, 5].length) (baseStart_6615861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6615861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6615861 prefixEnd_6615861 := by exact prefixLift 6615861
  have htrace : WordTrace (prefixWord ++ tailWord_6615861) baseStart_6615861 baseEnd_6615861 := by
    simpa [prefixWord, tailWord_6615861, baseEnd_6615861] using wordTrace_append hprefix tailTrace_6615861
  have hstable : (prefixWord ++ tailWord_6615861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6615861).length < 2 ^ (prefixWord ++ tailWord_6615861).sum := by decide
  have hdescent : baseEnd_6615861 < baseStart_6615861 := by decide
  rcases family_descends (prefixWord ++ tailWord_6615861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6615864 : List Nat := [2, 1, 2, 1, 3, 2, 4, 8]
def baseStart_6615864 : Nat := 118140960795 + 6615864 * 2 ^ 59
def prefixEnd_6615864 : Nat := 4983230072969 + 3 ^ 40 * 6615864 * 2
def baseEnd_6615864 : Nat := 125819191732489208717563

theorem tailTrace_6615864 : CollatzResearch.WordTrace tailWord_6615864 prefixEnd_6615864 125819191732489208717563 := by
  unfold tailWord_6615864
  simp only [CollatzResearch.WordTrace]
  refine ⟨120650191851931051230203323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160866922469241401640271097 120650191851931051230203323)
  ·
    refine ⟨180975287777896576845304985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120650191851931051230203323 180975287777896576845304985)
    ·
      refine ⟨135731465833422432633978739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180975287777896576845304985 135731465833422432633978739)
      ·
        refine ⟨203597198750133648950968109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135731465833422432633978739 203597198750133648950968109)
        ·
          refine ⟨76348949531300118356613041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 203597198750133648950968109 76348949531300118356613041)
          ·
            refine ⟨57261712148475088767459781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76348949531300118356613041 57261712148475088767459781)
            ·
              refine ⟨10736571027839079143898709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57261712148475088767459781 10736571027839079143898709)
              ·
                refine ⟨125819191732489208717563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10736571027839079143898709 125819191732489208717563)
                ·
                  rfl

theorem cell23_6615864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 4, 8].length) (baseStart_6615864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6615864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6615864 prefixEnd_6615864 := by exact prefixLift 6615864
  have htrace : WordTrace (prefixWord ++ tailWord_6615864) baseStart_6615864 baseEnd_6615864 := by
    simpa [prefixWord, tailWord_6615864, baseEnd_6615864] using wordTrace_append hprefix tailTrace_6615864
  have hstable : (prefixWord ++ tailWord_6615864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6615864).length < 2 ^ (prefixWord ++ tailWord_6615864).sum := by decide
  have hdescent : baseEnd_6615864 < baseStart_6615864 := by decide
  rcases family_descends (prefixWord ++ tailWord_6615864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6615891 : List Nat := [1, 1, 1, 2, 1, 1, 3, 3, 6, 1, 3]
def baseStart_6615891 : Nat := 118140960795 + 6615891 * 2 ^ 59
def prefixEnd_6615891 : Nat := 4983230072969 + 3 ^ 40 * 6615891 * 2
def baseEnd_6615891 : Nat := 3397132040754880029736577

theorem tailTrace_6615891 : CollatzResearch.WordTrace tailWord_6615891 prefixEnd_6615891 3397132040754880029736577 := by
  unfold tailWord_6615891
  simp only [CollatzResearch.WordTrace]
  refine ⟨241301368474764286071639527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160867578983176190714426351 241301368474764286071639527)
  ·
    refine ⟨361952052712146429107459291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241301368474764286071639527 361952052712146429107459291)
    ·
      refine ⟨542928079068219643661188937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 361952052712146429107459291 542928079068219643661188937)
      ·
        refine ⟨407196059301164732745891703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 542928079068219643661188937 407196059301164732745891703)
        ·
          refine ⟨610794088951747099118837555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 407196059301164732745891703 610794088951747099118837555)
          ·
            refine ⟨916191133427620648678256333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 610794088951747099118837555 916191133427620648678256333)
            ·
              refine ⟨343571675035357743254346125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 916191133427620648678256333 343571675035357743254346125)
              ·
                refine ⟨128839378138259153720379797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 343571675035357743254346125 128839378138259153720379797)
                ·
                  refine ⟨6039345850230897830642803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 128839378138259153720379797 6039345850230897830642803)
                  ·
                    refine ⟨9059018775346346745964205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6039345850230897830642803 9059018775346346745964205)
                    ·
                      refine ⟨3397132040754880029736577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9059018775346346745964205 3397132040754880029736577)
                      ·
                        rfl

theorem cell23_6615891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 3, 6, 1, 3].length) (baseStart_6615891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6615891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6615891 prefixEnd_6615891 := by exact prefixLift 6615891
  have htrace : WordTrace (prefixWord ++ tailWord_6615891) baseStart_6615891 baseEnd_6615891 := by
    simpa [prefixWord, tailWord_6615891, baseEnd_6615891] using wordTrace_append hprefix tailTrace_6615891
  have hstable : (prefixWord ++ tailWord_6615891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6615891).length < 2 ^ (prefixWord ++ tailWord_6615891).sum := by decide
  have hdescent : baseEnd_6615891 < baseStart_6615891 := by decide
  rcases family_descends (prefixWord ++ tailWord_6615891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6615895 : List Nat := [1, 1, 3, 2, 4, 2, 3, 1, 1, 2, 3]
def baseStart_6615895 : Nat := 118140960795 + 6615895 * 2 ^ 59
def prefixEnd_6615895 : Nat := 4983230072969 + 3 ^ 40 * 6615895 * 2
def baseEnd_6615895 : Nat := 3397134094677498014086559

theorem tailTrace_6615895 : CollatzResearch.WordTrace tailWord_6615895 prefixEnd_6615895 3397134094677498014086559 := by
  unfold tailWord_6615895
  simp only [CollatzResearch.WordTrace]
  refine ⟨241301514366749794754785139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160867676244499863169856759 241301514366749794754785139)
  ·
    refine ⟨361952271550124692132177709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241301514366749794754785139 361952271550124692132177709)
    ·
      refine ⟨135732101831296759549566641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 361952271550124692132177709 135732101831296759549566641)
      ·
        refine ⟨101799076373472569662174981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135732101831296759549566641 101799076373472569662174981)
        ·
          refine ⟨19087326820026106811657809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 101799076373472569662174981 19087326820026106811657809)
          ·
            refine ⟨14315495115019580108743357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19087326820026106811657809 14315495115019580108743357)
            ·
              refine ⟨5368310668132342540778759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14315495115019580108743357 5368310668132342540778759)
              ·
                refine ⟨8052466002198513811168139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5368310668132342540778759 8052466002198513811168139)
                ·
                  refine ⟨12078699003297770716752209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8052466002198513811168139 12078699003297770716752209)
                  ·
                    refine ⟨9059024252473328037564157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12078699003297770716752209 9059024252473328037564157)
                    ·
                      refine ⟨3397134094677498014086559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9059024252473328037564157 3397134094677498014086559)
                      ·
                        rfl

theorem cell23_6615895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 3, 1, 1, 2, 3].length) (baseStart_6615895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6615895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6615895 prefixEnd_6615895 := by exact prefixLift 6615895
  have htrace : WordTrace (prefixWord ++ tailWord_6615895) baseStart_6615895 baseEnd_6615895 := by
    simpa [prefixWord, tailWord_6615895, baseEnd_6615895] using wordTrace_append hprefix tailTrace_6615895
  have hstable : (prefixWord ++ tailWord_6615895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6615895).length < 2 ^ (prefixWord ++ tailWord_6615895).sum := by decide
  have hdescent : baseEnd_6615895 < baseStart_6615895 := by decide
  rcases family_descends (prefixWord ++ tailWord_6615895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6615925 : List Nat := [1, 3, 4, 1, 1, 2, 2, 3, 2, 1, 3]
def baseStart_6615925 : Nat := 118140960795 + 6615925 * 2 ^ 59
def prefixEnd_6615925 : Nat := 4983230072969 + 3 ^ 40 * 6615925 * 2
def baseEnd_6615925 : Nat := 3397149499097132896711421

theorem tailTrace_6615925 : CollatzResearch.WordTrace tailWord_6615925 prefixEnd_6615925 3397149499097132896711421 := by
  unfold tailWord_6615925
  simp only [CollatzResearch.WordTrace]
  refine ⟨241302608556641109878377229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160868405704427406585584819 241302608556641109878377229)
  ·
    refine ⟨90488478208740416204391461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 241302608556641109878377229 90488478208740416204391461)
    ·
      refine ⟨16966589664138828038323399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90488478208740416204391461 16966589664138828038323399)
      ·
        refine ⟨25449884496208242057485099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16966589664138828038323399 25449884496208242057485099)
        ·
          refine ⟨38174826744312363086227649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25449884496208242057485099 38174826744312363086227649)
          ·
            refine ⟨28631120058234272314670737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38174826744312363086227649 28631120058234272314670737)
            ·
              refine ⟨21473340043675704236003053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28631120058234272314670737 21473340043675704236003053)
              ·
                refine ⟨8052502516378389088501145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21473340043675704236003053 8052502516378389088501145)
                ·
                  refine ⟨6039376887283791816375859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8052502516378389088501145 6039376887283791816375859)
                  ·
                    refine ⟨9059065330925687724563789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6039376887283791816375859 9059065330925687724563789)
                    ·
                      refine ⟨3397149499097132896711421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9059065330925687724563789 3397149499097132896711421)
                      ·
                        rfl

theorem cell23_6615925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 3, 2, 1, 3].length) (baseStart_6615925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6615925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6615925 prefixEnd_6615925 := by exact prefixLift 6615925
  have htrace : WordTrace (prefixWord ++ tailWord_6615925) baseStart_6615925 baseEnd_6615925 := by
    simpa [prefixWord, tailWord_6615925, baseEnd_6615925] using wordTrace_append hprefix tailTrace_6615925
  have hstable : (prefixWord ++ tailWord_6615925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6615925).length < 2 ^ (prefixWord ++ tailWord_6615925).sum := by decide
  have hdescent : baseEnd_6615925 < baseStart_6615925 := by decide
  rcases family_descends (prefixWord ++ tailWord_6615925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6615948 : List Nat := [2, 2, 1, 2, 1, 2, 4, 2, 1, 4, 2]
def baseStart_6615948 : Nat := 118140960795 + 6615948 * 2 ^ 59
def prefixEnd_6615948 : Nat := 4983230072969 + 3 ^ 40 * 6615948 * 2
def baseEnd_6615948 : Nat := 3397161309152186306723815

theorem tailTrace_6615948 : CollatzResearch.WordTrace tailWord_6615948 prefixEnd_6615948 3397161309152186306723815 := by
  unfold tailWord_6615948
  simp only [CollatzResearch.WordTrace]
  refine ⟨120651723717778892403232249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160868964957038523204309665 120651723717778892403232249)
  ·
    refine ⟨90488792788334169302424187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120651723717778892403232249 90488792788334169302424187)
    ·
      refine ⟨135733189182501253953636281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90488792788334169302424187 135733189182501253953636281)
      ·
        refine ⟨101799891886875940465227211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135733189182501253953636281 101799891886875940465227211)
        ·
          refine ⟨152699837830313910697840817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101799891886875940465227211 152699837830313910697840817)
          ·
            refine ⟨114524878372735433023380613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152699837830313910697840817 114524878372735433023380613)
            ·
              refine ⟨21473414694887893691883865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 114524878372735433023380613 21473414694887893691883865)
              ·
                refine ⟨16105061021165920268912899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21473414694887893691883865 16105061021165920268912899)
                ·
                  refine ⟨24157591531748880403369349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16105061021165920268912899 24157591531748880403369349)
                  ·
                    refine ⟨4529548412202915075631753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24157591531748880403369349 4529548412202915075631753)
                    ·
                      refine ⟨3397161309152186306723815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4529548412202915075631753 3397161309152186306723815)
                      ·
                        rfl

theorem cell23_6615948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 2, 1, 4, 2].length) (baseStart_6615948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6615948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6615948 prefixEnd_6615948 := by exact prefixLift 6615948
  have htrace : WordTrace (prefixWord ++ tailWord_6615948) baseStart_6615948 baseEnd_6615948 := by
    simpa [prefixWord, tailWord_6615948, baseEnd_6615948] using wordTrace_append hprefix tailTrace_6615948
  have hstable : (prefixWord ++ tailWord_6615948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6615948).length < 2 ^ (prefixWord ++ tailWord_6615948).sum := by decide
  have hdescent : baseEnd_6615948 < baseStart_6615948 := by decide
  rcases family_descends (prefixWord ++ tailWord_6615948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6615965 : List Nat := [1, 4, 2, 1, 2, 1, 3, 1, 4, 2, 2]
def baseStart_6615965 : Nat := 118140960795 + 6615965 * 2 ^ 59
def prefixEnd_6615965 : Nat := 4983230072969 + 3 ^ 40 * 6615965 * 2
def baseEnd_6615965 : Nat := 3397170038323312740211237

theorem tailTrace_6615965 : CollatzResearch.WordTrace tailWord_6615965 prefixEnd_6615965 3397170038323312740211237 := by
  unfold tailWord_6615965
  simp only [CollatzResearch.WordTrace]
  refine ⟨241304067476496196709833349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160869378317664131139888899 241304067476496196709833349)
  ·
    refine ⟨45244512651843036883093753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 241304067476496196709833349 45244512651843036883093753)
    ·
      refine ⟨33933384488882277662320315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45244512651843036883093753 33933384488882277662320315)
      ·
        refine ⟨50900076733323416493480473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33933384488882277662320315 50900076733323416493480473)
        ·
          refine ⟨38175057549992562370110355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50900076733323416493480473 38175057549992562370110355)
          ·
            refine ⟨57262586324988843555165533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38175057549992562370110355 57262586324988843555165533)
            ·
              refine ⟨21473469871870816333187075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57262586324988843555165533 21473469871870816333187075)
              ·
                refine ⟨32210204807806224499780613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21473469871870816333187075 32210204807806224499780613)
                ·
                  refine ⟨6039413401463667093708865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32210204807806224499780613 6039413401463667093708865)
                  ·
                    refine ⟨4529560051097750320281649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6039413401463667093708865 4529560051097750320281649)
                    ·
                      refine ⟨3397170038323312740211237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4529560051097750320281649 3397170038323312740211237)
                      ·
                        rfl

theorem cell23_6615965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 1, 4, 2, 2].length) (baseStart_6615965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6615965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6615965 prefixEnd_6615965 := by exact prefixLift 6615965
  have htrace : WordTrace (prefixWord ++ tailWord_6615965) baseStart_6615965 baseEnd_6615965 := by
    simpa [prefixWord, tailWord_6615965, baseEnd_6615965] using wordTrace_append hprefix tailTrace_6615965
  have hstable : (prefixWord ++ tailWord_6615965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6615965).length < 2 ^ (prefixWord ++ tailWord_6615965).sum := by decide
  have hdescent : baseEnd_6615965 < baseStart_6615965 := by decide
  rcases family_descends (prefixWord ++ tailWord_6615965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
