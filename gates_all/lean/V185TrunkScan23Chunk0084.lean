import V185TrunkScan23Chunk0083

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_499053 : List Nat := [1, 5, 1, 1, 1, 4, 1, 2, 1, 1, 5]
def baseStart_499053 : Nat := 118140960795 + 499053 * 2 ^ 59
def prefixEnd_499053 : Nat := 4983230072969 + 3 ^ 40 * 499053 * 2
def baseEnd_499053 : Nat := 256254061068341186542403

theorem tailTrace_499053 : CollatzResearch.WordTrace tailWord_499053 prefixEnd_499053 256254061068341186542403 := by
  unfold tailWord_499053
  simp only [CollatzResearch.WordTrace]
  refine ⟨18201958261023687311885813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12134638840682458207923875 18201958261023687311885813)
  ·
    refine ⟨1706433586970970685489295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18201958261023687311885813 1706433586970970685489295)
    ·
      refine ⟨2559650380456456028233943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1706433586970970685489295 2559650380456456028233943)
      ·
        refine ⟨3839475570684684042350915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2559650380456456028233943 3839475570684684042350915)
        ·
          refine ⟨5759213356027026063526373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3839475570684684042350915 5759213356027026063526373)
          ·
            refine ⟨1079852504255067386911195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5759213356027026063526373 1079852504255067386911195)
            ·
              refine ⟨1619778756382601080366793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1079852504255067386911195 1619778756382601080366793)
              ·
                refine ⟨1214834067286950810275095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1619778756382601080366793 1214834067286950810275095)
                ·
                  refine ⟨1822251100930426215412643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1214834067286950810275095 1822251100930426215412643)
                  ·
                    refine ⟨2733376651395639323118965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1822251100930426215412643 2733376651395639323118965)
                    ·
                      refine ⟨256254061068341186542403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2733376651395639323118965 256254061068341186542403)
                      ·
                        rfl

theorem cell23_499053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 2, 1, 1, 5].length) (baseStart_499053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_499053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_499053 prefixEnd_499053 := by exact prefixLift 499053
  have htrace : WordTrace (prefixWord ++ tailWord_499053) baseStart_499053 baseEnd_499053 := by
    simpa [prefixWord, tailWord_499053, baseEnd_499053] using wordTrace_append hprefix tailTrace_499053
  have hstable : (prefixWord ++ tailWord_499053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499053).length < 2 ^ (prefixWord ++ tailWord_499053).sum := by decide
  have hdescent : baseEnd_499053 < baseStart_499053 := by decide
  rcases family_descends (prefixWord ++ tailWord_499053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499073 : List Nat := [1, 2, 4, 3, 2, 1, 1, 9]
def baseStart_499073 : Nat := 118140960795 + 499073 * 2 ^ 59
def prefixEnd_499073 : Nat := 4983230072969 + 3 ^ 40 * 499073 * 2
def baseEnd_499073 : Nat := 9491271506719670677493

theorem tailTrace_499073 : CollatzResearch.WordTrace tailWord_499073 prefixEnd_499073 9491271506719670677493 := by
  unfold tailWord_499073
  simp only [CollatzResearch.WordTrace]
  refine ⟨18202687720951230727613873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12135125147300820485075915 18202687720951230727613873)
  ·
    refine ⟨13652015790713423045710405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18202687720951230727613873 13652015790713423045710405)
    ·
      refine ⟨2559752960758766821070701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13652015790713423045710405 2559752960758766821070701)
      ·
        refine ⟨959907360284537557901513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2559752960758766821070701 959907360284537557901513)
        ·
          refine ⟨719930520213403168426135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 959907360284537557901513 719930520213403168426135)
          ·
            refine ⟨1079895780320104752639203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 719930520213403168426135 1079895780320104752639203)
            ·
              refine ⟨1619843670480157128958805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1079895780320104752639203 1619843670480157128958805)
              ·
                refine ⟨9491271506719670677493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1619843670480157128958805 9491271506719670677493)
                ·
                  rfl

theorem cell23_499073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 9].length) (baseStart_499073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_499073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_499073 prefixEnd_499073 := by exact prefixLift 499073
  have htrace : WordTrace (prefixWord ++ tailWord_499073) baseStart_499073 baseEnd_499073 := by
    simpa [prefixWord, tailWord_499073, baseEnd_499073] using wordTrace_append hprefix tailTrace_499073
  have hstable : (prefixWord ++ tailWord_499073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499073).length < 2 ^ (prefixWord ++ tailWord_499073).sum := by decide
  have hdescent : baseEnd_499073 < baseStart_499073 := by decide
  rcases family_descends (prefixWord ++ tailWord_499073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499083 : List Nat := [1, 1, 1, 1, 4, 3, 1, 1, 6, 1, 3]
def baseStart_499083 : Nat := 118140960795 + 499083 * 2 ^ 59
def prefixEnd_499083 : Nat := 4983230072969 + 3 ^ 40 * 499083 * 2
def baseEnd_499083 : Nat := 256269465487976069167265

theorem tailTrace_499083 : CollatzResearch.WordTrace tailWord_499083 prefixEnd_499083 256269465487976069167265 := by
  unfold tailWord_499083
  simp only [CollatzResearch.WordTrace]
  refine ⟨18203052450915002435477903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12135368300610001623651935 18203052450915002435477903)
  ·
    refine ⟨27304578676372503653216855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18203052450915002435477903 27304578676372503653216855)
    ·
      refine ⟨40956868014558755479825283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27304578676372503653216855 40956868014558755479825283)
      ·
        refine ⟨61435302021838133219737925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40956868014558755479825283 61435302021838133219737925)
        ·
          refine ⟨11519119129094649978700861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61435302021838133219737925 11519119129094649978700861)
          ·
            refine ⟨4319669673410493742012823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11519119129094649978700861 4319669673410493742012823)
            ·
              refine ⟨6479504510115740613019235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4319669673410493742012823 6479504510115740613019235)
              ·
                refine ⟨9719256765173610919528853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6479504510115740613019235 9719256765173610919528853)
                ·
                  refine ⟨455590160867513011852915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9719256765173610919528853 455590160867513011852915)
                  ·
                    refine ⟨683385241301269517779373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 455590160867513011852915 683385241301269517779373)
                    ·
                      refine ⟨256269465487976069167265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 683385241301269517779373 256269465487976069167265)
                      ·
                        rfl

theorem cell23_499083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 1, 6, 1, 3].length) (baseStart_499083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_499083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_499083 prefixEnd_499083 := by exact prefixLift 499083
  have htrace : WordTrace (prefixWord ++ tailWord_499083) baseStart_499083 baseEnd_499083 := by
    simpa [prefixWord, tailWord_499083, baseEnd_499083] using wordTrace_append hprefix tailTrace_499083
  have hstable : (prefixWord ++ tailWord_499083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499083).length < 2 ^ (prefixWord ++ tailWord_499083).sum := by decide
  have hdescent : baseEnd_499083 < baseStart_499083 := by decide
  rcases family_descends (prefixWord ++ tailWord_499083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499090 : List Nat := [3, 2, 3, 3, 1, 2, 9]
def baseStart_499090 : Nat := 118140960795 + 499090 * 2 ^ 59
def prefixEnd_499090 : Nat := 4983230072969 + 3 ^ 40 * 499090 * 2
def baseEnd_499090 : Nat := 3163864936451327676293

theorem tailTrace_499090 : CollatzResearch.WordTrace tailWord_499090 prefixEnd_499090 3163864936451327676293 := by
  unfold tailWord_499090
  simp only [CollatzResearch.WordTrace]
  refine ⟨4550826940472410657745681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12135538507926428420655149 4550826940472410657745681)
  ·
    refine ⟨3413120205354307993309261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4550826940472410657745681 3413120205354307993309261)
    ·
      refine ⟨1279920077007865497490973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3413120205354307993309261 1279920077007865497490973)
      ·
        refine ⟨479970028877949561559115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1279920077007865497490973 479970028877949561559115)
        ·
          refine ⟨719955043316924342338673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 479970028877949561559115 719955043316924342338673)
          ·
            refine ⟨539966282487693256754005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 719955043316924342338673 539966282487693256754005)
            ·
              refine ⟨3163864936451327676293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 539966282487693256754005 3163864936451327676293)
              ·
                rfl

theorem cell23_499090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 9].length) (baseStart_499090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_499090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_499090 prefixEnd_499090 := by exact prefixLift 499090
  have htrace : WordTrace (prefixWord ++ tailWord_499090) baseStart_499090 baseEnd_499090 := by
    simpa [prefixWord, tailWord_499090, baseEnd_499090] using wordTrace_append hprefix tailTrace_499090
  have hstable : (prefixWord ++ tailWord_499090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499090).length < 2 ^ (prefixWord ++ tailWord_499090).sum := by decide
  have hdescent : baseEnd_499090 < baseStart_499090 := by decide
  rcases family_descends (prefixWord ++ tailWord_499090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499101 : List Nat := [1, 4, 2, 1, 3, 2, 3, 2, 1, 2, 2]
def baseStart_499101 : Nat := 118140960795 + 499101 * 2 ^ 59
def prefixEnd_499101 : Nat := 4983230072969 + 3 ^ 40 * 499101 * 2
def baseEnd_499101 : Nat := 256278708139756998742183

theorem tailTrace_499101 : CollatzResearch.WordTrace tailWord_499101 prefixEnd_499101 256278708139756998742183 := by
  unfold tailWord_499101
  simp only [CollatzResearch.WordTrace]
  refine ⟨18203708964849791509633157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12135805976566527673088771 18203708964849791509633157)
  ·
    refine ⟨3413195430909335908056217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18203708964849791509633157 3413195430909335908056217)
    ·
      refine ⟨2559896573182001931042163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3413195430909335908056217 2559896573182001931042163)
      ·
        refine ⟨3839844859773002896563245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2559896573182001931042163 3839844859773002896563245)
        ·
          refine ⟨1439941822414876086211217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3839844859773002896563245 1439941822414876086211217)
          ·
            refine ⟨1079956366811157064658413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1439941822414876086211217 1079956366811157064658413)
            ·
              refine ⟨404983637554183899246905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1079956366811157064658413 404983637554183899246905)
              ·
                refine ⟨303737728165637924435179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 404983637554183899246905 303737728165637924435179)
                ·
                  refine ⟨455606592248456886652769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 303737728165637924435179 455606592248456886652769)
                  ·
                    refine ⟨341704944186342664989577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 455606592248456886652769 341704944186342664989577)
                    ·
                      refine ⟨256278708139756998742183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 341704944186342664989577 256278708139756998742183)
                      ·
                        rfl

theorem cell23_499101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 3, 2, 1, 2, 2].length) (baseStart_499101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_499101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_499101 prefixEnd_499101 := by exact prefixLift 499101
  have htrace : WordTrace (prefixWord ++ tailWord_499101) baseStart_499101 baseEnd_499101 := by
    simpa [prefixWord, tailWord_499101, baseEnd_499101] using wordTrace_append hprefix tailTrace_499101
  have hstable : (prefixWord ++ tailWord_499101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499101).length < 2 ^ (prefixWord ++ tailWord_499101).sum := by decide
  have hdescent : baseEnd_499101 < baseStart_499101 := by decide
  rcases family_descends (prefixWord ++ tailWord_499101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499116 : List Nat := [2, 2, 1, 1, 1, 1, 4, 3, 2, 6]
def baseStart_499116 : Nat := 118140960795 + 499116 * 2 ^ 59
def prefixEnd_499116 : Nat := 4983230072969 + 3 ^ 40 * 499116 * 2
def baseEnd_499116 : Nat := 85428803449858146684871

theorem tailTrace_499116 : CollatzResearch.WordTrace tailWord_499116 prefixEnd_499116 85428803449858146684871 := by
  unfold tailWord_499116
  simp only [CollatzResearch.WordTrace]
  refine ⟨9102128029897724535714601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12136170706530299380952801 9102128029897724535714601)
  ·
    refine ⟨6826596022423293401785951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9102128029897724535714601 6826596022423293401785951)
    ·
      refine ⟨10239894033634940102678927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6826596022423293401785951 10239894033634940102678927)
      ·
        refine ⟨15359841050452410154018391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10239894033634940102678927 15359841050452410154018391)
        ·
          refine ⟨23039761575678615231027587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15359841050452410154018391 23039761575678615231027587)
          ·
            refine ⟨34559642363517922846541381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23039761575678615231027587 34559642363517922846541381)
            ·
              refine ⟨6479932943159610533726509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34559642363517922846541381 6479932943159610533726509)
              ·
                refine ⟨2429974853684853950147441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6479932943159610533726509 2429974853684853950147441)
                ·
                  refine ⟨1822481140263640462610581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2429974853684853950147441 1822481140263640462610581)
                  ·
                    refine ⟨85428803449858146684871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1822481140263640462610581 85428803449858146684871)
                    ·
                      rfl

theorem cell23_499116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 6].length) (baseStart_499116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_499116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_499116 prefixEnd_499116 := by exact prefixLift 499116
  have htrace : WordTrace (prefixWord ++ tailWord_499116) baseStart_499116 baseEnd_499116 := by
    simpa [prefixWord, tailWord_499116, baseEnd_499116] using wordTrace_append hprefix tailTrace_499116
  have hstable : (prefixWord ++ tailWord_499116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499116).length < 2 ^ (prefixWord ++ tailWord_499116).sum := by decide
  have hdescent : baseEnd_499116 < baseStart_499116 := by decide
  rcases family_descends (prefixWord ++ tailWord_499116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499123 : List Nat := [1, 1, 1, 2, 3, 1, 1, 2, 5, 4, 2]
def baseStart_499123 : Nat := 118140960795 + 499123 * 2 ^ 59
def prefixEnd_499123 : Nat := 4983230072969 + 3 ^ 40 * 499123 * 2
def baseEnd_499123 : Nat := 256290004714155912667081

theorem tailTrace_499123 : CollatzResearch.WordTrace tailWord_499123 prefixEnd_499123 256290004714155912667081 := by
  unfold tailWord_499123
  simp only [CollatzResearch.WordTrace]
  refine ⟨18204511370770089266934023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12136340913846726177956015 18204511370770089266934023)
  ·
    refine ⟨27306767056155133900401035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18204511370770089266934023 27306767056155133900401035)
    ·
      refine ⟨40960150584232700850601553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27306767056155133900401035 40960150584232700850601553)
      ·
        refine ⟨30720112938174525637951165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40960150584232700850601553 30720112938174525637951165)
        ·
          refine ⟨11520042351815447114231687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30720112938174525637951165 11520042351815447114231687)
          ·
            refine ⟨17280063527723170671347531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11520042351815447114231687 17280063527723170671347531)
            ·
              refine ⟨25920095291584756007021297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17280063527723170671347531 25920095291584756007021297)
              ·
                refine ⟨19440071468688567005265973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25920095291584756007021297 19440071468688567005265973)
                ·
                  refine ⟨1822506700189553156743685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19440071468688567005265973 1822506700189553156743685)
                  ·
                    refine ⟨341720006285541216889441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1822506700189553156743685 341720006285541216889441)
                    ·
                      refine ⟨256290004714155912667081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 341720006285541216889441 256290004714155912667081)
                      ·
                        rfl

theorem cell23_499123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 5, 4, 2].length) (baseStart_499123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_499123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_499123 prefixEnd_499123 := by exact prefixLift 499123
  have htrace : WordTrace (prefixWord ++ tailWord_499123) baseStart_499123 baseEnd_499123 := by
    simpa [prefixWord, tailWord_499123, baseEnd_499123] using wordTrace_append hprefix tailTrace_499123
  have hstable : (prefixWord ++ tailWord_499123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499123).length < 2 ^ (prefixWord ++ tailWord_499123).sum := by decide
  have hdescent : baseEnd_499123 < baseStart_499123 := by decide
  rcases family_descends (prefixWord ++ tailWord_499123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499138 : List Nat := [3, 5, 2, 1, 2, 1, 1, 1, 1, 1, 5]
def baseStart_499138 : Nat := 118140960795 + 499138 * 2 ^ 59
def prefixEnd_499138 : Nat := 4983230072969 + 3 ^ 40 * 499138 * 2
def baseEnd_499138 : Nat := 256297706923973353979513

theorem tailTrace_499138 : CollatzResearch.WordTrace tailWord_499138 prefixEnd_499138 256297706923973353979513 := by
  unfold tailWord_499138
  simp only [CollatzResearch.WordTrace]
  refine ⟨4551264616428936707182517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12136705643810497885820045 4551264616428936707182517)
  ·
    refine ⟨426681057790212816298361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4551264616428936707182517 426681057790212816298361)
    ·
      refine ⟨320010793342659612223771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 426681057790212816298361 320010793342659612223771)
      ·
        refine ⟨480016190013989418335657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320010793342659612223771 480016190013989418335657)
        ·
          refine ⟨360012142510492063751743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 480016190013989418335657 360012142510492063751743)
          ·
            refine ⟨540018213765738095627615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 360012142510492063751743 540018213765738095627615)
            ·
              refine ⟨810027320648607143441423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 540018213765738095627615 810027320648607143441423)
              ·
                refine ⟨1215040980972910715162135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 810027320648607143441423 1215040980972910715162135)
                ·
                  refine ⟨1822561471459366072743203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1215040980972910715162135 1822561471459366072743203)
                  ·
                    refine ⟨2733842207189049109114805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1822561471459366072743203 2733842207189049109114805)
                    ·
                      refine ⟨256297706923973353979513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2733842207189049109114805 256297706923973353979513)
                      ·
                        rfl

theorem cell23_499138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_499138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_499138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_499138 prefixEnd_499138 := by exact prefixLift 499138
  have htrace : WordTrace (prefixWord ++ tailWord_499138) baseStart_499138 baseEnd_499138 := by
    simpa [prefixWord, tailWord_499138, baseEnd_499138] using wordTrace_append hprefix tailTrace_499138
  have hstable : (prefixWord ++ tailWord_499138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499138).length < 2 ^ (prefixWord ++ tailWord_499138).sum := by decide
  have hdescent : baseEnd_499138 < baseStart_499138 := by decide
  rcases family_descends (prefixWord ++ tailWord_499138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499216 : List Nat := [2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 11]
def baseStart_499216 : Nat := 118140960795 + 499216 * 2 ^ 59
def prefixEnd_499216 : Nat := 4983230072969 + 3 ^ 40 * 499216 * 2
def baseEnd_499216 : Nat := 256337758415024048804153

theorem tailTrace_499216 : CollatzResearch.WordTrace tailWord_499216 prefixEnd_499216 256337758415024048804153 := by
  unfold tailWord_499216
  simp only [CollatzResearch.WordTrace]
  refine ⟨9103951679716583075034751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12138602239622110766713001 9103951679716583075034751)
  ·
    refine ⟨13655927519574874612552127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9103951679716583075034751 13655927519574874612552127)
    ·
      refine ⟨20483891279362311918828191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13655927519574874612552127 20483891279362311918828191)
      ·
        refine ⟨30725836919043467878242287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20483891279362311918828191 30725836919043467878242287)
        ·
          refine ⟨46088755378565201817363431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30725836919043467878242287 46088755378565201817363431)
          ·
            refine ⟨69133133067847802726045147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46088755378565201817363431 69133133067847802726045147)
            ·
              refine ⟨103699699601771704089067721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69133133067847802726045147 103699699601771704089067721)
              ·
                refine ⟨77774774701328778066800791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 103699699601771704089067721 77774774701328778066800791)
                ·
                  refine ⟨116662162051993167100201187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 77774774701328778066800791 116662162051993167100201187)
                  ·
                    refine ⟨174993243077989750650301781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 116662162051993167100201187 174993243077989750650301781)
                    ·
                      refine ⟨256337758415024048804153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 11 174993243077989750650301781 256337758415024048804153)
                      ·
                        rfl

theorem cell23_499216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 11].length) (baseStart_499216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_499216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_499216 prefixEnd_499216 := by exact prefixLift 499216
  have htrace : WordTrace (prefixWord ++ tailWord_499216) baseStart_499216 baseEnd_499216 := by
    simpa [prefixWord, tailWord_499216, baseEnd_499216] using wordTrace_append hprefix tailTrace_499216
  have hstable : (prefixWord ++ tailWord_499216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499216).length < 2 ^ (prefixWord ++ tailWord_499216).sum := by decide
  have hdescent : baseEnd_499216 < baseStart_499216 := by decide
  rcases family_descends (prefixWord ++ tailWord_499216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499250 : List Nat := [3, 2, 1, 1, 2, 1, 1, 5, 2, 2, 3]
def baseStart_499250 : Nat := 118140960795 + 499250 * 2 ^ 59
def prefixEnd_499250 : Nat := 4983230072969 + 3 ^ 40 * 499250 * 2
def baseEnd_499250 : Nat := 256355216757276915778997

theorem tailTrace_499250 : CollatzResearch.WordTrace tailWord_499250 prefixEnd_499250 256355216757276915778997 := by
  unfold tailWord_499250
  simp only [CollatzResearch.WordTrace]
  refine ⟨4552285860327497489201801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12139428960873326637871469 4552285860327497489201801)
  ·
    refine ⟨3414214395245623116901351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4552285860327497489201801 3414214395245623116901351)
    ·
      refine ⟨5121321592868434675352027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3414214395245623116901351 5121321592868434675352027)
      ·
        refine ⟨7681982389302652013028041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5121321592868434675352027 7681982389302652013028041)
        ·
          refine ⟨5761486791976989009771031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7681982389302652013028041 5761486791976989009771031)
          ·
            refine ⟨8642230187965483514656547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5761486791976989009771031 8642230187965483514656547)
            ·
              refine ⟨12963345281948225271984821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8642230187965483514656547 12963345281948225271984821)
              ·
                refine ⟨1215313620182646119248577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12963345281948225271984821 1215313620182646119248577)
                ·
                  refine ⟨911485215136984589436433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1215313620182646119248577 911485215136984589436433)
                  ·
                    refine ⟨683613911352738442077325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 911485215136984589436433 683613911352738442077325)
                    ·
                      refine ⟨256355216757276915778997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 683613911352738442077325 256355216757276915778997)
                      ·
                        rfl

theorem cell23_499250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 5, 2, 2, 3].length) (baseStart_499250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_499250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_499250 prefixEnd_499250 := by exact prefixLift 499250
  have htrace : WordTrace (prefixWord ++ tailWord_499250) baseStart_499250 baseEnd_499250 := by
    simpa [prefixWord, tailWord_499250, baseEnd_499250] using wordTrace_append hprefix tailTrace_499250
  have hstable : (prefixWord ++ tailWord_499250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499250).length < 2 ^ (prefixWord ++ tailWord_499250).sum := by decide
  have hdescent : baseEnd_499250 < baseStart_499250 := by decide
  rcases family_descends (prefixWord ++ tailWord_499250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499253 : List Nat := [1, 3, 3, 1, 1, 3, 1, 2, 8]
def baseStart_499253 : Nat := 118140960795 + 499253 * 2 ^ 59
def prefixEnd_499253 : Nat := 4983230072969 + 3 ^ 40 * 499253 * 2
def baseEnd_499253 : Nat := 28484084133248933782387

theorem tailTrace_499253 : CollatzResearch.WordTrace tailWord_499253 prefixEnd_499253 28484084133248933782387 := by
  unfold tailWord_499253
  simp only [CollatzResearch.WordTrace]
  refine ⟨18209252860299121469166413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12139501906866080979444275 18209252860299121469166413)
  ·
    refine ⟨6828469822612170550937405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18209252860299121469166413 6828469822612170550937405)
    ·
      refine ⟨2560676183479563956601527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6828469822612170550937405 2560676183479563956601527)
      ·
        refine ⟨3841014275219345934902291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2560676183479563956601527 3841014275219345934902291)
        ·
          refine ⟨5761521412829018902353437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3841014275219345934902291 5761521412829018902353437)
          ·
            refine ⟨2160570529810882088382539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5761521412829018902353437 2160570529810882088382539)
            ·
              refine ⟨3240855794716323132573809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2160570529810882088382539 3240855794716323132573809)
              ·
                refine ⟨2430641846037242349430357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3240855794716323132573809 2430641846037242349430357)
                ·
                  refine ⟨28484084133248933782387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2430641846037242349430357 28484084133248933782387)
                  ·
                    rfl

theorem cell23_499253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 2, 8].length) (baseStart_499253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_499253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_499253 prefixEnd_499253 := by exact prefixLift 499253
  have htrace : WordTrace (prefixWord ++ tailWord_499253) baseStart_499253 baseEnd_499253 := by
    simpa [prefixWord, tailWord_499253, baseEnd_499253] using wordTrace_append hprefix tailTrace_499253
  have hstable : (prefixWord ++ tailWord_499253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499253).length < 2 ^ (prefixWord ++ tailWord_499253).sum := by decide
  have hdescent : baseEnd_499253 < baseStart_499253 := by decide
  rcases family_descends (prefixWord ++ tailWord_499253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499274 : List Nat := [3, 1, 2, 1, 1, 3, 5, 2, 1, 4]
def baseStart_499274 : Nat := 118140960795 + 499274 * 2 ^ 59
def prefixEnd_499274 : Nat := 4983230072969 + 3 ^ 40 * 499274 * 2
def baseEnd_499274 : Nat := 85455846764328273959629

theorem tailTrace_499274 : CollatzResearch.WordTrace tailWord_499274 prefixEnd_499274 85455846764328273959629 := by
  unfold tailWord_499274
  simp only [CollatzResearch.WordTrace]
  refine ⟨4552504698305760513920219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12140012528815361370453917 4552504698305760513920219)
  ·
    refine ⟨6828757047458640770880329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4552504698305760513920219 6828757047458640770880329)
    ·
      refine ⟨5121567785593980578160247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6828757047458640770880329 5121567785593980578160247)
      ·
        refine ⟨7682351678390970867240371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5121567785593980578160247 7682351678390970867240371)
        ·
          refine ⟨11523527517586456300860557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7682351678390970867240371 11523527517586456300860557)
          ·
            refine ⟨4321322819094921112822709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11523527517586456300860557 4321322819094921112822709)
            ·
              refine ⟨405124014290148854327129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4321322819094921112822709 405124014290148854327129)
              ·
                refine ⟨303843010717611640745347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 405124014290148854327129 303843010717611640745347)
                ·
                  refine ⟨455764516076417461118021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 303843010717611640745347 455764516076417461118021)
                  ·
                    refine ⟨85455846764328273959629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 455764516076417461118021 85455846764328273959629)
                    ·
                      rfl

theorem cell23_499274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 5, 2, 1, 4].length) (baseStart_499274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_499274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_499274 prefixEnd_499274 := by exact prefixLift 499274
  have htrace : WordTrace (prefixWord ++ tailWord_499274) baseStart_499274 baseEnd_499274 := by
    simpa [prefixWord, tailWord_499274, baseEnd_499274] using wordTrace_append hprefix tailTrace_499274
  have hstable : (prefixWord ++ tailWord_499274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499274).length < 2 ^ (prefixWord ++ tailWord_499274).sum := by decide
  have hdescent : baseEnd_499274 < baseStart_499274 := by decide
  rcases family_descends (prefixWord ++ tailWord_499274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499287 : List Nat := [1, 1, 3, 2, 2, 5, 2, 1, 6]
def baseStart_499287 : Nat := 118140960795 + 499287 * 2 ^ 59
def prefixEnd_499287 : Nat := 4983230072969 + 3 ^ 40 * 499287 * 2
def baseEnd_499287 : Nat := 28486023949054807890703

theorem tailTrace_499287 : CollatzResearch.WordTrace tailWord_499287 prefixEnd_499287 28486023949054807890703 := by
  unfold tailWord_499287
  simp only [CollatzResearch.WordTrace]
  refine ⟨18210492942175945275904115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12140328628117296850602743 18210492942175945275904115)
  ·
    refine ⟨27315739413263917913856173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18210492942175945275904115 27315739413263917913856173)
    ·
      refine ⟨10243402279973969217696065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27315739413263917913856173 10243402279973969217696065)
      ·
        refine ⟨7682551709980476913272049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10243402279973969217696065 7682551709980476913272049)
        ·
          refine ⟨5761913782485357684954037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7682551709980476913272049 5761913782485357684954037)
          ·
            refine ⟨540179417108002282964441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5761913782485357684954037 540179417108002282964441)
            ·
              refine ⟨405134562831001712223331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 540179417108002282964441 405134562831001712223331)
              ·
                refine ⟨607701844246502568334997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 405134562831001712223331 607701844246502568334997)
                ·
                  refine ⟨28486023949054807890703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 607701844246502568334997 28486023949054807890703)
                  ·
                    rfl

theorem cell23_499287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 2, 1, 6].length) (baseStart_499287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_499287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_499287 prefixEnd_499287 := by exact prefixLift 499287
  have htrace : WordTrace (prefixWord ++ tailWord_499287) baseStart_499287 baseEnd_499287 := by
    simpa [prefixWord, tailWord_499287, baseEnd_499287] using wordTrace_append hprefix tailTrace_499287
  have hstable : (prefixWord ++ tailWord_499287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499287).length < 2 ^ (prefixWord ++ tailWord_499287).sum := by decide
  have hdescent : baseEnd_499287 < baseStart_499287 := by decide
  rcases family_descends (prefixWord ++ tailWord_499287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499290 : List Nat := [3, 1, 1, 2, 1, 1, 1, 3, 3, 5, 2]
def baseStart_499290 : Nat := 118140960795 + 499290 * 2 ^ 59
def prefixEnd_499290 : Nat := 4983230072969 + 3 ^ 40 * 499290 * 2
def baseEnd_499290 : Nat := 256375755983456759278813

theorem tailTrace_499290 : CollatzResearch.WordTrace tailWord_499290 prefixEnd_499290 256375755983456759278813 := by
  unfold tailWord_499290
  simp only [CollatzResearch.WordTrace]
  refine ⟨4552650590291269197065831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12140401574110051192175549 4552650590291269197065831)
  ·
    refine ⟨6828975885436903795598747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4552650590291269197065831 6828975885436903795598747)
    ·
      refine ⟨10243463828155355693398121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6828975885436903795598747 10243463828155355693398121)
      ·
        refine ⟨7682597871116516770048591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10243463828155355693398121 7682597871116516770048591)
        ·
          refine ⟨11523896806674775155072887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7682597871116516770048591 11523896806674775155072887)
          ·
            refine ⟨17285845210012162732609331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11523896806674775155072887 17285845210012162732609331)
            ·
              refine ⟨25928767815018244098913997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17285845210012162732609331 25928767815018244098913997)
              ·
                refine ⟨9723287930631841537092749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25928767815018244098913997 9723287930631841537092749)
                ·
                  refine ⟨3646232973986940576409781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9723287930631841537092749 3646232973986940576409781)
                  ·
                    refine ⟨341834341311275679038417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3646232973986940576409781 341834341311275679038417)
                    ·
                      refine ⟨256375755983456759278813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 341834341311275679038417 256375755983456759278813)
                      ·
                        rfl

theorem cell23_499290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 3, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 3, 3, 5, 2].length) (baseStart_499290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_499290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_499290 prefixEnd_499290 := by exact prefixLift 499290
  have htrace : WordTrace (prefixWord ++ tailWord_499290) baseStart_499290 baseEnd_499290 := by
    simpa [prefixWord, tailWord_499290, baseEnd_499290] using wordTrace_append hprefix tailTrace_499290
  have hstable : (prefixWord ++ tailWord_499290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499290).length < 2 ^ (prefixWord ++ tailWord_499290).sum := by decide
  have hdescent : baseEnd_499290 < baseStart_499290 := by decide
  rcases family_descends (prefixWord ++ tailWord_499290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499300 : List Nat := [2, 3, 1, 1, 2, 4, 1, 1, 3, 5]
def baseStart_499300 : Nat := 118140960795 + 499300 * 2 ^ 59
def prefixEnd_499300 : Nat := 4983230072969 + 3 ^ 40 * 499300 * 2
def baseEnd_499300 : Nat := 85460296930000573384589

theorem tailTrace_499300 : CollatzResearch.WordTrace tailWord_499300 prefixEnd_499300 85460296930000573384589 := by
  unfold tailWord_499300
  simp only [CollatzResearch.WordTrace]
  refine ⟨9105483545564424248063677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12140644727419232330751569 9105483545564424248063677)
  ·
    refine ⟨3414556329586659093023879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9105483545564424248063677 3414556329586659093023879)
    ·
      refine ⟨5121834494379988639535819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3414556329586659093023879 5121834494379988639535819)
      ·
        refine ⟨7682751741569982959303729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5121834494379988639535819 7682751741569982959303729)
        ·
          refine ⟨5762063806177487219477797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7682751741569982959303729 5762063806177487219477797)
          ·
            refine ⟨1080386963658278853652087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5762063806177487219477797 1080386963658278853652087)
            ·
              refine ⟨1620580445487418280478131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1080386963658278853652087 1620580445487418280478131)
              ·
                refine ⟨2430870668231127420717197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1620580445487418280478131 2430870668231127420717197)
                ·
                  refine ⟨911576500586672782768949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2430870668231127420717197 911576500586672782768949)
                  ·
                    refine ⟨85460296930000573384589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 911576500586672782768949 85460296930000573384589)
                    ·
                      rfl

theorem cell23_499300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 1, 3, 5].length) (baseStart_499300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_499300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_499300 prefixEnd_499300 := by exact prefixLift 499300
  have htrace : WordTrace (prefixWord ++ tailWord_499300) baseStart_499300 baseEnd_499300 := by
    simpa [prefixWord, tailWord_499300, baseEnd_499300] using wordTrace_append hprefix tailTrace_499300
  have hstable : (prefixWord ++ tailWord_499300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499300).length < 2 ^ (prefixWord ++ tailWord_499300).sum := by decide
  have hdescent : baseEnd_499300 < baseStart_499300 := by decide
  rcases family_descends (prefixWord ++ tailWord_499300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499340 : List Nat := [2, 2, 1, 2, 1, 1, 3, 1, 5, 2, 3]
def baseStart_499340 : Nat := 118140960795 + 499340 * 2 ^ 59
def prefixEnd_499340 : Nat := 4983230072969 + 3 ^ 40 * 499340 * 2
def baseEnd_499340 : Nat := 256401430016181563653583

theorem tailTrace_499340 : CollatzResearch.WordTrace tailWord_499340 prefixEnd_499340 256401430016181563653583 := by
  unfold tailWord_499340
  simp only [CollatzResearch.WordTrace]
  refine ⟨9106213005491967663791737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12141617340655956885055649 9106213005491967663791737)
  ·
    refine ⟨6829659754118975747843803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9106213005491967663791737 6829659754118975747843803)
    ·
      refine ⟨10244489631178463621765705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6829659754118975747843803 10244489631178463621765705)
      ·
        refine ⟨7683367223383847716324279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10244489631178463621765705 7683367223383847716324279)
        ·
          refine ⟨11525050835075771574486419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7683367223383847716324279 11525050835075771574486419)
          ·
            refine ⟨17287576252613657361729629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11525050835075771574486419 17287576252613657361729629)
            ·
              refine ⟨6482841094730121510648611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17287576252613657361729629 6482841094730121510648611)
              ·
                refine ⟨9724261642095182265972917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6482841094730121510648611 9724261642095182265972917)
                ·
                  refine ⟨911649528946423337434961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9724261642095182265972917 911649528946423337434961)
                  ·
                    refine ⟨683737146709817503076221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 911649528946423337434961 683737146709817503076221)
                    ·
                      refine ⟨256401430016181563653583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 683737146709817503076221 256401430016181563653583)
                      ·
                        rfl

theorem cell23_499340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 5, 2, 3].length) (baseStart_499340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_499340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_499340 prefixEnd_499340 := by exact prefixLift 499340
  have htrace : WordTrace (prefixWord ++ tailWord_499340) baseStart_499340 baseEnd_499340 := by
    simpa [prefixWord, tailWord_499340, baseEnd_499340] using wordTrace_append hprefix tailTrace_499340
  have hstable : (prefixWord ++ tailWord_499340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499340).length < 2 ^ (prefixWord ++ tailWord_499340).sum := by decide
  have hdescent : baseEnd_499340 < baseStart_499340 := by decide
  rcases family_descends (prefixWord ++ tailWord_499340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499357 : List Nat := [1, 4, 2, 1, 1, 1, 1, 6, 1, 2, 3]
def baseStart_499357 : Nat := 118140960795 + 499357 * 2 ^ 59
def prefixEnd_499357 : Nat := 4983230072969 + 3 ^ 40 * 499357 * 2
def baseEnd_499357 : Nat := 256410159187307997141005

theorem tailTrace_499357 : CollatzResearch.WordTrace tailWord_499357 prefixEnd_499357 256410159187307997141005 := by
  unfold tailWord_499357
  simp only [CollatzResearch.WordTrace]
  refine ⟨18213046051922347230952325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12142030701281564820634883 18213046051922347230952325)
  ·
    refine ⟨3414946134735440105803561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18213046051922347230952325 3414946134735440105803561)
    ·
      refine ⟨2561209601051580079352671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3414946134735440105803561 2561209601051580079352671)
      ·
        refine ⟨3841814401577370119029007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2561209601051580079352671 3841814401577370119029007)
        ·
          refine ⟨5762721602366055178543511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3841814401577370119029007 5762721602366055178543511)
          ·
            refine ⟨8644082403549082767815267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5762721602366055178543511 8644082403549082767815267)
            ·
              refine ⟨12966123605323624151722901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8644082403549082767815267 12966123605323624151722901)
              ·
                refine ⟨607787043999544882112011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12966123605323624151722901 607787043999544882112011)
                ·
                  refine ⟨911680565999317323168017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 607787043999544882112011 911680565999317323168017)
                  ·
                    refine ⟨683760424499487992376013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 911680565999317323168017 683760424499487992376013)
                    ·
                      refine ⟨256410159187307997141005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 683760424499487992376013 256410159187307997141005)
                      ·
                        rfl

theorem cell23_499357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 6, 1, 2, 3].length) (baseStart_499357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_499357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_499357 prefixEnd_499357 := by exact prefixLift 499357
  have htrace : WordTrace (prefixWord ++ tailWord_499357) baseStart_499357 baseEnd_499357 := by
    simpa [prefixWord, tailWord_499357, baseEnd_499357] using wordTrace_append hprefix tailTrace_499357
  have hstable : (prefixWord ++ tailWord_499357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499357).length < 2 ^ (prefixWord ++ tailWord_499357).sum := by decide
  have hdescent : baseEnd_499357 < baseStart_499357 := by decide
  rcases family_descends (prefixWord ++ tailWord_499357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499381 : List Nat := [1, 3, 3, 3, 2, 2, 1, 2, 2, 4]
def baseStart_499381 : Nat := 118140960795 + 499381 * 2 ^ 59
def prefixEnd_499381 : Nat := 4983230072969 + 3 ^ 40 * 499381 * 2
def baseEnd_499381 : Nat := 85474160907671967746965

theorem tailTrace_499381 : CollatzResearch.WordTrace tailWord_499381 prefixEnd_499381 85474160907671967746965 := by
  unfold tailWord_499381
  simp only [CollatzResearch.WordTrace]
  refine ⟨18213921403835399329825997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12142614269223599553217331 18213921403835399329825997)
  ·
    refine ⟨6830220526438274748684749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18213921403835399329825997 6830220526438274748684749)
    ·
      refine ⟨2561332697414353030756781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6830220526438274748684749 2561332697414353030756781)
      ·
        refine ⟨960499761530382386533793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2561332697414353030756781 960499761530382386533793)
        ·
          refine ⟨720374821147786789900345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 960499761530382386533793 720374821147786789900345)
          ·
            refine ⟨540281115860840092425259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 720374821147786789900345 540281115860840092425259)
            ·
              refine ⟨810421673791260138637889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 540281115860840092425259 810421673791260138637889)
              ·
                refine ⟨607816255343445103978417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 810421673791260138637889 607816255343445103978417)
                ·
                  refine ⟨455862191507583827983813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 607816255343445103978417 455862191507583827983813)
                  ·
                    refine ⟨85474160907671967746965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 455862191507583827983813 85474160907671967746965)
                    ·
                      rfl

theorem cell23_499381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 1, 2, 2, 4].length) (baseStart_499381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_499381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_499381 prefixEnd_499381 := by exact prefixLift 499381
  have htrace : WordTrace (prefixWord ++ tailWord_499381) baseStart_499381 baseEnd_499381 := by
    simpa [prefixWord, tailWord_499381, baseEnd_499381] using wordTrace_append hprefix tailTrace_499381
  have hstable : (prefixWord ++ tailWord_499381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499381).length < 2 ^ (prefixWord ++ tailWord_499381).sum := by decide
  have hdescent : baseEnd_499381 < baseStart_499381 := by decide
  rcases family_descends (prefixWord ++ tailWord_499381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499440 : List Nat := [2, 1, 1, 1, 3, 1, 2, 4, 2, 2, 4]
def baseStart_499440 : Nat := 118140960795 + 499440 * 2 ^ 59
def prefixEnd_499440 : Nat := 4983230072969 + 3 ^ 40 * 499440 * 2
def baseEnd_499440 : Nat := 256452778081631172403123

theorem tailTrace_499440 : CollatzResearch.WordTrace tailWord_499440 prefixEnd_499440 256452778081631172403123 := by
  unfold tailWord_499440
  simp only [CollatzResearch.WordTrace]
  refine ⟨9108036655310826203111887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12144048873747768270815849 9108036655310826203111887)
  ·
    refine ⟨13662054982966239304667831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9108036655310826203111887 13662054982966239304667831)
    ·
      refine ⟨20493082474449358957001747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13662054982966239304667831 20493082474449358957001747)
      ·
        refine ⟨30739623711674038435502621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20493082474449358957001747 30739623711674038435502621)
        ·
          refine ⟨11527358891877764413313483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30739623711674038435502621 11527358891877764413313483)
          ·
            refine ⟨17291038337816646619970225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11527358891877764413313483 17291038337816646619970225)
            ·
              refine ⟨12968278753362484964977669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17291038337816646619970225 12968278753362484964977669)
              ·
                refine ⟨2431552266255465930933313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12968278753362484964977669 2431552266255465930933313)
                ·
                  refine ⟨1823664199691599448199985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2431552266255465930933313 1823664199691599448199985)
                  ·
                    refine ⟨1367748149768699586149989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1823664199691599448199985 1367748149768699586149989)
                    ·
                      refine ⟨256452778081631172403123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1367748149768699586149989 256452778081631172403123)
                      ·
                        rfl

theorem cell23_499440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 4, 2, 2, 4].length) (baseStart_499440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_499440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_499440 prefixEnd_499440 := by exact prefixLift 499440
  have htrace : WordTrace (prefixWord ++ tailWord_499440) baseStart_499440 baseEnd_499440 := by
    simpa [prefixWord, tailWord_499440, baseEnd_499440] using wordTrace_append hprefix tailTrace_499440
  have hstable : (prefixWord ++ tailWord_499440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499440).length < 2 ^ (prefixWord ++ tailWord_499440).sum := by decide
  have hdescent : baseEnd_499440 < baseStart_499440 := by decide
  rcases family_descends (prefixWord ++ tailWord_499440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499480 : List Nat := [2, 1, 2, 3, 1, 1, 2, 3, 1, 7]
def baseStart_499480 : Nat := 118140960795 + 499480 * 2 ^ 59
def prefixEnd_499480 : Nat := 4983230072969 + 3 ^ 40 * 499480 * 2
def baseEnd_499480 : Nat := 85491105769270338634313

theorem tailTrace_499480 : CollatzResearch.WordTrace tailWord_499480 prefixEnd_499480 85491105769270338634313 := by
  unfold tailWord_499480
  simp only [CollatzResearch.WordTrace]
  refine ⟨9108766115238369618839947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12145021486984492825119929 9108766115238369618839947)
  ·
    refine ⟨13663149172857554428259921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9108766115238369618839947 13663149172857554428259921)
    ·
      refine ⟨10247361879643165821194941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13663149172857554428259921 10247361879643165821194941)
      ·
        refine ⟨3842760704866187182948103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10247361879643165821194941 3842760704866187182948103)
        ·
          refine ⟨5764141057299280774422155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3842760704866187182948103 5764141057299280774422155)
          ·
            refine ⟨8646211585948921161633233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5764141057299280774422155 8646211585948921161633233)
            ·
              refine ⟨6484658689461690871224925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8646211585948921161633233 6484658689461690871224925)
              ·
                refine ⟨2431747008548134076709347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6484658689461690871224925 2431747008548134076709347)
                ·
                  refine ⟨3647620512822201115064021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2431747008548134076709347 3647620512822201115064021)
                  ·
                    refine ⟨85491105769270338634313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3647620512822201115064021 85491105769270338634313)
                    ·
                      rfl

theorem cell23_499480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 3, 1, 7].length) (baseStart_499480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_499480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_499480 prefixEnd_499480 := by exact prefixLift 499480
  have htrace : WordTrace (prefixWord ++ tailWord_499480) baseStart_499480 baseEnd_499480 := by
    simpa [prefixWord, tailWord_499480, baseEnd_499480] using wordTrace_append hprefix tailTrace_499480
  have hstable : (prefixWord ++ tailWord_499480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499480).length < 2 ^ (prefixWord ++ tailWord_499480).sum := by decide
  have hdescent : baseEnd_499480 < baseStart_499480 := by decide
  rcases family_descends (prefixWord ++ tailWord_499480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499527 : List Nat := [1, 1, 4, 1, 2, 1, 3, 1, 5, 4]
def baseStart_499527 : Nat := 118140960795 + 499527 * 2 ^ 59
def prefixEnd_499527 : Nat := 4983230072969 + 3 ^ 40 * 499527 * 2
def baseEnd_499527 : Nat := 85499150299524110671741

theorem tailTrace_499527 : CollatzResearch.WordTrace tailWord_499527 prefixEnd_499527 85499150299524110671741 := by
  unfold tailWord_499527
  simp only [CollatzResearch.WordTrace]
  refine ⟨18219246461306466264640835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12146164307537644176427223 18219246461306466264640835)
  ·
    refine ⟨27328869691959699396961253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18219246461306466264640835 27328869691959699396961253)
    ·
      refine ⟨5124163067242443636930235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27328869691959699396961253 5124163067242443636930235)
      ·
        refine ⟨7686244600863665455395353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5124163067242443636930235 7686244600863665455395353)
        ·
          refine ⟨5764683450647749091546515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7686244600863665455395353 5764683450647749091546515)
          ·
            refine ⟨8647025175971623637319773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5764683450647749091546515 8647025175971623637319773)
            ·
              refine ⟨3242634440989358863994915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8647025175971623637319773 3242634440989358863994915)
              ·
                refine ⟨4863951661484038295992373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3242634440989358863994915 4863951661484038295992373)
                ·
                  refine ⟨455995468264128590249285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4863951661484038295992373 455995468264128590249285)
                  ·
                    refine ⟨85499150299524110671741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 455995468264128590249285 85499150299524110671741)
                    ·
                      rfl

theorem cell23_499527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 1, 5, 4].length) (baseStart_499527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_499527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_499527 prefixEnd_499527 := by exact prefixLift 499527
  have htrace : WordTrace (prefixWord ++ tailWord_499527) baseStart_499527 baseEnd_499527 := by
    simpa [prefixWord, tailWord_499527, baseEnd_499527] using wordTrace_append hprefix tailTrace_499527
  have hstable : (prefixWord ++ tailWord_499527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499527).length < 2 ^ (prefixWord ++ tailWord_499527).sum := by decide
  have hdescent : baseEnd_499527 < baseStart_499527 := by decide
  rcases family_descends (prefixWord ++ tailWord_499527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499584 : List Nat := [2, 1, 1, 2, 1, 2, 3, 4, 3, 1, 3]
def baseStart_499584 : Nat := 118140960795 + 499584 * 2 ^ 59
def prefixEnd_499584 : Nat := 4983230072969 + 3 ^ 40 * 499584 * 2
def baseEnd_499584 : Nat := 256526719295878609002461

theorem tailTrace_499584 : CollatzResearch.WordTrace tailWord_499584 prefixEnd_499584 256526719295878609002461 := by
  unfold tailWord_499584
  simp only [CollatzResearch.WordTrace]
  refine ⟨9110662711049982499732903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12147550281399976666310537 9110662711049982499732903)
  ·
    refine ⟨13665994066574973749599355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9110662711049982499732903 13665994066574973749599355)
    ·
      refine ⟨20498991099862460624399033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13665994066574973749599355 20498991099862460624399033)
      ·
        refine ⟨15374243324896845468299275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20498991099862460624399033 15374243324896845468299275)
        ·
          refine ⟨23061364987345268202448913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15374243324896845468299275 23061364987345268202448913)
          ·
            refine ⟨17296023740508951151836685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23061364987345268202448913 17296023740508951151836685)
            ·
              refine ⟨6486008902690856681938757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17296023740508951151836685 6486008902690856681938757)
              ·
                refine ⟨1216126669254535627863517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6486008902690856681938757 1216126669254535627863517)
                ·
                  refine ⟨456047500970450860448819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1216126669254535627863517 456047500970450860448819)
                  ·
                    refine ⟨684071251455676290673229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 456047500970450860448819 684071251455676290673229)
                    ·
                      refine ⟨256526719295878609002461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 684071251455676290673229 256526719295878609002461)
                      ·
                        rfl

theorem cell23_499584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 4, 3, 1, 3].length) (baseStart_499584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_499584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_499584 prefixEnd_499584 := by exact prefixLift 499584
  have htrace : WordTrace (prefixWord ++ tailWord_499584) baseStart_499584 baseEnd_499584 := by
    simpa [prefixWord, tailWord_499584, baseEnd_499584] using wordTrace_append hprefix tailTrace_499584
  have hstable : (prefixWord ++ tailWord_499584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499584).length < 2 ^ (prefixWord ++ tailWord_499584).sum := by decide
  have hdescent : baseEnd_499584 < baseStart_499584 := by decide
  rcases family_descends (prefixWord ++ tailWord_499584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499641 : List Nat := [1, 2, 1, 4, 2, 1, 2, 1, 5, 2, 2]
def baseStart_499641 : Nat := 118140960795 + 499641 * 2 ^ 59
def prefixEnd_499641 : Nat := 4983230072969 + 3 ^ 40 * 499641 * 2
def baseEnd_499641 : Nat := 256555987693184885989699

theorem tailTrace_499641 : CollatzResearch.WordTrace tailWord_499641 prefixEnd_499641 256555987693184885989699 := by
  unfold tailWord_499641
  simp only [CollatzResearch.WordTrace]
  refine ⟨18223404382893463734290777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12148936255262309156193851 18223404382893463734290777)
  ·
    refine ⟨13667553287170097800718083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18223404382893463734290777 13667553287170097800718083)
    ·
      refine ⟨20501329930755146701077125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13667553287170097800718083 20501329930755146701077125)
      ·
        refine ⟨3843999362016590006451961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20501329930755146701077125 3843999362016590006451961)
        ·
          refine ⟨2882999521512442504838971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3843999362016590006451961 2882999521512442504838971)
          ·
            refine ⟨4324499282268663757258457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2882999521512442504838971 4324499282268663757258457)
            ·
              refine ⟨3243374461701497817943843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4324499282268663757258457 3243374461701497817943843)
              ·
                refine ⟨4865061692552246726915765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3243374461701497817943843 4865061692552246726915765)
                ·
                  refine ⟨456099533676773130648353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4865061692552246726915765 456099533676773130648353)
                  ·
                    refine ⟨342074650257579847986265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 456099533676773130648353 342074650257579847986265)
                    ·
                      refine ⟨256555987693184885989699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 342074650257579847986265 256555987693184885989699)
                      ·
                        rfl

theorem cell23_499641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 1, 5, 2, 2].length) (baseStart_499641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_499641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_499641 prefixEnd_499641 := by exact prefixLift 499641
  have htrace : WordTrace (prefixWord ++ tailWord_499641) baseStart_499641 baseEnd_499641 := by
    simpa [prefixWord, tailWord_499641, baseEnd_499641] using wordTrace_append hprefix tailTrace_499641
  have hstable : (prefixWord ++ tailWord_499641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499641).length < 2 ^ (prefixWord ++ tailWord_499641).sum := by decide
  have hdescent : baseEnd_499641 < baseStart_499641 := by decide
  rcases family_descends (prefixWord ++ tailWord_499641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499752 : List Nat := [2, 1, 5, 3, 1, 1, 2, 2, 1, 3, 2]
def baseStart_499752 : Nat := 118140960795 + 499752 * 2 ^ 59
def prefixEnd_499752 : Nat := 4983230072969 + 3 ^ 40 * 499752 * 2
def baseEnd_499752 : Nat := 256612984045833951701689

theorem tailTrace_499752 : CollatzResearch.WordTrace tailWord_499752 prefixEnd_499752 256612984045833951701689 := by
  unfold tailWord_499752
  simp only [CollatzResearch.WordTrace]
  refine ⟨9113726442745664845790755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12151635256994219794387673 9113726442745664845790755)
  ·
    refine ⟨13670589664118497268686133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9113726442745664845790755 13670589664118497268686133)
    ·
      refine ⟨1281617781011109118939325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13670589664118497268686133 1281617781011109118939325)
      ·
        refine ⟨480606667879165919602247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1281617781011109118939325 480606667879165919602247)
        ·
          refine ⟨720910001818748879403371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 480606667879165919602247 720910001818748879403371)
          ·
            refine ⟨1081365002728123319105057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 720910001818748879403371 1081365002728123319105057)
            ·
              refine ⟨811023752046092489328793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1081365002728123319105057 811023752046092489328793)
              ·
                refine ⟨608267814034569366996595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 811023752046092489328793 608267814034569366996595)
                ·
                  refine ⟨912401721051854050494893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 608267814034569366996595 912401721051854050494893)
                  ·
                    refine ⟨342150645394445268935585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 912401721051854050494893 342150645394445268935585)
                    ·
                      refine ⟨256612984045833951701689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 342150645394445268935585 256612984045833951701689)
                      ·
                        rfl

theorem cell23_499752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_499752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_499752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_499752 prefixEnd_499752 := by exact prefixLift 499752
  have htrace : WordTrace (prefixWord ++ tailWord_499752) baseStart_499752 baseEnd_499752 := by
    simpa [prefixWord, tailWord_499752, baseEnd_499752] using wordTrace_append hprefix tailTrace_499752
  have hstable : (prefixWord ++ tailWord_499752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499752).length < 2 ^ (prefixWord ++ tailWord_499752).sum := by decide
  have hdescent : baseEnd_499752 < baseStart_499752 := by decide
  rcases family_descends (prefixWord ++ tailWord_499752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499782 : List Nat := [6, 1, 1, 1, 1, 1, 2, 4, 2, 2, 2]
def baseStart_499782 : Nat := 118140960795 + 499782 * 2 ^ 59
def prefixEnd_499782 : Nat := 4983230072969 + 3 ^ 40 * 499782 * 2
def baseEnd_499782 : Nat := 256628388465468834326551

theorem tailTrace_499782 : CollatzResearch.WordTrace tailWord_499782 prefixEnd_499782 256628388465468834326551 := by
  unfold tailWord_499782
  simp only [CollatzResearch.WordTrace]
  refine ⟨569642096105707650474175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 12152364716921763210115733 569642096105707650474175)
  ·
    refine ⟨854463144158561475711263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 569642096105707650474175 854463144158561475711263)
    ·
      refine ⟨1281694716237842213566895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 854463144158561475711263 1281694716237842213566895)
      ·
        refine ⟨1922542074356763320350343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1281694716237842213566895 1922542074356763320350343)
        ·
          refine ⟨2883813111535144980525515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1922542074356763320350343 2883813111535144980525515)
          ·
            refine ⟨4325719667302717470788273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2883813111535144980525515 4325719667302717470788273)
            ·
              refine ⟨3244289750477038103091205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4325719667302717470788273 3244289750477038103091205)
              ·
                refine ⟨608304328214444644329601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3244289750477038103091205 608304328214444644329601)
                ·
                  refine ⟨456228246160833483247201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 608304328214444644329601 456228246160833483247201)
                  ·
                    refine ⟨342171184620625112435401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 456228246160833483247201 342171184620625112435401)
                    ·
                      refine ⟨256628388465468834326551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 342171184620625112435401 256628388465468834326551)
                      ·
                        rfl

theorem cell23_499782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 4, 2, 2, 2].length) (baseStart_499782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_499782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_499782 prefixEnd_499782 := by exact prefixLift 499782
  have htrace : WordTrace (prefixWord ++ tailWord_499782) baseStart_499782 baseEnd_499782 := by
    simpa [prefixWord, tailWord_499782, baseEnd_499782] using wordTrace_append hprefix tailTrace_499782
  have hstable : (prefixWord ++ tailWord_499782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499782).length < 2 ^ (prefixWord ++ tailWord_499782).sum := by decide
  have hdescent : baseEnd_499782 < baseStart_499782 := by decide
  rcases family_descends (prefixWord ++ tailWord_499782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499818 : List Nat := [3, 1, 3, 2, 3, 1, 2, 1, 2, 5]
def baseStart_499818 : Nat := 118140960795 + 499818 * 2 ^ 59
def prefixEnd_499818 : Nat := 4983230072969 + 3 ^ 40 * 499818 * 2
def baseEnd_499818 : Nat := 85548957923010231158795

theorem tailTrace_499818 : CollatzResearch.WordTrace tailWord_499818 prefixEnd_499818 85548957923010231158795 := by
  unfold tailWord_499818
  simp only [CollatzResearch.WordTrace]
  refine ⟨4557465025813055740871027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12153240068834815308989405 4557465025813055740871027)
  ·
    refine ⟨6836197538719583611306541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4557465025813055740871027 6836197538719583611306541)
    ·
      refine ⟨2563574077019843854239953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6836197538719583611306541 2563574077019843854239953)
      ·
        refine ⟨1922680557764882890679965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2563574077019843854239953 1922680557764882890679965)
        ·
          refine ⟨721005209161831084004987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1922680557764882890679965 721005209161831084004987)
          ·
            refine ⟨1081507813742746626007481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 721005209161831084004987 1081507813742746626007481)
            ·
              refine ⟨811130860307059969505611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1081507813742746626007481 811130860307059969505611)
              ·
                refine ⟨1216696290460589954258417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 811130860307059969505611 1216696290460589954258417)
                ·
                  refine ⟨912522217845442465693813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1216696290460589954258417 912522217845442465693813)
                  ·
                    refine ⟨85548957923010231158795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 912522217845442465693813 85548957923010231158795)
                    ·
                      rfl

theorem cell23_499818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 2, 1, 2, 5].length) (baseStart_499818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_499818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_499818 prefixEnd_499818 := by exact prefixLift 499818
  have htrace : WordTrace (prefixWord ++ tailWord_499818) baseStart_499818 baseEnd_499818 := by
    simpa [prefixWord, tailWord_499818, baseEnd_499818] using wordTrace_append hprefix tailTrace_499818
  have hstable : (prefixWord ++ tailWord_499818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499818).length < 2 ^ (prefixWord ++ tailWord_499818).sum := by decide
  have hdescent : baseEnd_499818 < baseStart_499818 := by decide
  rcases family_descends (prefixWord ++ tailWord_499818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499898 : List Nat := [3, 1, 1, 1, 2, 2, 2, 4, 2, 3, 2]
def baseStart_499898 : Nat := 118140960795 + 499898 * 2 ^ 59
def prefixEnd_499898 : Nat := 4983230072969 + 3 ^ 40 * 499898 * 2
def baseEnd_499898 : Nat := 256687952221390380476017

theorem tailTrace_499898 : CollatzResearch.WordTrace tailWord_499898 prefixEnd_499898 256687952221390380476017 := by
  unfold tailWord_499898
  simp only [CollatzResearch.WordTrace]
  refine ⟨4558194485740599156599087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12155185295308264417597565 4558194485740599156599087)
  ·
    refine ⟨6837291728610898734898631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4558194485740599156599087 6837291728610898734898631)
    ·
      refine ⟨10255937592916348102347947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6837291728610898734898631 10255937592916348102347947)
      ·
        refine ⟨15383906389374522153521921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10255937592916348102347947 15383906389374522153521921)
        ·
          refine ⟨11537929792030891615141441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15383906389374522153521921 11537929792030891615141441)
          ·
            refine ⟨8653447344023168711356081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11537929792030891615141441 8653447344023168711356081)
            ·
              refine ⟨6490085508017376533517061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8653447344023168711356081 6490085508017376533517061)
              ·
                refine ⟨1216891032753258100034449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6490085508017376533517061 1216891032753258100034449)
                ·
                  refine ⟨912668274564943575025837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1216891032753258100034449 912668274564943575025837)
                  ·
                    refine ⟨342250602961853840634689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 912668274564943575025837 342250602961853840634689)
                    ·
                      refine ⟨256687952221390380476017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 342250602961853840634689 256687952221390380476017)
                      ·
                        rfl

theorem cell23_499898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 4, 2, 3, 2].length) (baseStart_499898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_499898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_499898 prefixEnd_499898 := by exact prefixLift 499898
  have htrace : WordTrace (prefixWord ++ tailWord_499898) baseStart_499898 baseEnd_499898 := by
    simpa [prefixWord, tailWord_499898, baseEnd_499898] using wordTrace_append hprefix tailTrace_499898
  have hstable : (prefixWord ++ tailWord_499898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499898).length < 2 ^ (prefixWord ++ tailWord_499898).sum := by decide
  have hdescent : baseEnd_499898 < baseStart_499898 := by decide
  rcases family_descends (prefixWord ++ tailWord_499898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499921 : List Nat := [1, 2, 2, 1, 2, 2, 5, 1, 1, 6]
def baseStart_499921 : Nat := 118140960795 + 499921 * 2 ^ 59
def prefixEnd_499921 : Nat := 4983230072969 + 3 ^ 40 * 499921 * 2
def baseEnd_499921 : Nat := 85566587425481263496137

theorem tailTrace_499921 : CollatzResearch.WordTrace tailWord_499921 prefixEnd_499921 85566587425481263496137 := by
  unfold tailWord_499921
  simp only [CollatzResearch.WordTrace]
  refine ⟨18233616821879071554483617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12155744547919381036322411 18233616821879071554483617)
  ·
    refine ⟨13675212616409303665862713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18233616821879071554483617 13675212616409303665862713)
    ·
      refine ⟨10256409462306977749397035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13675212616409303665862713 10256409462306977749397035)
      ·
        refine ⟨15384614193460466624095553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10256409462306977749397035 15384614193460466624095553)
        ·
          refine ⟨11538460645095349968071665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15384614193460466624095553 11538460645095349968071665)
          ·
            refine ⟨8653845483821512476053749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11538460645095349968071665 8653845483821512476053749)
            ·
              refine ⟨811298014108266794630039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8653845483821512476053749 811298014108266794630039)
              ·
                refine ⟨1216947021162400191945059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 811298014108266794630039 1216947021162400191945059)
                ·
                  refine ⟨1825420531743600287917589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1216947021162400191945059 1825420531743600287917589)
                  ·
                    refine ⟨85566587425481263496137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1825420531743600287917589 85566587425481263496137)
                    ·
                      rfl

theorem cell23_499921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 5, 1, 1, 6].length) (baseStart_499921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_499921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_499921 prefixEnd_499921 := by exact prefixLift 499921
  have htrace : WordTrace (prefixWord ++ tailWord_499921) baseStart_499921 baseEnd_499921 := by
    simpa [prefixWord, tailWord_499921, baseEnd_499921] using wordTrace_append hprefix tailTrace_499921
  have hstable : (prefixWord ++ tailWord_499921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499921).length < 2 ^ (prefixWord ++ tailWord_499921).sum := by decide
  have hdescent : baseEnd_499921 < baseStart_499921 := by decide
  rcases family_descends (prefixWord ++ tailWord_499921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499925 : List Nat := [1, 3, 2, 4, 2, 1, 2, 2, 1, 5]
def baseStart_499925 : Nat := 118140960795 + 499925 * 2 ^ 59
def prefixEnd_499925 : Nat := 4983230072969 + 3 ^ 40 * 499925 * 2
def baseEnd_499925 : Nat := 85567272066353924946131

theorem tailTrace_499925 : CollatzResearch.WordTrace tailWord_499925 prefixEnd_499925 85567272066353924946131 := by
  unfold tailWord_499925
  simp only [CollatzResearch.WordTrace]
  refine ⟨18233762713864580237629229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12155841809243053491752819 18233762713864580237629229)
  ·
    refine ⟨6837661017699217589110961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18233762713864580237629229 6837661017699217589110961)
    ·
      refine ⟨5128245763274413191833221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6837661017699217589110961 5128245763274413191833221)
      ·
        refine ⟨961546080613952473468729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5128245763274413191833221 961546080613952473468729)
        ·
          refine ⟨721159560460464355101547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 961546080613952473468729 721159560460464355101547)
          ·
            refine ⟨1081739340690696532652321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 721159560460464355101547 1081739340690696532652321)
            ·
              refine ⟨811304505518022399489241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1081739340690696532652321 811304505518022399489241)
              ·
                refine ⟨608478379138516799616931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 811304505518022399489241 608478379138516799616931)
                ·
                  refine ⟨912717568707775199425397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 608478379138516799616931 912717568707775199425397)
                  ·
                    refine ⟨85567272066353924946131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 912717568707775199425397 85567272066353924946131)
                    ·
                      rfl

theorem cell23_499925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 2, 2, 1, 5].length) (baseStart_499925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_499925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_499925 prefixEnd_499925 := by exact prefixLift 499925
  have htrace : WordTrace (prefixWord ++ tailWord_499925) baseStart_499925 baseEnd_499925 := by
    simpa [prefixWord, tailWord_499925, baseEnd_499925] using wordTrace_append hprefix tailTrace_499925
  have hstable : (prefixWord ++ tailWord_499925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499925).length < 2 ^ (prefixWord ++ tailWord_499925).sum := by decide
  have hdescent : baseEnd_499925 < baseStart_499925 := by decide
  rcases family_descends (prefixWord ++ tailWord_499925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499928 : List Nat := [2, 1, 2, 2, 4, 1, 1, 4, 1, 1, 4]
def baseStart_499928 : Nat := 118140960795 + 499928 * 2 ^ 59
def prefixEnd_499928 : Nat := 4983230072969 + 3 ^ 40 * 499928 * 2
def baseEnd_499928 : Nat := 256703356641025263100879

theorem tailTrace_499928 : CollatzResearch.WordTrace tailWord_499928 prefixEnd_499928 256703356641025263100879 := by
  unfold tailWord_499928
  simp only [CollatzResearch.WordTrace]
  refine ⟨9116936066426855874994219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12155914755235807833325625 9116936066426855874994219)
  ·
    refine ⟨13675404099640283812491329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9116936066426855874994219 13675404099640283812491329)
    ·
      refine ⟨10256553074730212859368497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13675404099640283812491329 10256553074730212859368497)
      ·
        refine ⟨7692414806047659644526373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10256553074730212859368497 7692414806047659644526373)
        ·
          refine ⟨1442327776133936183348695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7692414806047659644526373 1442327776133936183348695)
          ·
            refine ⟨2163491664200904275023043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1442327776133936183348695 2163491664200904275023043)
            ·
              refine ⟨3245237496301356412534565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2163491664200904275023043 3245237496301356412534565)
              ·
                refine ⟨608482030556504327350231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3245237496301356412534565 608482030556504327350231)
                ·
                  refine ⟨912723045834756491025347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 608482030556504327350231 912723045834756491025347)
                  ·
                    refine ⟨1369084568752134736538021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 912723045834756491025347 1369084568752134736538021)
                    ·
                      refine ⟨256703356641025263100879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1369084568752134736538021 256703356641025263100879)
                      ·
                        rfl

theorem cell23_499928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 4, 1, 1, 4].length) (baseStart_499928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_499928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_499928 prefixEnd_499928 := by exact prefixLift 499928
  have htrace : WordTrace (prefixWord ++ tailWord_499928) baseStart_499928 baseEnd_499928 := by
    simpa [prefixWord, tailWord_499928, baseEnd_499928] using wordTrace_append hprefix tailTrace_499928
  have hstable : (prefixWord ++ tailWord_499928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499928).length < 2 ^ (prefixWord ++ tailWord_499928).sum := by decide
  have hdescent : baseEnd_499928 < baseStart_499928 := by decide
  rcases family_descends (prefixWord ++ tailWord_499928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499948 : List Nat := [2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 3]
def baseStart_499948 : Nat := 118140960795 + 499948 * 2 ^ 59
def prefixEnd_499948 : Nat := 4983230072969 + 3 ^ 40 * 499948 * 2
def baseEnd_499948 : Nat := 256713626254115184850787

theorem tailTrace_499948 : CollatzResearch.WordTrace tailWord_499948 prefixEnd_499948 256713626254115184850787 := by
  unfold tailWord_499948
  simp only [CollatzResearch.WordTrace]
  refine ⟨9117300796390627582858249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12156401061854170110477665 9117300796390627582858249)
  ·
    refine ⟨6837975597292970687143687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9117300796390627582858249 6837975597292970687143687)
    ·
      refine ⟨10256963395939456030715531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6837975597292970687143687 10256963395939456030715531)
      ·
        refine ⟨15385445093909184046073297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10256963395939456030715531 15385445093909184046073297)
        ·
          refine ⟨11539083820431888034554973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15385445093909184046073297 11539083820431888034554973)
          ·
            refine ⟨4327156432661958012958115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11539083820431888034554973 4327156432661958012958115)
            ·
              refine ⟨6490734648992937019437173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4327156432661958012958115 6490734648992937019437173)
              ·
                refine ⟨608506373343087845572235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6490734648992937019437173 608506373343087845572235)
                ·
                  refine ⟨912759560014631768358353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 608506373343087845572235 912759560014631768358353)
                  ·
                    refine ⟨684569670010973826268765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 912759560014631768358353 684569670010973826268765)
                    ·
                      refine ⟨256713626254115184850787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 684569670010973826268765 256713626254115184850787)
                      ·
                        rfl

theorem cell23_499948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 3].length) (baseStart_499948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_499948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_499948 prefixEnd_499948 := by exact prefixLift 499948
  have htrace : WordTrace (prefixWord ++ tailWord_499948) baseStart_499948 baseEnd_499948 := by
    simpa [prefixWord, tailWord_499948, baseEnd_499948] using wordTrace_append hprefix tailTrace_499948
  have hstable : (prefixWord ++ tailWord_499948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499948).length < 2 ^ (prefixWord ++ tailWord_499948).sum := by decide
  have hdescent : baseEnd_499948 < baseStart_499948 := by decide
  rcases family_descends (prefixWord ++ tailWord_499948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499951 : List Nat := [1, 1, 2, 1, 6, 3, 9]
def baseStart_499951 : Nat := 118140960795 + 499951 * 2 ^ 59
def prefixEnd_499951 : Nat := 4983230072969 + 3 ^ 40 * 499951 * 2
def baseEnd_499951 : Nat := 3169323045630600902633

theorem tailTrace_499951 : CollatzResearch.WordTrace tailWord_499951 prefixEnd_499951 3169323045630600902633 := by
  unfold tailWord_499951
  simp only [CollatzResearch.WordTrace]
  refine ⟨18234711011770386678075707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12156474007846924452050471 18234711011770386678075707)
  ·
    refine ⟨27352066517655580017113561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18234711011770386678075707 27352066517655580017113561)
    ·
      refine ⟨20514049888241685012835171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27352066517655580017113561 20514049888241685012835171)
      ·
        refine ⟨30771074832362527519252757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20514049888241685012835171 30771074832362527519252757)
        ·
          refine ⟨1442394132766993477464973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 30771074832362527519252757 1442394132766993477464973)
          ·
            refine ⟨540897799787622554049365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1442394132766993477464973 540897799787622554049365)
            ·
              refine ⟨3169323045630600902633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 540897799787622554049365 3169323045630600902633)
              ·
                rfl

theorem cell23_499951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3, 9].length) (baseStart_499951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_499951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_499951 prefixEnd_499951 := by exact prefixLift 499951
  have htrace : WordTrace (prefixWord ++ tailWord_499951) baseStart_499951 baseEnd_499951 := by
    simpa [prefixWord, tailWord_499951, baseEnd_499951] using wordTrace_append hprefix tailTrace_499951
  have hstable : (prefixWord ++ tailWord_499951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499951).length < 2 ^ (prefixWord ++ tailWord_499951).sum := by decide
  have hdescent : baseEnd_499951 < baseStart_499951 := by decide
  rcases family_descends (prefixWord ++ tailWord_499951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499961 : List Nat := [1, 2, 1, 3, 1, 1, 2, 1, 5, 3, 3]
def baseStart_499961 : Nat := 118140960795 + 499961 * 2 ^ 59
def prefixEnd_499961 : Nat := 4983230072969 + 3 ^ 40 * 499961 * 2
def baseEnd_499961 : Nat := 256720301502623633988227

theorem tailTrace_499961 : CollatzResearch.WordTrace tailWord_499961 prefixEnd_499961 256720301502623633988227 := by
  unfold tailWord_499961
  simp only [CollatzResearch.WordTrace]
  refine ⟨18235075741734158385939737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12156717161156105590626491 18235075741734158385939737)
  ·
    refine ⟨13676306806300618789454803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18235075741734158385939737 13676306806300618789454803)
    ·
      refine ⟨20514460209450928184182205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13676306806300618789454803 20514460209450928184182205)
      ·
        refine ⟨7692922578544098069068327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20514460209450928184182205 7692922578544098069068327)
        ·
          refine ⟨11539383867816147103602491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7692922578544098069068327 11539383867816147103602491)
          ·
            refine ⟨17309075801724220655403737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11539383867816147103602491 17309075801724220655403737)
            ·
              refine ⟨12981806851293165491552803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17309075801724220655403737 12981806851293165491552803)
              ·
                refine ⟨19472710276939748237329205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12981806851293165491552803 19472710276939748237329205)
                ·
                  refine ⟨1825566588463101397249613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19472710276939748237329205 1825566588463101397249613)
                  ·
                    refine ⟨684587470673663023968605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1825566588463101397249613 684587470673663023968605)
                    ·
                      refine ⟨256720301502623633988227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 684587470673663023968605 256720301502623633988227)
                      ·
                        rfl

theorem cell23_499961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 5, 3, 3].length) (baseStart_499961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_499961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_499961 prefixEnd_499961 := by exact prefixLift 499961
  have htrace : WordTrace (prefixWord ++ tailWord_499961) baseStart_499961 baseEnd_499961 := by
    simpa [prefixWord, tailWord_499961, baseEnd_499961] using wordTrace_append hprefix tailTrace_499961
  have hstable : (prefixWord ++ tailWord_499961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499961).length < 2 ^ (prefixWord ++ tailWord_499961).sum := by decide
  have hdescent : baseEnd_499961 < baseStart_499961 := by decide
  rcases family_descends (prefixWord ++ tailWord_499961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_499962 : List Nat := [3, 1, 1, 1, 1, 7, 1, 1, 3, 2, 2]
def baseStart_499962 : Nat := 118140960795 + 499962 * 2 ^ 59
def prefixEnd_499962 : Nat := 4983230072969 + 3 ^ 40 * 499962 * 2
def baseEnd_499962 : Nat := 256720814983278130075723

theorem tailTrace_499962 : CollatzResearch.WordTrace tailWord_499962 prefixEnd_499962 256720814983278130075723 := by
  unfold tailWord_499962
  simp only [CollatzResearch.WordTrace]
  refine ⟨4558778053682633889181535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12156741476487023704484093 4558778053682633889181535)
  ·
    refine ⟨6838167080523950833772303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4558778053682633889181535 6838167080523950833772303)
    ·
      refine ⟨10257250620785926250658455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6838167080523950833772303 10257250620785926250658455)
      ·
        refine ⟨15385875931178889375987683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10257250620785926250658455 15385875931178889375987683)
        ·
          refine ⟨23078813896768334063981525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15385875931178889375987683 23078813896768334063981525)
          ·
            refine ⟨540909700705507829624567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 23078813896768334063981525 540909700705507829624567)
            ·
              refine ⟨811364551058261744436851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 540909700705507829624567 811364551058261744436851)
              ·
                refine ⟨1217046826587392616655277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 811364551058261744436851 1217046826587392616655277)
                ·
                  refine ⟨456392559970272231245729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1217046826587392616655277 456392559970272231245729)
                  ·
                    refine ⟨342294419977704173434297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 456392559970272231245729 342294419977704173434297)
                    ·
                      refine ⟨256720814983278130075723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 342294419977704173434297 256720814983278130075723)
                      ·
                        rfl

theorem cell23_499962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 1, 1, 3, 2, 2].length) (baseStart_499962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_499962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_499962 prefixEnd_499962 := by exact prefixLift 499962
  have htrace : WordTrace (prefixWord ++ tailWord_499962) baseStart_499962 baseEnd_499962 := by
    simpa [prefixWord, tailWord_499962, baseEnd_499962] using wordTrace_append hprefix tailTrace_499962
  have hstable : (prefixWord ++ tailWord_499962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_499962).length < 2 ^ (prefixWord ++ tailWord_499962).sum := by decide
  have hdescent : baseEnd_499962 < baseStart_499962 := by decide
  rcases family_descends (prefixWord ++ tailWord_499962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500068 : List Nat := [2, 3, 1, 1, 3, 1, 1, 1, 4, 3, 3]
def baseStart_500068 : Nat := 118140960795 + 500068 * 2 ^ 59
def prefixEnd_500068 : Nat := 4983230072969 + 3 ^ 40 * 500068 * 2
def baseEnd_500068 : Nat := 256775243932654715350235

theorem tailTrace_500068 : CollatzResearch.WordTrace tailWord_500068 prefixEnd_500068 256775243932654715350235 := by
  unfold tailWord_500068
  simp only [CollatzResearch.WordTrace]
  refine ⟨9119489176173257830042429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12159318901564343773389905 9119489176173257830042429)
  ·
    refine ⟨3419808441064971686265911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9119489176173257830042429 3419808441064971686265911)
    ·
      refine ⟨5129712661597457529398867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3419808441064971686265911 5129712661597457529398867)
      ·
        refine ⟨7694568992396186294098301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5129712661597457529398867 7694568992396186294098301)
        ·
          refine ⟨2885463372148569860286863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7694568992396186294098301 2885463372148569860286863)
          ·
            refine ⟨4328195058222854790430295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2885463372148569860286863 4328195058222854790430295)
            ·
              refine ⟨6492292587334282185645443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4328195058222854790430295 6492292587334282185645443)
              ·
                refine ⟨9738438881001423278468165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6492292587334282185645443 9738438881001423278468165)
                ·
                  refine ⟨1825957290187766864712781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9738438881001423278468165 1825957290187766864712781)
                  ·
                    refine ⟨684733983820412574267293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1825957290187766864712781 684733983820412574267293)
                    ·
                      refine ⟨256775243932654715350235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 684733983820412574267293 256775243932654715350235)
                      ·
                        rfl

theorem cell23_500068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 1, 4, 3, 3].length) (baseStart_500068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_500068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_500068 prefixEnd_500068 := by exact prefixLift 500068
  have htrace : WordTrace (prefixWord ++ tailWord_500068) baseStart_500068 baseEnd_500068 := by
    simpa [prefixWord, tailWord_500068, baseEnd_500068] using wordTrace_append hprefix tailTrace_500068
  have hstable : (prefixWord ++ tailWord_500068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500068).length < 2 ^ (prefixWord ++ tailWord_500068).sum := by decide
  have hdescent : baseEnd_500068 < baseStart_500068 := by decide
  rcases family_descends (prefixWord ++ tailWord_500068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500069 : List Nat := [1, 3, 1, 3, 1, 5, 1, 2, 2, 2, 2]
def baseStart_500069 : Nat := 118140960795 + 500069 * 2 ^ 59
def prefixEnd_500069 : Nat := 4983230072969 + 3 ^ 40 * 500069 * 2
def baseEnd_500069 : Nat := 256775757413309211437731

theorem tailTrace_500069 : CollatzResearch.WordTrace tailWord_500069 prefixEnd_500069 256775757413309211437731 := by
  unfold tailWord_500069
  simp only [CollatzResearch.WordTrace]
  refine ⟨18239014825342892830871261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12159343216895261887247507 18239014825342892830871261)
  ·
    refine ⟨6839630559503584811576723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18239014825342892830871261 6839630559503584811576723)
    ·
      refine ⟨10259445839255377217365085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6839630559503584811576723 10259445839255377217365085)
      ·
        refine ⟨3847292189720766456511907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10259445839255377217365085 3847292189720766456511907)
        ·
          refine ⟨5770938284581149684767861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3847292189720766456511907 5770938284581149684767861)
          ·
            refine ⟨541025464179482782946987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5770938284581149684767861 541025464179482782946987)
            ·
              refine ⟨811538196269224174420481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 541025464179482782946987 811538196269224174420481)
              ·
                refine ⟨608653647201918130815361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 811538196269224174420481 608653647201918130815361)
                ·
                  refine ⟨456490235401438598111521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 608653647201918130815361 456490235401438598111521)
                  ·
                    refine ⟨342367676551078948583641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 456490235401438598111521 342367676551078948583641)
                    ·
                      refine ⟨256775757413309211437731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 342367676551078948583641 256775757413309211437731)
                      ·
                        rfl

theorem cell23_500069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 1, 2, 2, 2, 2].length) (baseStart_500069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_500069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_500069 prefixEnd_500069 := by exact prefixLift 500069
  have htrace : WordTrace (prefixWord ++ tailWord_500069) baseStart_500069 baseEnd_500069 := by
    simpa [prefixWord, tailWord_500069, baseEnd_500069] using wordTrace_append hprefix tailTrace_500069
  have hstable : (prefixWord ++ tailWord_500069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500069).length < 2 ^ (prefixWord ++ tailWord_500069).sum := by decide
  have hdescent : baseEnd_500069 < baseStart_500069 := by decide
  rcases family_descends (prefixWord ++ tailWord_500069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500081 : List Nat := [1, 2, 2, 2, 1, 2, 1, 3, 1, 1, 7]
def baseStart_500081 : Nat := 118140960795 + 500081 * 2 ^ 59
def prefixEnd_500081 : Nat := 4983230072969 + 3 ^ 40 * 500081 * 2
def baseEnd_500081 : Nat := 256781919181163164487675

theorem tailTrace_500081 : CollatzResearch.WordTrace tailWord_500081 prefixEnd_500081 256781919181163164487675 := by
  unfold tailWord_500081
  simp only [CollatzResearch.WordTrace]
  refine ⟨18239452501299418880308097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12159635000866279253538731 18239452501299418880308097)
  ·
    refine ⟨13679589375974564160231073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18239452501299418880308097 13679589375974564160231073)
    ·
      refine ⟨10259692031980923120173305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13679589375974564160231073 10259692031980923120173305)
      ·
        refine ⟨7694769023985692340129979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10259692031980923120173305 7694769023985692340129979)
        ·
          refine ⟨11542153535978538510194969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7694769023985692340129979 11542153535978538510194969)
          ·
            refine ⟨8656615151983903882646227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11542153535978538510194969 8656615151983903882646227)
            ·
              refine ⟨12984922727975855823969341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8656615151983903882646227 12984922727975855823969341)
              ·
                refine ⟨4869346022990945933988503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12984922727975855823969341 4869346022990945933988503)
                ·
                  refine ⟨7304019034486418900982755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4869346022990945933988503 7304019034486418900982755)
                  ·
                    refine ⟨10956028551729628351474133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7304019034486418900982755 10956028551729628351474133)
                    ·
                      refine ⟨256781919181163164487675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 10956028551729628351474133 256781919181163164487675)
                      ·
                        rfl

theorem cell23_500081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 3, 1, 1, 7].length) (baseStart_500081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_500081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_500081 prefixEnd_500081 := by exact prefixLift 500081
  have htrace : WordTrace (prefixWord ++ tailWord_500081) baseStart_500081 baseEnd_500081 := by
    simpa [prefixWord, tailWord_500081, baseEnd_500081] using wordTrace_append hprefix tailTrace_500081
  have hstable : (prefixWord ++ tailWord_500081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500081).length < 2 ^ (prefixWord ++ tailWord_500081).sum := by decide
  have hdescent : baseEnd_500081 < baseStart_500081 := by decide
  rcases family_descends (prefixWord ++ tailWord_500081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500085 : List Nat := [1, 3, 4, 1, 2, 1, 2, 1, 2, 3, 3]
def baseStart_500085 : Nat := 118140960795 + 500085 * 2 ^ 59
def prefixEnd_500085 : Nat := 4983230072969 + 3 ^ 40 * 500085 * 2
def baseEnd_500085 : Nat := 256783973103781148837657

theorem tailTrace_500085 : CollatzResearch.WordTrace tailWord_500085 prefixEnd_500085 256783973103781148837657 := by
  unfold tailWord_500085
  simp only [CollatzResearch.WordTrace]
  refine ⟨18239598393284927563453709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12159732262189951708969139 18239598393284927563453709)
  ·
    refine ⟨6839849397481847836295141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18239598393284927563453709 6839849397481847836295141)
    ·
      refine ⟨1282471762027846469305339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6839849397481847836295141 1282471762027846469305339)
      ·
        refine ⟨1923707643041769703958009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1282471762027846469305339 1923707643041769703958009)
        ·
          refine ⟨1442780732281327277968507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1923707643041769703958009 1442780732281327277968507)
          ·
            refine ⟨2164171098421990916952761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1442780732281327277968507 2164171098421990916952761)
            ·
              refine ⟨1623128323816493187714571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2164171098421990916952761 1623128323816493187714571)
              ·
                refine ⟨2434692485724739781571857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1623128323816493187714571 2434692485724739781571857)
                ·
                  refine ⟨1826019364293554836178893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2434692485724739781571857 1826019364293554836178893)
                  ·
                    refine ⟨684757261610083063567085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1826019364293554836178893 684757261610083063567085)
                    ·
                      refine ⟨256783973103781148837657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 684757261610083063567085 256783973103781148837657)
                      ·
                        rfl

theorem cell23_500085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 1, 2, 3, 3].length) (baseStart_500085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_500085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_500085 prefixEnd_500085 := by exact prefixLift 500085
  have htrace : WordTrace (prefixWord ++ tailWord_500085) baseStart_500085 baseEnd_500085 := by
    simpa [prefixWord, tailWord_500085, baseEnd_500085] using wordTrace_append hprefix tailTrace_500085
  have hstable : (prefixWord ++ tailWord_500085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500085).length < 2 ^ (prefixWord ++ tailWord_500085).sum := by decide
  have hdescent : baseEnd_500085 < baseStart_500085 := by decide
  rcases family_descends (prefixWord ++ tailWord_500085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500086 : List Nat := [5, 1, 1, 4, 1, 2, 1, 1, 1, 4, 2]
def baseStart_500086 : Nat := 118140960795 + 500086 * 2 ^ 59
def prefixEnd_500086 : Nat := 4983230072969 + 3 ^ 40 * 500086 * 2
def baseEnd_500086 : Nat := 256784486584435644925153

theorem tailTrace_500086 : CollatzResearch.WordTrace tailWord_500086 prefixEnd_500086 256784486584435644925153 := by
  unfold tailWord_500086
  simp only [CollatzResearch.WordTrace]
  refine ⟨1139977179142581545890007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12159756577520869822826741 1139977179142581545890007)
  ·
    refine ⟨1709965768713872318835011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1139977179142581545890007 1709965768713872318835011)
    ·
      refine ⟨2564948653070808478252517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1709965768713872318835011 2564948653070808478252517)
      ·
        refine ⟨480927872450776589672347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2564948653070808478252517 480927872450776589672347)
        ·
          refine ⟨721391808676164884508521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 480927872450776589672347 721391808676164884508521)
          ·
            refine ⟨541043856507123663381391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 721391808676164884508521 541043856507123663381391)
            ·
              refine ⟨811565784760685495072087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 541043856507123663381391 811565784760685495072087)
              ·
                refine ⟨1217348677141028242608131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 811565784760685495072087 1217348677141028242608131)
                ·
                  refine ⟨1826023015711542363912197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1217348677141028242608131 1826023015711542363912197)
                  ·
                    refine ⟨342379315445914193233537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1826023015711542363912197 342379315445914193233537)
                    ·
                      refine ⟨256784486584435644925153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 342379315445914193233537 256784486584435644925153)
                      ·
                        rfl

theorem cell23_500086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_500086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_500086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_500086 prefixEnd_500086 := by exact prefixLift 500086
  have htrace : WordTrace (prefixWord ++ tailWord_500086) baseStart_500086 baseEnd_500086 := by
    simpa [prefixWord, tailWord_500086, baseEnd_500086] using wordTrace_append hprefix tailTrace_500086
  have hstable : (prefixWord ++ tailWord_500086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500086).length < 2 ^ (prefixWord ++ tailWord_500086).sum := by decide
  have hdescent : baseEnd_500086 < baseStart_500086 := by decide
  rcases family_descends (prefixWord ++ tailWord_500086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500101 : List Nat := [1, 3, 1, 1, 3, 1, 1, 1, 1, 10]
def baseStart_500101 : Nat := 118140960795 + 500101 * 2 ^ 59
def prefixEnd_500101 : Nat := 4983230072969 + 3 ^ 40 * 500101 * 2
def baseEnd_500101 : Nat := 85597396264751028745861

theorem tailTrace_500101 : CollatzResearch.WordTrace tailWord_500101 prefixEnd_500101 85597396264751028745861 := by
  unfold tailWord_500101
  simp only [CollatzResearch.WordTrace]
  refine ⟨18240181961226962296036157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12160121307484641530690771 18240181961226962296036157)
  ·
    refine ⟨6840068235460110861013559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18240181961226962296036157 6840068235460110861013559)
    ·
      refine ⟨10260102353190166291520339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6840068235460110861013559 10260102353190166291520339)
      ·
        refine ⟨15390153529785249437280509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10260102353190166291520339 15390153529785249437280509)
        ·
          refine ⟨5771307573669468538980191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15390153529785249437280509 5771307573669468538980191)
          ·
            refine ⟨8656961360504202808470287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5771307573669468538980191 8656961360504202808470287)
            ·
              refine ⟨12985442040756304212705431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8656961360504202808470287 12985442040756304212705431)
              ·
                refine ⟨19478163061134456319058147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12985442040756304212705431 19478163061134456319058147)
                ·
                  refine ⟨29217244591701684478587221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19478163061134456319058147 29217244591701684478587221)
                  ·
                    refine ⟨85597396264751028745861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 29217244591701684478587221 85597396264751028745861)
                    ·
                      rfl

theorem cell23_500101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 10].length) (baseStart_500101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_500101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_500101 prefixEnd_500101 := by exact prefixLift 500101
  have htrace : WordTrace (prefixWord ++ tailWord_500101) baseStart_500101 baseEnd_500101 := by
    simpa [prefixWord, tailWord_500101, baseEnd_500101] using wordTrace_append hprefix tailTrace_500101
  have hstable : (prefixWord ++ tailWord_500101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500101).length < 2 ^ (prefixWord ++ tailWord_500101).sum := by decide
  have hdescent : baseEnd_500101 < baseStart_500101 := by decide
  rcases family_descends (prefixWord ++ tailWord_500101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500108 : List Nat := [2, 2, 1, 2, 1, 4, 2, 1, 1, 3, 4]
def baseStart_500108 : Nat := 118140960795 + 500108 * 2 ^ 59
def prefixEnd_500108 : Nat := 4983230072969 + 3 ^ 40 * 500108 * 2
def baseEnd_500108 : Nat := 256795783158834558850051

theorem tailTrace_500108 : CollatzResearch.WordTrace tailWord_500108 prefixEnd_500108 256795783158834558850051 := by
  unfold tailWord_500108
  simp only [CollatzResearch.WordTrace]
  refine ⟨9120218636100801245770489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12160291514801068327693985 9120218636100801245770489)
  ·
    refine ⟨6840163977075600934327867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9120218636100801245770489 6840163977075600934327867)
    ·
      refine ⟨10260245965613401401491801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6840163977075600934327867 10260245965613401401491801)
      ·
        refine ⟨7695184474210051051118851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10260245965613401401491801 7695184474210051051118851)
        ·
          refine ⟨11542776711315076576678277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7695184474210051051118851 11542776711315076576678277)
          ·
            refine ⟨2164270633371576858127177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11542776711315076576678277 2164270633371576858127177)
            ·
              refine ⟨1623202975028682643595383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2164270633371576858127177 1623202975028682643595383)
              ·
                refine ⟨2434804462543023965393075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1623202975028682643595383 2434804462543023965393075)
                ·
                  refine ⟨3652206693814535948089613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2434804462543023965393075 3652206693814535948089613)
                  ·
                    refine ⟨1369577510180450980533605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3652206693814535948089613 1369577510180450980533605)
                    ·
                      refine ⟨256795783158834558850051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1369577510180450980533605 256795783158834558850051)
                      ·
                        rfl

theorem cell23_500108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 1, 1, 3, 4].length) (baseStart_500108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_500108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_500108 prefixEnd_500108 := by exact prefixLift 500108
  have htrace : WordTrace (prefixWord ++ tailWord_500108) baseStart_500108 baseEnd_500108 := by
    simpa [prefixWord, tailWord_500108, baseEnd_500108] using wordTrace_append hprefix tailTrace_500108
  have hstable : (prefixWord ++ tailWord_500108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500108).length < 2 ^ (prefixWord ++ tailWord_500108).sum := by decide
  have hdescent : baseEnd_500108 < baseStart_500108 := by decide
  rcases family_descends (prefixWord ++ tailWord_500108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500182 : List Nat := [5, 2, 1, 1, 1, 1, 4, 2, 6]
def baseStart_500182 : Nat := 118140960795 + 500182 * 2 ^ 59
def prefixEnd_500182 : Nat := 4983230072969 + 3 ^ 40 * 500182 * 2
def baseEnd_500182 : Nat := 28537086747474141036079

theorem tailTrace_500182 : CollatzResearch.WordTrace tailWord_500182 prefixEnd_500182 28537086747474141036079 := by
  unfold tailWord_500182
  simp only [CollatzResearch.WordTrace]
  refine ⟨1140196017120844570608425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12162090849289008753156533 1140196017120844570608425)
  ·
    refine ⟨855147012840633427956319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1140196017120844570608425 855147012840633427956319)
    ·
      refine ⟨1282720519260950141934479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 855147012840633427956319 1282720519260950141934479)
      ·
        refine ⟨1924080778891425212901719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1282720519260950141934479 1924080778891425212901719)
        ·
          refine ⟨2886121168337137819352579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1924080778891425212901719 2886121168337137819352579)
          ·
            refine ⟨4329181752505706729028869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2886121168337137819352579 4329181752505706729028869)
            ·
              refine ⟨811721578594820011692913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4329181752505706729028869 811721578594820011692913)
              ·
                refine ⟨608791183946115008769685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 811721578594820011692913 608791183946115008769685)
                ·
                  refine ⟨28537086747474141036079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 608791183946115008769685 28537086747474141036079)
                  ·
                    rfl

theorem cell23_500182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 4, 2, 6].length) (baseStart_500182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_500182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_500182 prefixEnd_500182 := by exact prefixLift 500182
  have htrace : WordTrace (prefixWord ++ tailWord_500182) baseStart_500182 baseEnd_500182 := by
    simpa [prefixWord, tailWord_500182, baseEnd_500182] using wordTrace_append hprefix tailTrace_500182
  have hstable : (prefixWord ++ tailWord_500182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500182).length < 2 ^ (prefixWord ++ tailWord_500182).sum := by decide
  have hdescent : baseEnd_500182 < baseStart_500182 := by decide
  rcases family_descends (prefixWord ++ tailWord_500182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500218 : List Nat := [3, 1, 1, 1, 1, 2, 2, 1, 5, 1, 5]
def baseStart_500218 : Nat := 118140960795 + 500218 * 2 ^ 59
def prefixEnd_500218 : Nat := 4983230072969 + 3 ^ 40 * 500218 * 2
def baseEnd_500218 : Nat := 256852266030829128474545

theorem tailTrace_500218 : CollatzResearch.WordTrace tailWord_500218 prefixEnd_500218 256852266030829128474545 := by
  unfold tailWord_500218
  simp only [CollatzResearch.WordTrace]
  refine ⟨4561112325450772819511327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12162966201202060852030205 4561112325450772819511327)
  ·
    refine ⟨6841668488176159229266991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4561112325450772819511327 6841668488176159229266991)
    ·
      refine ⟨10262502732264238843900487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6841668488176159229266991 10262502732264238843900487)
      ·
        refine ⟨15393754098396358265850731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10262502732264238843900487 15393754098396358265850731)
        ·
          refine ⟨23090631147594537398776097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15393754098396358265850731 23090631147594537398776097)
          ·
            refine ⟨17317973360695903049082073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23090631147594537398776097 17317973360695903049082073)
            ·
              refine ⟨12988480020521927286811555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17317973360695903049082073 12988480020521927286811555)
              ·
                refine ⟨19482720030782890930217333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12988480020521927286811555 19482720030782890930217333)
                ·
                  refine ⟨1826505002885896024707875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19482720030782890930217333 1826505002885896024707875)
                  ·
                    refine ⟨2739757504328844037061813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1826505002885896024707875 2739757504328844037061813)
                    ·
                      refine ⟨256852266030829128474545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2739757504328844037061813 256852266030829128474545)
                      ·
                        rfl

theorem cell23_500218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 5, 1, 5].length) (baseStart_500218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_500218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_500218 prefixEnd_500218 := by exact prefixLift 500218
  have htrace : WordTrace (prefixWord ++ tailWord_500218) baseStart_500218 baseEnd_500218 := by
    simpa [prefixWord, tailWord_500218, baseEnd_500218] using wordTrace_append hprefix tailTrace_500218
  have hstable : (prefixWord ++ tailWord_500218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500218).length < 2 ^ (prefixWord ++ tailWord_500218).sum := by decide
  have hdescent : baseEnd_500218 < baseStart_500218 := by decide
  rcases family_descends (prefixWord ++ tailWord_500218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500225 : List Nat := [1, 2, 4, 1, 3, 1, 2, 2, 1, 6]
def baseStart_500225 : Nat := 118140960795 + 500225 * 2 ^ 59
def prefixEnd_500225 : Nat := 4983230072969 + 3 ^ 40 * 500225 * 2
def baseEnd_500225 : Nat := 85618620131803533695671

theorem tailTrace_500225 : CollatzResearch.WordTrace tailWord_500225 prefixEnd_500225 85618620131803533695671 := by
  unfold tailWord_500225
  simp only [CollatzResearch.WordTrace]
  refine ⟨18244704612777731473550129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12163136408518487649033419 18244704612777731473550129)
  ·
    refine ⟨13683528459583298605162597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18244704612777731473550129 13683528459583298605162597)
    ·
      refine ⟨2565661586171868488467987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13683528459583298605162597 2565661586171868488467987)
      ·
        refine ⟨3848492379257802732701981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2565661586171868488467987 3848492379257802732701981)
        ·
          refine ⟨1443184642221676024763243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3848492379257802732701981 1443184642221676024763243)
          ·
            refine ⟨2164776963332514037144865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1443184642221676024763243 2164776963332514037144865)
            ·
              refine ⟨1623582722499385527858649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2164776963332514037144865 1623582722499385527858649)
              ·
                refine ⟨1217687041874539145893987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1623582722499385527858649 1217687041874539145893987)
                ·
                  refine ⟨1826530562811808718840981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1217687041874539145893987 1826530562811808718840981)
                  ·
                    refine ⟨85618620131803533695671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1826530562811808718840981 85618620131803533695671)
                    ·
                      rfl

theorem cell23_500225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 2, 1, 6].length) (baseStart_500225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_500225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_500225 prefixEnd_500225 := by exact prefixLift 500225
  have htrace : WordTrace (prefixWord ++ tailWord_500225) baseStart_500225 baseEnd_500225 := by
    simpa [prefixWord, tailWord_500225, baseEnd_500225] using wordTrace_append hprefix tailTrace_500225
  have hstable : (prefixWord ++ tailWord_500225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500225).length < 2 ^ (prefixWord ++ tailWord_500225).sum := by decide
  have hdescent : baseEnd_500225 < baseStart_500225 := by decide
  rcases family_descends (prefixWord ++ tailWord_500225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500232 : List Nat := [2, 1, 3, 2, 1, 1, 1, 1, 7, 2, 2]
def baseStart_500232 : Nat := 118140960795 + 500232 * 2 ^ 59
def prefixEnd_500232 : Nat := 4983230072969 + 3 ^ 40 * 500232 * 2
def baseEnd_500232 : Nat := 256859454759992073699481

theorem tailTrace_500232 : CollatzResearch.WordTrace tailWord_500232 prefixEnd_500232 256859454759992073699481 := by
  unfold tailWord_500232
  simp only [CollatzResearch.WordTrace]
  refine ⟨9122479961876185834527475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12163306615834914446036633 9122479961876185834527475)
  ·
    refine ⟨13683719942814278751791213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9122479961876185834527475 13683719942814278751791213)
    ·
      refine ⟨5131394978555354531921705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13683719942814278751791213 5131394978555354531921705)
      ·
        refine ⟨3848546233916515898941279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5131394978555354531921705 3848546233916515898941279)
        ·
          refine ⟨5772819350874773848411919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3848546233916515898941279 5772819350874773848411919)
          ·
            refine ⟨8659229026312160772617879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5772819350874773848411919 8659229026312160772617879)
            ·
              refine ⟨12988843539468241158926819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8659229026312160772617879 12988843539468241158926819)
              ·
                refine ⟨19483265309202361738390229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12988843539468241158926819 19483265309202361738390229)
                ·
                  refine ⟨456639030684430353243521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19483265309202361738390229 456639030684430353243521)
                  ·
                    refine ⟨342479273013322764932641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 456639030684430353243521 342479273013322764932641)
                    ·
                      refine ⟨256859454759992073699481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 342479273013322764932641 256859454759992073699481)
                      ·
                        rfl

theorem cell23_500232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 7, 2, 2].length) (baseStart_500232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_500232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_500232 prefixEnd_500232 := by exact prefixLift 500232
  have htrace : WordTrace (prefixWord ++ tailWord_500232) baseStart_500232 baseEnd_500232 := by
    simpa [prefixWord, tailWord_500232, baseEnd_500232] using wordTrace_append hprefix tailTrace_500232
  have hstable : (prefixWord ++ tailWord_500232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500232).length < 2 ^ (prefixWord ++ tailWord_500232).sum := by decide
  have hdescent : baseEnd_500232 < baseStart_500232 := by decide
  rcases family_descends (prefixWord ++ tailWord_500232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500259 : List Nat := [1, 1, 1, 4, 4, 2, 3, 1, 2, 4]
def baseStart_500259 : Nat := 118140960795 + 500259 * 2 ^ 59
def prefixEnd_500259 : Nat := 4983230072969 + 3 ^ 40 * 500259 * 2
def baseEnd_500259 : Nat := 85624439579221156020619

theorem tailTrace_500259 : CollatzResearch.WordTrace tailWord_500259 prefixEnd_500259 85624439579221156020619 := by
  unfold tailWord_500259
  simp only [CollatzResearch.WordTrace]
  refine ⟨18245944694654555280287831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12163963129769703520191887 18245944694654555280287831)
  ·
    refine ⟨27368917041981832920431747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18245944694654555280287831 27368917041981832920431747)
    ·
      refine ⟨41053375562972749380647621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27368917041981832920431747 41053375562972749380647621)
      ·
        refine ⟨7697507918057390508871429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41053375562972749380647621 7697507918057390508871429)
        ·
          refine ⟨1443282734635760720413393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7697507918057390508871429 1443282734635760720413393)
          ·
            refine ⟨1082462050976820540310045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1443282734635760720413393 1082462050976820540310045)
            ·
              refine ⟨405923269116307702616267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1082462050976820540310045 405923269116307702616267)
              ·
                refine ⟨608884903674461553924401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 405923269116307702616267 608884903674461553924401)
                ·
                  refine ⟨456663677755846165443301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 608884903674461553924401 456663677755846165443301)
                  ·
                    refine ⟨85624439579221156020619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 456663677755846165443301 85624439579221156020619)
                    ·
                      rfl

theorem cell23_500259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 3, 1, 2, 4].length) (baseStart_500259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_500259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_500259 prefixEnd_500259 := by exact prefixLift 500259
  have htrace : WordTrace (prefixWord ++ tailWord_500259) baseStart_500259 baseEnd_500259 := by
    simpa [prefixWord, tailWord_500259, baseEnd_500259] using wordTrace_append hprefix tailTrace_500259
  have hstable : (prefixWord ++ tailWord_500259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500259).length < 2 ^ (prefixWord ++ tailWord_500259).sum := by decide
  have hdescent : baseEnd_500259 < baseStart_500259 := by decide
  rcases family_descends (prefixWord ++ tailWord_500259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500268 : List Nat := [2, 2, 1, 1, 1, 2, 1, 4, 2, 7]
def baseStart_500268 : Nat := 118140960795 + 500268 * 2 ^ 59
def prefixEnd_500268 : Nat := 4983230072969 + 3 ^ 40 * 500268 * 2
def baseEnd_500268 : Nat := 85625980021184644283105

theorem tailTrace_500268 : CollatzResearch.WordTrace tailWord_500268 prefixEnd_500268 85625980021184644283105 := by
  unfold tailWord_500268
  simp only [CollatzResearch.WordTrace]
  refine ⟨9123136475810974908682729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12164181967747966544910305 9123136475810974908682729)
  ·
    refine ⟨6842352356858231181512047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9123136475810974908682729 6842352356858231181512047)
    ·
      refine ⟨10263528535287346772268071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6842352356858231181512047 10263528535287346772268071)
      ·
        refine ⟨15395292802931020158402107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10263528535287346772268071 15395292802931020158402107)
        ·
          refine ⟨23092939204396530237603161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15395292802931020158402107 23092939204396530237603161)
          ·
            refine ⟨17319704403297397678202371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23092939204396530237603161 17319704403297397678202371)
            ·
              refine ⟨25979556604946096517303557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17319704403297397678202371 25979556604946096517303557)
              ·
                refine ⟨4871166863427393096994417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25979556604946096517303557 4871166863427393096994417)
                ·
                  refine ⟨3653375147570544822745813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4871166863427393096994417 3653375147570544822745813)
                  ·
                    refine ⟨85625980021184644283105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3653375147570544822745813 85625980021184644283105)
                    ·
                      rfl

theorem cell23_500268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 7].length) (baseStart_500268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_500268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_500268 prefixEnd_500268 := by exact prefixLift 500268
  have htrace : WordTrace (prefixWord ++ tailWord_500268) baseStart_500268 baseEnd_500268 := by
    simpa [prefixWord, tailWord_500268, baseEnd_500268] using wordTrace_append hprefix tailTrace_500268
  have hstable : (prefixWord ++ tailWord_500268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500268).length < 2 ^ (prefixWord ++ tailWord_500268).sum := by decide
  have hdescent : baseEnd_500268 < baseStart_500268 := by decide
  rcases family_descends (prefixWord ++ tailWord_500268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500282 : List Nat := [3, 1, 1, 1, 3, 3, 1, 2, 4, 1, 3]
def baseStart_500282 : Nat := 118140960795 + 500282 * 2 ^ 59
def prefixEnd_500282 : Nat := 4983230072969 + 3 ^ 40 * 500282 * 2
def baseEnd_500282 : Nat := 256885128792716878074251

theorem tailTrace_500282 : CollatzResearch.WordTrace tailWord_500282 prefixEnd_500282 256885128792716878074251 := by
  unfold tailWord_500282
  simp only [CollatzResearch.WordTrace]
  refine ⟨4561695893392807552093775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12164522382380820138916733 4561695893392807552093775)
  ·
    refine ⟨6842543840089211328140663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4561695893392807552093775 6842543840089211328140663)
    ·
      refine ⟨10263815760133816992210995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6842543840089211328140663 10263815760133816992210995)
      ·
        refine ⟨15395723640200725488316493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10263815760133816992210995 15395723640200725488316493)
        ·
          refine ⟨5773396365075272058118685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15395723640200725488316493 5773396365075272058118685)
          ·
            refine ⟨2165023636903227021794507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5773396365075272058118685 2165023636903227021794507)
            ·
              refine ⟨3247535455354840532691761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2165023636903227021794507 3247535455354840532691761)
              ·
                refine ⟨2435651591516130399518821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3247535455354840532691761 2435651591516130399518821)
                ·
                  refine ⟨456684673409274449909779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2435651591516130399518821 456684673409274449909779)
                  ·
                    refine ⟨685027010113911674864669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 456684673409274449909779 685027010113911674864669)
                    ·
                      refine ⟨256885128792716878074251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 685027010113911674864669 256885128792716878074251)
                      ·
                        rfl

theorem cell23_500282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 1, 2, 4, 1, 3].length) (baseStart_500282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_500282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_500282 prefixEnd_500282 := by exact prefixLift 500282
  have htrace : WordTrace (prefixWord ++ tailWord_500282) baseStart_500282 baseEnd_500282 := by
    simpa [prefixWord, tailWord_500282, baseEnd_500282] using wordTrace_append hprefix tailTrace_500282
  have hstable : (prefixWord ++ tailWord_500282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500282).length < 2 ^ (prefixWord ++ tailWord_500282).sum := by decide
  have hdescent : baseEnd_500282 < baseStart_500282 := by decide
  rcases family_descends (prefixWord ++ tailWord_500282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500316 : List Nat := [2, 2, 4, 1, 3, 1, 1, 3, 2, 1, 3]
def baseStart_500316 : Nat := 118140960795 + 500316 * 2 ^ 59
def prefixEnd_500316 : Nat := 4983230072969 + 3 ^ 40 * 500316 * 2
def baseEnd_500316 : Nat := 256902587134969745049095

theorem tailTrace_500316 : CollatzResearch.WordTrace tailWord_500316 prefixEnd_500316 256902587134969745049095 := by
  unfold tailWord_500316
  simp only [CollatzResearch.WordTrace]
  refine ⟨9124011827724027007556401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12165349103632036010075201 9124011827724027007556401)
  ·
    refine ⟨6843008870793020255667301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9124011827724027007556401 6843008870793020255667301)
    ·
      refine ⟨1283064163273691297937619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6843008870793020255667301 1283064163273691297937619)
      ·
        refine ⟨1924596244910536946906429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1283064163273691297937619 1924596244910536946906429)
        ·
          refine ⟨721723591841451355089911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1924596244910536946906429 721723591841451355089911)
          ·
            refine ⟨1082585387762177032634867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 721723591841451355089911 1082585387762177032634867)
            ·
              refine ⟨1623878081643265548952301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1082585387762177032634867 1623878081643265548952301)
              ·
                refine ⟨608954280616224580857113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1623878081643265548952301 608954280616224580857113)
                ·
                  refine ⟨456715710462168435642835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 608954280616224580857113 456715710462168435642835)
                  ·
                    refine ⟨685073565693252653464253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 456715710462168435642835 685073565693252653464253)
                    ·
                      refine ⟨256902587134969745049095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 685073565693252653464253 256902587134969745049095)
                      ·
                        rfl

theorem cell23_500316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 1, 3, 2, 1, 3].length) (baseStart_500316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_500316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_500316 prefixEnd_500316 := by exact prefixLift 500316
  have htrace : WordTrace (prefixWord ++ tailWord_500316) baseStart_500316 baseEnd_500316 := by
    simpa [prefixWord, tailWord_500316, baseEnd_500316] using wordTrace_append hprefix tailTrace_500316
  have hstable : (prefixWord ++ tailWord_500316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500316).length < 2 ^ (prefixWord ++ tailWord_500316).sum := by decide
  have hdescent : baseEnd_500316 < baseStart_500316 := by decide
  rcases family_descends (prefixWord ++ tailWord_500316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500356 : List Nat := [2, 3, 2, 1, 3, 1, 1, 4, 2, 2, 2]
def baseStart_500356 : Nat := 118140960795 + 500356 * 2 ^ 59
def prefixEnd_500356 : Nat := 4983230072969 + 3 ^ 40 * 500356 * 2
def baseEnd_500356 : Nat := 256923126361149588548911

theorem tailTrace_500356 : CollatzResearch.WordTrace tailWord_500356 prefixEnd_500356 256923126361149588548911 := by
  unfold tailWord_500356
  simp only [CollatzResearch.WordTrace]
  refine ⟨9124741287651570423284461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12166321716868760564379281 9124741287651570423284461)
  ·
    refine ⟨3421777982869338908731673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9124741287651570423284461 3421777982869338908731673)
    ·
      refine ⟨2566333487152004181548755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3421777982869338908731673 2566333487152004181548755)
      ·
        refine ⟨3849500230728006272323133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2566333487152004181548755 3849500230728006272323133)
        ·
          refine ⟨1443562586523002352121175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3849500230728006272323133 1443562586523002352121175)
          ·
            refine ⟨2165343879784503528181763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1443562586523002352121175 2165343879784503528181763)
            ·
              refine ⟨3248015819676755292272645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2165343879784503528181763 3248015819676755292272645)
              ·
                refine ⟨609002966189391617301121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3248015819676755292272645 609002966189391617301121)
                ·
                  refine ⟨456752224642043712975841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 609002966189391617301121 456752224642043712975841)
                  ·
                    refine ⟨342564168481532784731881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 456752224642043712975841 342564168481532784731881)
                    ·
                      refine ⟨256923126361149588548911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 342564168481532784731881 256923126361149588548911)
                      ·
                        rfl

theorem cell23_500356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 4, 2, 2, 2].length) (baseStart_500356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_500356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_500356 prefixEnd_500356 := by exact prefixLift 500356
  have htrace : WordTrace (prefixWord ++ tailWord_500356) baseStart_500356 baseEnd_500356 := by
    simpa [prefixWord, tailWord_500356, baseEnd_500356] using wordTrace_append hprefix tailTrace_500356
  have hstable : (prefixWord ++ tailWord_500356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500356).length < 2 ^ (prefixWord ++ tailWord_500356).sum := by decide
  have hdescent : baseEnd_500356 < baseStart_500356 := by decide
  rcases family_descends (prefixWord ++ tailWord_500356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500375 : List Nat := [1, 1, 3, 3, 2, 1, 2, 2, 1, 7]
def baseStart_500375 : Nat := 118140960795 + 500375 * 2 ^ 59
def prefixEnd_500375 : Nat := 4983230072969 + 3 ^ 40 * 500375 * 2
def baseEnd_500375 : Nat := 85644294164528338070441

theorem tailTrace_500375 : CollatzResearch.WordTrace tailWord_500375 prefixEnd_500375 85644294164528338070441 := by
  unfold tailWord_500375
  simp only [CollatzResearch.WordTrace]
  refine ⟨18250175562234307091510579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12166783708156204727673719 18250175562234307091510579)
  ·
    refine ⟨27375263343351460637265869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18250175562234307091510579 27375263343351460637265869)
    ·
      refine ⟨10265723753756797738974701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27375263343351460637265869 10265723753756797738974701)
      ·
        refine ⟨3849646407658799152115513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10265723753756797738974701 3849646407658799152115513)
        ·
          refine ⟨2887234805744099364086635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3849646407658799152115513 2887234805744099364086635)
          ·
            refine ⟨4330852208616149046129953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2887234805744099364086635 4330852208616149046129953)
            ·
              refine ⟨3248139156462111784597465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4330852208616149046129953 3248139156462111784597465)
              ·
                refine ⟨2436104367346583838448099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3248139156462111784597465 2436104367346583838448099)
                ·
                  refine ⟨3654156551019875757672149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2436104367346583838448099 3654156551019875757672149)
                  ·
                    refine ⟨85644294164528338070441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3654156551019875757672149 85644294164528338070441)
                    ·
                      rfl

theorem cell23_500375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 2, 1, 7].length) (baseStart_500375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_500375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_500375 prefixEnd_500375 := by exact prefixLift 500375
  have htrace : WordTrace (prefixWord ++ tailWord_500375) baseStart_500375 baseEnd_500375 := by
    simpa [prefixWord, tailWord_500375, baseEnd_500375] using wordTrace_append hprefix tailTrace_500375
  have hstable : (prefixWord ++ tailWord_500375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500375).length < 2 ^ (prefixWord ++ tailWord_500375).sum := by decide
  have hdescent : baseEnd_500375 < baseStart_500375 := by decide
  rcases family_descends (prefixWord ++ tailWord_500375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500412 : List Nat := [2, 2, 2, 3, 1, 1, 2, 1, 4, 1, 4]
def baseStart_500412 : Nat := 118140960795 + 500412 * 2 ^ 59
def prefixEnd_500412 : Nat := 4983230072969 + 3 ^ 40 * 500412 * 2
def baseEnd_500412 : Nat := 256951881277801369448653

theorem tailTrace_500412 : CollatzResearch.WordTrace tailWord_500412 prefixEnd_500412 256951881277801369448653 := by
  unfold tailWord_500412
  simp only [CollatzResearch.WordTrace]
  refine ⟨9125762531550131205303745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12167683375400174940404993 9125762531550131205303745)
  ·
    refine ⟨6844321898662598403977809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9125762531550131205303745 6844321898662598403977809)
    ·
      refine ⟨5133241423996948802983357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6844321898662598403977809 5133241423996948802983357)
      ·
        refine ⟨1924965533998855801118759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5133241423996948802983357 1924965533998855801118759)
        ·
          refine ⟨2887448300998283701678139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1924965533998855801118759 2887448300998283701678139)
          ·
            refine ⟨4331172451497425552517209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2887448300998283701678139 4331172451497425552517209)
            ·
              refine ⟨3248379338623069164387907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4331172451497425552517209 3248379338623069164387907)
              ·
                refine ⟨4872569007934603746581861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3248379338623069164387907 4872569007934603746581861)
                ·
                  refine ⟨913606688987738202484099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4872569007934603746581861 913606688987738202484099)
                  ·
                    refine ⟨1370410033481607303726149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 913606688987738202484099 1370410033481607303726149)
                    ·
                      refine ⟨256951881277801369448653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1370410033481607303726149 256951881277801369448653)
                      ·
                        rfl

theorem cell23_500412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_500412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_500412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_500412 prefixEnd_500412 := by exact prefixLift 500412
  have htrace : WordTrace (prefixWord ++ tailWord_500412) baseStart_500412 baseEnd_500412 := by
    simpa [prefixWord, tailWord_500412, baseEnd_500412] using wordTrace_append hprefix tailTrace_500412
  have hstable : (prefixWord ++ tailWord_500412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500412).length < 2 ^ (prefixWord ++ tailWord_500412).sum := by decide
  have hdescent : baseEnd_500412 < baseStart_500412 := by decide
  rcases family_descends (prefixWord ++ tailWord_500412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500506 : List Nat := [3, 1, 1, 3, 2, 1, 4, 1, 2, 3, 2]
def baseStart_500506 : Nat := 118140960795 + 500506 * 2 ^ 59
def prefixEnd_500506 : Nat := 4983230072969 + 3 ^ 40 * 500506 * 2
def baseEnd_500506 : Nat := 257000148459324001673221

theorem tailTrace_500506 : CollatzResearch.WordTrace tailWord_500506 prefixEnd_500506 257000148459324001673221 := by
  unfold tailWord_500506
  simp only [CollatzResearch.WordTrace]
  refine ⟨4563738381189929116132343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12169969016506477643019581 4563738381189929116132343)
  ·
    refine ⟨6845607571784893674198515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4563738381189929116132343 6845607571784893674198515)
    ·
      refine ⟨10268411357677340511297773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6845607571784893674198515 10268411357677340511297773)
      ·
        refine ⟨3850654259129002691736665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10268411357677340511297773 3850654259129002691736665)
        ·
          refine ⟨2887990694346752018802499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3850654259129002691736665 2887990694346752018802499)
          ·
            refine ⟨4331986041520128028203749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2887990694346752018802499 4331986041520128028203749)
            ·
              refine ⟨812247382785024005288203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4331986041520128028203749 812247382785024005288203)
              ·
                refine ⟨1218371074177536007932305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 812247382785024005288203 1218371074177536007932305)
                ·
                  refine ⟨913778305633152005949229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1218371074177536007932305 913778305633152005949229)
                  ·
                    refine ⟨342666864612432002230961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 913778305633152005949229 342666864612432002230961)
                    ·
                      refine ⟨257000148459324001673221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 342666864612432002230961 257000148459324001673221)
                      ·
                        rfl

theorem cell23_500506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 4, 1, 2, 3, 2].length) (baseStart_500506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_500506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_500506 prefixEnd_500506 := by exact prefixLift 500506
  have htrace : WordTrace (prefixWord ++ tailWord_500506) baseStart_500506 baseEnd_500506 := by
    simpa [prefixWord, tailWord_500506, baseEnd_500506] using wordTrace_append hprefix tailTrace_500506
  have hstable : (prefixWord ++ tailWord_500506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500506).length < 2 ^ (prefixWord ++ tailWord_500506).sum := by decide
  have hdescent : baseEnd_500506 < baseStart_500506 := by decide
  rcases family_descends (prefixWord ++ tailWord_500506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500512 : List Nat := [2, 1, 1, 5, 1, 2, 1, 1, 3, 6]
def baseStart_500512 : Nat := 118140960795 + 500512 * 2 ^ 59
def prefixEnd_500512 : Nat := 4983230072969 + 3 ^ 40 * 500512 * 2
def baseEnd_500512 : Nat := 85667743114416992732731

theorem tailTrace_500512 : CollatzResearch.WordTrace tailWord_500512 prefixEnd_500512 85667743114416992732731 := by
  unfold tailWord_500512
  simp only [CollatzResearch.WordTrace]
  refine ⟨9127586181368989744623895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12170114908491986326165193 9127586181368989744623895)
  ·
    refine ⟨13691379272053484616935843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9127586181368989744623895 13691379272053484616935843)
    ·
      refine ⟨20537068908080226925403765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13691379272053484616935843 20537068908080226925403765)
      ·
        refine ⟨1925350210132521274256603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20537068908080226925403765 1925350210132521274256603)
        ·
          refine ⟨2888025315198781911384905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1925350210132521274256603 2888025315198781911384905)
          ·
            refine ⟨2166018986399086433538679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2888025315198781911384905 2166018986399086433538679)
            ·
              refine ⟨3249028479598629650308019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2166018986399086433538679 3249028479598629650308019)
              ·
                refine ⟨4873542719397944475462029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3249028479598629650308019 4873542719397944475462029)
                ·
                  refine ⟨1827578519774229178298261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4873542719397944475462029 1827578519774229178298261)
                  ·
                    refine ⟨85667743114416992732731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1827578519774229178298261 85667743114416992732731)
                    ·
                      rfl

theorem cell23_500512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 1, 3, 6].length) (baseStart_500512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_500512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_500512 prefixEnd_500512 := by exact prefixLift 500512
  have htrace : WordTrace (prefixWord ++ tailWord_500512) baseStart_500512 baseEnd_500512 := by
    simpa [prefixWord, tailWord_500512, baseEnd_500512] using wordTrace_append hprefix tailTrace_500512
  have hstable : (prefixWord ++ tailWord_500512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500512).length < 2 ^ (prefixWord ++ tailWord_500512).sum := by decide
  have hdescent : baseEnd_500512 < baseStart_500512 := by decide
  rcases family_descends (prefixWord ++ tailWord_500512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500536 : List Nat := [2, 1, 2, 1, 3, 2, 2, 3, 3, 2, 2]
def baseStart_500536 : Nat := 118140960795 + 500536 * 2 ^ 59
def prefixEnd_500536 : Nat := 4983230072969 + 3 ^ 40 * 500536 * 2
def baseEnd_500536 : Nat := 257015552878958884298083

theorem tailTrace_500536 : CollatzResearch.WordTrace tailWord_500536 prefixEnd_500536 257015552878958884298083 := by
  unfold tailWord_500536
  simp only [CollatzResearch.WordTrace]
  refine ⟨9128023857325515794060731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12170698476434021058747641 9128023857325515794060731)
  ·
    refine ⟨13692035785988273691091097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9128023857325515794060731 13692035785988273691091097)
    ·
      refine ⟨10269026839491205268318323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13692035785988273691091097 10269026839491205268318323)
      ·
        refine ⟨15403540259236807902477485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10269026839491205268318323 15403540259236807902477485)
        ·
          refine ⟨5776327597213802963429057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15403540259236807902477485 5776327597213802963429057)
          ·
            refine ⟨4332245697910352222571793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5776327597213802963429057 4332245697910352222571793)
            ·
              refine ⟨3249184273432764166928845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4332245697910352222571793 3249184273432764166928845)
              ·
                refine ⟨1218444102537286562598317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3249184273432764166928845 1218444102537286562598317)
                ·
                  refine ⟨456916538451482460974369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1218444102537286562598317 456916538451482460974369)
                  ·
                    refine ⟨342687403838611845730777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 456916538451482460974369 342687403838611845730777)
                    ·
                      refine ⟨257015552878958884298083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 342687403838611845730777 257015552878958884298083)
                      ·
                        rfl

theorem cell23_500536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 3, 3, 2, 2].length) (baseStart_500536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_500536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_500536 prefixEnd_500536 := by exact prefixLift 500536
  have htrace : WordTrace (prefixWord ++ tailWord_500536) baseStart_500536 baseEnd_500536 := by
    simpa [prefixWord, tailWord_500536, baseEnd_500536] using wordTrace_append hprefix tailTrace_500536
  have hstable : (prefixWord ++ tailWord_500536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500536).length < 2 ^ (prefixWord ++ tailWord_500536).sum := by decide
  have hdescent : baseEnd_500536 < baseStart_500536 := by decide
  rcases family_descends (prefixWord ++ tailWord_500536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500557 : List Nat := [1, 6, 1, 2, 3, 1, 1, 1, 2, 3, 2]
def baseStart_500557 : Nat := 118140960795 + 500557 * 2 ^ 59
def prefixEnd_500557 : Nat := 4983230072969 + 3 ^ 40 * 500557 * 2
def baseEnd_500557 : Nat := 257026335972703302135487

theorem tailTrace_500557 : CollatzResearch.WordTrace tailWord_500557 prefixEnd_500557 257026335972703302135487 := by
  unfold tailWord_500557
  simp only [CollatzResearch.WordTrace]
  refine ⟨18256813647574952174635925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12171209098383301449757283 18256813647574952174635925)
  ·
    refine ⟨855788139730075883186059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 18256813647574952174635925 855788139730075883186059)
    ·
      refine ⟨1283682209595113824779089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 855788139730075883186059 1283682209595113824779089)
      ·
        refine ⟨962761657196335368584317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1283682209595113824779089 962761657196335368584317)
        ·
          refine ⟨361035621448625763219119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 962761657196335368584317 361035621448625763219119)
          ·
            refine ⟨541553432172938644828679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 361035621448625763219119 541553432172938644828679)
            ·
              refine ⟨812330148259407967243019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 541553432172938644828679 812330148259407967243019)
              ·
                refine ⟨1218495222389111950864529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 812330148259407967243019 1218495222389111950864529)
                ·
                  refine ⟨913871416791833963148397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1218495222389111950864529 913871416791833963148397)
                  ·
                    refine ⟨342701781296937736180649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 913871416791833963148397 342701781296937736180649)
                    ·
                      refine ⟨257026335972703302135487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 342701781296937736180649 257026335972703302135487)
                      ·
                        rfl

theorem cell23_500557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 1, 1, 2, 3, 2].length) (baseStart_500557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_500557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_500557 prefixEnd_500557 := by exact prefixLift 500557
  have htrace : WordTrace (prefixWord ++ tailWord_500557) baseStart_500557 baseEnd_500557 := by
    simpa [prefixWord, tailWord_500557, baseEnd_500557] using wordTrace_append hprefix tailTrace_500557
  have hstable : (prefixWord ++ tailWord_500557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500557).length < 2 ^ (prefixWord ++ tailWord_500557).sum := by decide
  have hdescent : baseEnd_500557 < baseStart_500557 := by decide
  rcases family_descends (prefixWord ++ tailWord_500557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500569 : List Nat := [1, 2, 1, 2, 2, 4, 2, 2, 1, 3, 3]
def baseStart_500569 : Nat := 118140960795 + 500569 * 2 ^ 59
def prefixEnd_500569 : Nat := 4983230072969 + 3 ^ 40 * 500569 * 2
def baseEnd_500569 : Nat := 257032497740557255185431

theorem tailTrace_500569 : CollatzResearch.WordTrace tailWord_500569 prefixEnd_500569 257032497740557255185431 := by
  unfold tailWord_500569
  simp only [CollatzResearch.WordTrace]
  refine ⟨18257251323531478224072761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12171500882354318816048507 18257251323531478224072761)
  ·
    refine ⟨13692938492648608668054571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18257251323531478224072761 13692938492648608668054571)
    ·
      refine ⟨20539407738972913002081857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13692938492648608668054571 20539407738972913002081857)
      ·
        refine ⟨15404555804229684751561393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20539407738972913002081857 15404555804229684751561393)
        ·
          refine ⟨11553416853172263563671045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15404555804229684751561393 11553416853172263563671045)
          ·
            refine ⟨2166265659969799418188321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11553416853172263563671045 2166265659969799418188321)
            ·
              refine ⟨1624699244977349563641241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2166265659969799418188321 1624699244977349563641241)
              ·
                refine ⟨1218524433733012172730931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1624699244977349563641241 1218524433733012172730931)
                ·
                  refine ⟨1827786650599518259096397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1218524433733012172730931 1827786650599518259096397)
                  ·
                    refine ⟨685419993974819347161149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1827786650599518259096397 685419993974819347161149)
                    ·
                      refine ⟨257032497740557255185431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 685419993974819347161149 257032497740557255185431)
                      ·
                        rfl

theorem cell23_500569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 2, 1, 3, 3].length) (baseStart_500569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_500569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_500569 prefixEnd_500569 := by exact prefixLift 500569
  have htrace : WordTrace (prefixWord ++ tailWord_500569) baseStart_500569 baseEnd_500569 := by
    simpa [prefixWord, tailWord_500569, baseEnd_500569] using wordTrace_append hprefix tailTrace_500569
  have hstable : (prefixWord ++ tailWord_500569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500569).length < 2 ^ (prefixWord ++ tailWord_500569).sum := by decide
  have hdescent : baseEnd_500569 < baseStart_500569 := by decide
  rcases family_descends (prefixWord ++ tailWord_500569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500570 : List Nat := [3, 1, 1, 2, 1, 5, 2, 3, 1, 2, 2]
def baseStart_500570 : Nat := 118140960795 + 500570 * 2 ^ 59
def prefixEnd_500570 : Nat := 4983230072969 + 3 ^ 40 * 500570 * 2
def baseEnd_500570 : Nat := 257033011221211751272927

theorem tailTrace_500570 : CollatzResearch.WordTrace tailWord_500570 prefixEnd_500570 257033011221211751272927 := by
  unfold tailWord_500570
  simp only [CollatzResearch.WordTrace]
  refine ⟨4564321949131963848714791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12171525197685236929906109 4564321949131963848714791)
  ·
    refine ⟨6846482923697945773072187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4564321949131963848714791 6846482923697945773072187)
    ·
      refine ⟨10269724385546918659608281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6846482923697945773072187 10269724385546918659608281)
      ·
        refine ⟨7702293289160188994706211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10269724385546918659608281 7702293289160188994706211)
        ·
          refine ⟨11553439933740283492059317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7702293289160188994706211 11553439933740283492059317)
          ·
            refine ⟨1083134993788151577380561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11553439933740283492059317 1083134993788151577380561)
            ·
              refine ⟨812351245341113683035421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1083134993788151577380561 812351245341113683035421)
              ·
                refine ⟨304631717002917631138283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 812351245341113683035421 304631717002917631138283)
                ·
                  refine ⟨456947575504376446707425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 304631717002917631138283 456947575504376446707425)
                  ·
                    refine ⟨342710681628282335030569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 456947575504376446707425 342710681628282335030569)
                    ·
                      refine ⟨257033011221211751272927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 342710681628282335030569 257033011221211751272927)
                      ·
                        rfl

theorem cell23_500570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 2, 3, 1, 2, 2].length) (baseStart_500570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_500570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_500570 prefixEnd_500570 := by exact prefixLift 500570
  have htrace : WordTrace (prefixWord ++ tailWord_500570) baseStart_500570 baseEnd_500570 := by
    simpa [prefixWord, tailWord_500570, baseEnd_500570] using wordTrace_append hprefix tailTrace_500570
  have hstable : (prefixWord ++ tailWord_500570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500570).length < 2 ^ (prefixWord ++ tailWord_500570).sum := by decide
  have hdescent : baseEnd_500570 < baseStart_500570 := by decide
  rcases family_descends (prefixWord ++ tailWord_500570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500592 : List Nat := [2, 1, 1, 1, 4, 1, 2, 1, 1, 5, 4]
def baseStart_500592 : Nat := 118140960795 + 500592 * 2 ^ 59
def prefixEnd_500592 : Nat := 4983230072969 + 3 ^ 40 * 500592 * 2
def baseEnd_500592 : Nat := 257044307795610665197825

theorem tailTrace_500592 : CollatzResearch.WordTrace tailWord_500592 prefixEnd_500592 257044307795610665197825 := by
  unfold tailWord_500592
  simp only [CollatzResearch.WordTrace]
  refine ⟨9129045101224076576080015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12172060134965435434773353 9129045101224076576080015)
  ·
    refine ⟨13693567651836114864120023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9129045101224076576080015 13693567651836114864120023)
    ·
      refine ⟨20540351477754172296180035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13693567651836114864120023 20540351477754172296180035)
      ·
        refine ⟨30810527216631258444270053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20540351477754172296180035 30810527216631258444270053)
        ·
          refine ⟨5776973853118360958300635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30810527216631258444270053 5776973853118360958300635)
          ·
            refine ⟨8665460779677541437450953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5776973853118360958300635 8665460779677541437450953)
            ·
              refine ⟨6499095584758156078088215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8665460779677541437450953 6499095584758156078088215)
              ·
                refine ⟨9748643377137234117132323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6499095584758156078088215 9748643377137234117132323)
                ·
                  refine ⟨14622965065705851175698485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9748643377137234117132323 14622965065705851175698485)
                  ·
                    refine ⟨1370902974909923547721733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14622965065705851175698485 1370902974909923547721733)
                    ·
                      refine ⟨257044307795610665197825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1370902974909923547721733 257044307795610665197825)
                      ·
                        rfl

theorem cell23_500592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 1, 5, 4].length) (baseStart_500592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_500592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_500592 prefixEnd_500592 := by exact prefixLift 500592
  have htrace : WordTrace (prefixWord ++ tailWord_500592) baseStart_500592 baseEnd_500592 := by
    simpa [prefixWord, tailWord_500592, baseEnd_500592] using wordTrace_append hprefix tailTrace_500592
  have hstable : (prefixWord ++ tailWord_500592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500592).length < 2 ^ (prefixWord ++ tailWord_500592).sum := by decide
  have hdescent : baseEnd_500592 < baseStart_500592 := by decide
  rcases family_descends (prefixWord ++ tailWord_500592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500610 : List Nat := [3, 4, 2, 2, 1, 2, 2, 7]
def baseStart_500610 : Nat := 118140960795 + 500610 * 2 ^ 59
def prefixEnd_500610 : Nat := 4983230072969 + 3 ^ 40 * 500610 * 2
def baseEnd_500610 : Nat := 9520501868421910917509

theorem tailTrace_500610 : CollatzResearch.WordTrace tailWord_500610 prefixEnd_500610 9520501868421910917509 := by
  unfold tailWord_500610
  simp only [CollatzResearch.WordTrace]
  refine ⟨4564686679095735556578821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12172497810921961484210189 4564686679095735556578821)
  ·
    refine ⟨855878752330450416858529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4564686679095735556578821 855878752330450416858529)
    ·
      refine ⟨641909064247837812643897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 855878752330450416858529 641909064247837812643897)
      ·
        refine ⟨481431798185878359482923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 641909064247837812643897 481431798185878359482923)
        ·
          refine ⟨722147697278817539224385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 481431798185878359482923 722147697278817539224385)
          ·
            refine ⟨541610772959113154418289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 722147697278817539224385 541610772959113154418289)
            ·
              refine ⟨406208079719334865813717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 541610772959113154418289 406208079719334865813717)
              ·
                refine ⟨9520501868421910917509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 406208079719334865813717 9520501868421910917509)
                ·
                  rfl

theorem cell23_500610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 2, 7].length) (baseStart_500610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_500610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_500610 prefixEnd_500610 := by exact prefixLift 500610
  have htrace : WordTrace (prefixWord ++ tailWord_500610) baseStart_500610 baseEnd_500610 := by
    simpa [prefixWord, tailWord_500610, baseEnd_500610] using wordTrace_append hprefix tailTrace_500610
  have hstable : (prefixWord ++ tailWord_500610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500610).length < 2 ^ (prefixWord ++ tailWord_500610).sum := by decide
  have hdescent : baseEnd_500610 < baseStart_500610 := by decide
  rcases family_descends (prefixWord ++ tailWord_500610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500613 : List Nat := [1, 3, 1, 1, 3, 4, 2, 2, 1, 3, 2]
def baseStart_500613 : Nat := 118140960795 + 500613 * 2 ^ 59
def prefixEnd_500613 : Nat := 4983230072969 + 3 ^ 40 * 500613 * 2
def baseEnd_500613 : Nat := 257055090889355083035229

theorem tailTrace_500613 : CollatzResearch.WordTrace tailWord_500613 prefixEnd_500613 257055090889355083035229 := by
  unfold tailWord_500613
  simp only [CollatzResearch.WordTrace]
  refine ⟨18258856135372073738674493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12172570756914715825782995 18258856135372073738674493)
  ·
    refine ⟨6847071050764527652002935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18258856135372073738674493 6847071050764527652002935)
    ·
      refine ⟨10270606576146791478004403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6847071050764527652002935 10270606576146791478004403)
      ·
        refine ⟨15405909864220187217006605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10270606576146791478004403 15405909864220187217006605)
        ·
          refine ⟨5777216199082570206377477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15405909864220187217006605 5777216199082570206377477)
          ·
            refine ⟨1083228037327981913695777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5777216199082570206377477 1083228037327981913695777)
            ·
              refine ⟨812421027995986435271833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1083228037327981913695777 812421027995986435271833)
              ·
                refine ⟨609315770996989826453875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 812421027995986435271833 609315770996989826453875)
                ·
                  refine ⟨913973656495484739680813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 609315770996989826453875 913973656495484739680813)
                  ·
                    refine ⟨342740121185806777380305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 913973656495484739680813 342740121185806777380305)
                    ·
                      refine ⟨257055090889355083035229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 342740121185806777380305 257055090889355083035229)
                      ·
                        rfl

theorem cell23_500613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 2, 2, 1, 3, 2].length) (baseStart_500613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_500613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_500613 prefixEnd_500613 := by exact prefixLift 500613
  have htrace : WordTrace (prefixWord ++ tailWord_500613) baseStart_500613 baseEnd_500613 := by
    simpa [prefixWord, tailWord_500613, baseEnd_500613] using wordTrace_append hprefix tailTrace_500613
  have hstable : (prefixWord ++ tailWord_500613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500613).length < 2 ^ (prefixWord ++ tailWord_500613).sum := by decide
  have hdescent : baseEnd_500613 < baseStart_500613 := by decide
  rcases family_descends (prefixWord ++ tailWord_500613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500629 : List Nat := [1, 3, 2, 1, 1, 5, 1, 1, 2, 1, 5]
def baseStart_500629 : Nat := 118140960795 + 500629 * 2 ^ 59
def prefixEnd_500629 : Nat := 4983230072969 + 3 ^ 40 * 500629 * 2
def baseEnd_500629 : Nat := 257063306579827020435155

theorem tailTrace_500629 : CollatzResearch.WordTrace tailWord_500629 prefixEnd_500629 257063306579827020435155 := by
  unfold tailWord_500629
  simp only [CollatzResearch.WordTrace]
  refine ⟨18259439703314108471256941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12172959802209405647504627 18259439703314108471256941)
  ·
    refine ⟨6847289888742790676721353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18259439703314108471256941 6847289888742790676721353)
    ·
      refine ⟨5135467416557093007541015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6847289888742790676721353 5135467416557093007541015)
      ·
        refine ⟨7703201124835639511311523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5135467416557093007541015 7703201124835639511311523)
        ·
          refine ⟨11554801687253459266967285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7703201124835639511311523 11554801687253459266967285)
          ·
            refine ⟨1083262658180011806278183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11554801687253459266967285 1083262658180011806278183)
            ·
              refine ⟨1624893987270017709417275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1083262658180011806278183 1624893987270017709417275)
              ·
                refine ⟨2437340980905026564125913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1624893987270017709417275 2437340980905026564125913)
                ·
                  refine ⟨1828005735678769923094435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2437340980905026564125913 1828005735678769923094435)
                  ·
                    refine ⟨2742008603518154884641653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1828005735678769923094435 2742008603518154884641653)
                    ·
                      refine ⟨257063306579827020435155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2742008603518154884641653 257063306579827020435155)
                      ·
                        rfl

theorem cell23_500629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 1, 2, 1, 5].length) (baseStart_500629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_500629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_500629 prefixEnd_500629 := by exact prefixLift 500629
  have htrace : WordTrace (prefixWord ++ tailWord_500629) baseStart_500629 baseEnd_500629 := by
    simpa [prefixWord, tailWord_500629, baseEnd_500629] using wordTrace_append hprefix tailTrace_500629
  have hstable : (prefixWord ++ tailWord_500629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500629).length < 2 ^ (prefixWord ++ tailWord_500629).sum := by decide
  have hdescent : baseEnd_500629 < baseStart_500629 := by decide
  rcases family_descends (prefixWord ++ tailWord_500629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500679 : List Nat := [1, 1, 4, 1, 1, 2, 3, 3, 2, 5]
def baseStart_500679 : Nat := 118140960795 + 500679 * 2 ^ 59
def prefixEnd_500679 : Nat := 4983230072969 + 3 ^ 40 * 500679 * 2
def baseEnd_500679 : Nat := 85696326870850608269975

theorem tailTrace_500679 : CollatzResearch.WordTrace tailWord_500679 prefixEnd_500679 85696326870850608269975 := by
  unfold tailWord_500679
  simp only [CollatzResearch.WordTrace]
  refine ⟨18261263353132967010577091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12174175568755311340384727 18261263353132967010577091)
  ·
    refine ⟨27391895029699450515865637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18261263353132967010577091 27391895029699450515865637)
    ·
      refine ⟨5135980318068646971724807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27391895029699450515865637 5135980318068646971724807)
      ·
        refine ⟨7703970477102970457587211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5135980318068646971724807 7703970477102970457587211)
        ·
          refine ⟨11555955715654455686380817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7703970477102970457587211 11555955715654455686380817)
          ·
            refine ⟨8666966786740841764785613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11555955715654455686380817 8666966786740841764785613)
            ·
              refine ⟨3250112545027815661794605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8666966786740841764785613 3250112545027815661794605)
              ·
                refine ⟨1218792204385430873172977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3250112545027815661794605 1218792204385430873172977)
                ·
                  refine ⟨914094153289073154879733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1218792204385430873172977 914094153289073154879733)
                  ·
                    refine ⟨85696326870850608269975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 914094153289073154879733 85696326870850608269975)
                    ·
                      rfl

theorem cell23_500679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 3, 2, 5].length) (baseStart_500679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_500679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_500679 prefixEnd_500679 := by exact prefixLift 500679
  have htrace : WordTrace (prefixWord ++ tailWord_500679) baseStart_500679 baseEnd_500679 := by
    simpa [prefixWord, tailWord_500679, baseEnd_500679] using wordTrace_append hprefix tailTrace_500679
  have hstable : (prefixWord ++ tailWord_500679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500679).length < 2 ^ (prefixWord ++ tailWord_500679).sum := by decide
  have hdescent : baseEnd_500679 < baseStart_500679 := by decide
  rcases family_descends (prefixWord ++ tailWord_500679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500793 : List Nat := [1, 2, 1, 5, 2, 1, 2, 1, 1, 5, 2]
def baseStart_500793 : Nat := 118140960795 + 500793 * 2 ^ 59
def prefixEnd_500793 : Nat := 4983230072969 + 3 ^ 40 * 500793 * 2
def baseEnd_500793 : Nat := 257147517407164378784401

theorem tailTrace_500793 : CollatzResearch.WordTrace tailWord_500793 prefixEnd_500793 257147517407164378784401 := by
  unfold tailWord_500793
  simp only [CollatzResearch.WordTrace]
  refine ⟨18265421274719964480227033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12176947516479976320151355 18265421274719964480227033)
  ·
    refine ⟨13699065956039973360170275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18265421274719964480227033 13699065956039973360170275)
    ·
      refine ⟨20548598934059960040255413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13699065956039973360170275 20548598934059960040255413)
      ·
        refine ⟨1926431150068121253773945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20548598934059960040255413 1926431150068121253773945)
        ·
          refine ⟨1444823362551090940330459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1926431150068121253773945 1444823362551090940330459)
          ·
            refine ⟨2167235043826636410495689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1444823362551090940330459 2167235043826636410495689)
            ·
              refine ⟨1625426282869977307871767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2167235043826636410495689 1625426282869977307871767)
              ·
                refine ⟨2438139424304965961807651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1625426282869977307871767 2438139424304965961807651)
                ·
                  refine ⟨3657209136457448942711477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2438139424304965961807651 3657209136457448942711477)
                  ·
                    refine ⟨342863356542885838379201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3657209136457448942711477 342863356542885838379201)
                    ·
                      refine ⟨257147517407164378784401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 342863356542885838379201 257147517407164378784401)
                      ·
                        rfl

theorem cell23_500793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 1, 1, 5, 2].length) (baseStart_500793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_500793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_500793 prefixEnd_500793 := by exact prefixLift 500793
  have htrace : WordTrace (prefixWord ++ tailWord_500793) baseStart_500793 baseEnd_500793 := by
    simpa [prefixWord, tailWord_500793, baseEnd_500793] using wordTrace_append hprefix tailTrace_500793
  have hstable : (prefixWord ++ tailWord_500793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500793).length < 2 ^ (prefixWord ++ tailWord_500793).sum := by decide
  have hdescent : baseEnd_500793 < baseStart_500793 := by decide
  rcases family_descends (prefixWord ++ tailWord_500793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500799 : List Nat := [1, 1, 2, 2, 3, 1, 1, 3, 3, 6]
def baseStart_500799 : Nat := 118140960795 + 500799 * 2 ^ 59
def prefixEnd_500799 : Nat := 4983230072969 + 3 ^ 40 * 500799 * 2
def baseEnd_500799 : Nat := 85716866097030451769791

theorem tailTrace_500799 : CollatzResearch.WordTrace tailWord_500799 prefixEnd_500799 85716866097030451769791 := by
  unfold tailWord_500799
  simp only [CollatzResearch.WordTrace]
  refine ⟨18265640112698227504945451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12177093408465485003296967 18265640112698227504945451)
  ·
    refine ⟨27398460169047341257418177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18265640112698227504945451 27398460169047341257418177)
    ·
      refine ⟨20548845126785505943063633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27398460169047341257418177 20548845126785505943063633)
      ·
        refine ⟨15411633845089129457297725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20548845126785505943063633 15411633845089129457297725)
        ·
          refine ⟨5779362691908423546486647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15411633845089129457297725 5779362691908423546486647)
          ·
            refine ⟨8669044037862635319729971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5779362691908423546486647 8669044037862635319729971)
            ·
              refine ⟨13003566056793952979594957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8669044037862635319729971 13003566056793952979594957)
              ·
                refine ⟨4876337271297732367348109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13003566056793952979594957 4876337271297732367348109)
                ·
                  refine ⟨1828626476736649637755541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4876337271297732367348109 1828626476736649637755541)
                  ·
                    refine ⟨85716866097030451769791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1828626476736649637755541 85716866097030451769791)
                    ·
                      rfl

theorem cell23_500799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 3, 3, 6].length) (baseStart_500799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_500799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_500799 prefixEnd_500799 := by exact prefixLift 500799
  have htrace : WordTrace (prefixWord ++ tailWord_500799) baseStart_500799 baseEnd_500799 := by
    simpa [prefixWord, tailWord_500799, baseEnd_500799] using wordTrace_append hprefix tailTrace_500799
  have hstable : (prefixWord ++ tailWord_500799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500799).length < 2 ^ (prefixWord ++ tailWord_500799).sum := by decide
  have hdescent : baseEnd_500799 < baseStart_500799 := by decide
  rcases family_descends (prefixWord ++ tailWord_500799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500819 : List Nat := [1, 1, 1, 2, 1, 1, 2, 6, 1, 1, 6]
def baseStart_500819 : Nat := 118140960795 + 500819 * 2 ^ 59
def prefixEnd_500819 : Nat := 4983230072969 + 3 ^ 40 * 500819 * 2
def baseEnd_500819 : Nat := 257160867904181277059281

theorem tailTrace_500819 : CollatzResearch.WordTrace tailWord_500819 prefixEnd_500819 257160867904181277059281 := by
  unfold tailWord_500819
  simp only [CollatzResearch.WordTrace]
  refine ⟨18266369572625770920673511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12177579715083847280449007 18266369572625770920673511)
  ·
    refine ⟨27399554358938656381010267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18266369572625770920673511 27399554358938656381010267)
    ·
      refine ⟨41099331538407984571515401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27399554358938656381010267 41099331538407984571515401)
      ·
        refine ⟨30824498653805988428636551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41099331538407984571515401 30824498653805988428636551)
        ·
          refine ⟨46236747980708982642954827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30824498653805988428636551 46236747980708982642954827)
          ·
            refine ⟨69355121971063473964432241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46236747980708982642954827 69355121971063473964432241)
            ·
              refine ⟨52016341478297605473324181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69355121971063473964432241 52016341478297605473324181)
              ·
                refine ⟨2438266006795200256562071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 52016341478297605473324181 2438266006795200256562071)
                ·
                  refine ⟨3657399010192800384843107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2438266006795200256562071 3657399010192800384843107)
                  ·
                    refine ⟨5486098515289200577264661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3657399010192800384843107 5486098515289200577264661)
                    ·
                      refine ⟨257160867904181277059281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5486098515289200577264661 257160867904181277059281)
                      ·
                        rfl

theorem cell23_500819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 6, 1, 1, 6].length) (baseStart_500819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_500819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_500819 prefixEnd_500819 := by exact prefixLift 500819
  have htrace : WordTrace (prefixWord ++ tailWord_500819) baseStart_500819 baseEnd_500819 := by
    simpa [prefixWord, tailWord_500819, baseEnd_500819] using wordTrace_append hprefix tailTrace_500819
  have hstable : (prefixWord ++ tailWord_500819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500819).length < 2 ^ (prefixWord ++ tailWord_500819).sum := by decide
  have hdescent : baseEnd_500819 < baseStart_500819 := by decide
  rcases family_descends (prefixWord ++ tailWord_500819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500836 : List Nat := [2, 3, 1, 1, 2, 1, 1, 5, 1, 2, 4]
def baseStart_500836 : Nat := 118140960795 + 500836 * 2 ^ 59
def prefixEnd_500836 : Nat := 4983230072969 + 3 ^ 40 * 500836 * 2
def baseEnd_500836 : Nat := 257169597075307710546703

theorem tailTrace_500836 : CollatzResearch.WordTrace tailWord_500836 prefixEnd_500836 257169597075307710546703 := by
  unfold tailWord_500836
  simp only [CollatzResearch.WordTrace]
  refine ⟨9133494806782091412021181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12177993075709455216028241 9133494806782091412021181)
  ·
    refine ⟨3425060552543284279507943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9133494806782091412021181 3425060552543284279507943)
    ·
      refine ⟨5137590828814926419261915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3425060552543284279507943 5137590828814926419261915)
      ·
        refine ⟨7706386243222389628892873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5137590828814926419261915 7706386243222389628892873)
        ·
          refine ⟨5779789682416792221669655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7706386243222389628892873 5779789682416792221669655)
          ·
            refine ⟨8669684523625188332504483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5779789682416792221669655 8669684523625188332504483)
            ·
              refine ⟨13004526785437782498756725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8669684523625188332504483 13004526785437782498756725)
              ·
                refine ⟨1219174386134792109258443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13004526785437782498756725 1219174386134792109258443)
                ·
                  refine ⟨1828761579202188163887665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1219174386134792109258443 1828761579202188163887665)
                  ·
                    refine ⟨1371571184401641122915749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1828761579202188163887665 1371571184401641122915749)
                    ·
                      refine ⟨257169597075307710546703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1371571184401641122915749 257169597075307710546703)
                      ·
                        rfl

theorem cell23_500836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 5, 1, 2, 4].length) (baseStart_500836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_500836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_500836 prefixEnd_500836 := by exact prefixLift 500836
  have htrace : WordTrace (prefixWord ++ tailWord_500836) baseStart_500836 baseEnd_500836 := by
    simpa [prefixWord, tailWord_500836, baseEnd_500836] using wordTrace_append hprefix tailTrace_500836
  have hstable : (prefixWord ++ tailWord_500836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500836).length < 2 ^ (prefixWord ++ tailWord_500836).sum := by decide
  have hdescent : baseEnd_500836 < baseStart_500836 := by decide
  rcases family_descends (prefixWord ++ tailWord_500836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500840 : List Nat := [2, 1, 4, 4, 1, 1, 1, 1, 3, 1, 4]
def baseStart_500840 : Nat := 118140960795 + 500840 * 2 ^ 59
def prefixEnd_500840 : Nat := 4983230072969 + 3 ^ 40 * 500840 * 2
def baseEnd_500840 : Nat := 257171650997925694896685

theorem tailTrace_500840 : CollatzResearch.WordTrace tailWord_500840 prefixEnd_500840 257171650997925694896685 := by
  unfold tailWord_500840
  simp only [CollatzResearch.WordTrace]
  refine ⟨9133567752774845753593987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12178090337033127671458649 9133567752774845753593987)
  ·
    refine ⟨13700351629162268630390981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9133567752774845753593987 13700351629162268630390981)
    ·
      refine ⟨2568815930467925368198309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13700351629162268630390981 2568815930467925368198309)
      ·
        refine ⟨481652986962736006537183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2568815930467925368198309 481652986962736006537183)
        ·
          refine ⟨722479480444104009805775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 481652986962736006537183 722479480444104009805775)
          ·
            refine ⟨1083719220666156014708663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 722479480444104009805775 1083719220666156014708663)
            ·
              refine ⟨1625578830999234022062995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1083719220666156014708663 1625578830999234022062995)
              ·
                refine ⟨2438368246498851033094493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1625578830999234022062995 2438368246498851033094493)
                ·
                  refine ⟨914388092437069137410435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2438368246498851033094493 914388092437069137410435)
                  ·
                    refine ⟨1371582138655603706115653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 914388092437069137410435 1371582138655603706115653)
                    ·
                      refine ⟨257171650997925694896685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1371582138655603706115653 257171650997925694896685)
                      ·
                        rfl

theorem cell23_500840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_500840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_500840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_500840 prefixEnd_500840 := by exact prefixLift 500840
  have htrace : WordTrace (prefixWord ++ tailWord_500840) baseStart_500840 baseEnd_500840 := by
    simpa [prefixWord, tailWord_500840, baseEnd_500840] using wordTrace_append hprefix tailTrace_500840
  have hstable : (prefixWord ++ tailWord_500840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500840).length < 2 ^ (prefixWord ++ tailWord_500840).sum := by decide
  have hdescent : baseEnd_500840 < baseStart_500840 := by decide
  rcases family_descends (prefixWord ++ tailWord_500840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500846 : List Nat := [4, 1, 2, 2, 1, 2, 2, 9]
def baseStart_500846 : Nat := 118140960795 + 500846 * 2 ^ 59
def prefixEnd_500846 : Nat := 4983230072969 + 3 ^ 40 * 500846 * 2
def baseEnd_500846 : Nat := 9524990069698247089691

theorem tailTrace_500846 : CollatzResearch.WordTrace tailWord_500846 prefixEnd_500846 9524990069698247089691 := by
  unfold tailWord_500846
  simp only [CollatzResearch.WordTrace]
  refine ⟨2283419292940994316488299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12178236229018636354604261 2283419292940994316488299)
  ·
    refine ⟨3425128939411491474732449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2283419292940994316488299 3425128939411491474732449)
    ·
      refine ⟨2568846704558618606049337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3425128939411491474732449 2568846704558618606049337)
      ·
        refine ⟨1926635028418963954537003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2568846704558618606049337 1926635028418963954537003)
        ·
          refine ⟨2889952542628445931805505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1926635028418963954537003 2889952542628445931805505)
          ·
            refine ⟨2167464406971334448854129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2889952542628445931805505 2167464406971334448854129)
            ·
              refine ⟨1625598305228500836640597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2167464406971334448854129 1625598305228500836640597)
              ·
                refine ⟨9524990069698247089691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1625598305228500836640597 9524990069698247089691)
                ·
                  rfl

theorem cell23_500846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 9].length) (baseStart_500846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_500846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_500846 prefixEnd_500846 := by exact prefixLift 500846
  have htrace : WordTrace (prefixWord ++ tailWord_500846) baseStart_500846 baseEnd_500846 := by
    simpa [prefixWord, tailWord_500846, baseEnd_500846] using wordTrace_append hprefix tailTrace_500846
  have hstable : (prefixWord ++ tailWord_500846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500846).length < 2 ^ (prefixWord ++ tailWord_500846).sum := by decide
  have hdescent : baseEnd_500846 < baseStart_500846 := by decide
  rcases family_descends (prefixWord ++ tailWord_500846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500856 : List Nat := [2, 1, 2, 1, 1, 1, 5, 1, 3, 3, 3]
def baseStart_500856 : Nat := 118140960795 + 500856 * 2 ^ 59
def prefixEnd_500856 : Nat := 4983230072969 + 3 ^ 40 * 500856 * 2
def baseEnd_500856 : Nat := 257179866688397632296611

theorem tailTrace_500856 : CollatzResearch.WordTrace tailWord_500856 prefixEnd_500856 257179866688397632296611 := by
  unfold tailWord_500856
  simp only [CollatzResearch.WordTrace]
  refine ⟨9133859536745863119885211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12178479382327817493180281 9133859536745863119885211)
  ·
    refine ⟨13700789305118794679827817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9133859536745863119885211 13700789305118794679827817)
    ·
      refine ⟨10275591978839096009870863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13700789305118794679827817 10275591978839096009870863)
      ·
        refine ⟨15413387968258644014806295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10275591978839096009870863 15413387968258644014806295)
        ·
          refine ⟨23120081952387966022209443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15413387968258644014806295 23120081952387966022209443)
          ·
            refine ⟨34680122928581949033314165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23120081952387966022209443 34680122928581949033314165)
            ·
              refine ⟨3251261524554557721873203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34680122928581949033314165 3251261524554557721873203)
              ·
                refine ⟨4876892286831836582809805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3251261524554557721873203 4876892286831836582809805)
                ·
                  refine ⟨1828834607561938718553677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4876892286831836582809805 1828834607561938718553677)
                  ·
                    refine ⟨685812977835727019457629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1828834607561938718553677 685812977835727019457629)
                    ·
                      refine ⟨257179866688397632296611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 685812977835727019457629 257179866688397632296611)
                      ·
                        rfl

theorem cell23_500856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 1, 3, 3, 3].length) (baseStart_500856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_500856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_500856 prefixEnd_500856 := by exact prefixLift 500856
  have htrace : WordTrace (prefixWord ++ tailWord_500856) baseStart_500856 baseEnd_500856 := by
    simpa [prefixWord, tailWord_500856, baseEnd_500856] using wordTrace_append hprefix tailTrace_500856
  have hstable : (prefixWord ++ tailWord_500856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500856).length < 2 ^ (prefixWord ++ tailWord_500856).sum := by decide
  have hdescent : baseEnd_500856 < baseStart_500856 := by decide
  rcases family_descends (prefixWord ++ tailWord_500856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500859 : List Nat := [1, 1, 1, 1, 1, 4, 1, 2, 4, 7]
def baseStart_500859 : Nat := 118140960795 + 500859 * 2 ^ 59
def prefixEnd_500859 : Nat := 4983230072969 + 3 ^ 40 * 500859 * 2
def baseEnd_500859 : Nat := 85727135710120373519699

theorem tailTrace_500859 : CollatzResearch.WordTrace tailWord_500859 prefixEnd_500859 85727135710120373519699 := by
  unfold tailWord_500859
  simp only [CollatzResearch.WordTrace]
  refine ⟨18267828492480857752129631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12178552328320571834753087 18267828492480857752129631)
  ·
    refine ⟨27401742738721286628194447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18267828492480857752129631 27401742738721286628194447)
    ·
      refine ⟨41102614108081929942291671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27401742738721286628194447 41102614108081929942291671)
      ·
        refine ⟨61653921162122894913437507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41102614108081929942291671 61653921162122894913437507)
        ·
          refine ⟨92480881743184342370156261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61653921162122894913437507 92480881743184342370156261)
          ·
            refine ⟨17340165326847064194404299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92480881743184342370156261 17340165326847064194404299)
            ·
              refine ⟨26010247990270596291606449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17340165326847064194404299 26010247990270596291606449)
              ·
                refine ⟨19507685992702947218704837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26010247990270596291606449 19507685992702947218704837)
                ·
                  refine ⟨3657691123631802603507157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19507685992702947218704837 3657691123631802603507157)
                  ·
                    refine ⟨85727135710120373519699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3657691123631802603507157 85727135710120373519699)
                    ·
                      rfl

theorem cell23_500859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 4, 7].length) (baseStart_500859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_500859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_500859 prefixEnd_500859 := by exact prefixLift 500859
  have htrace : WordTrace (prefixWord ++ tailWord_500859) baseStart_500859 baseEnd_500859 := by
    simpa [prefixWord, tailWord_500859, baseEnd_500859] using wordTrace_append hprefix tailTrace_500859
  have hstable : (prefixWord ++ tailWord_500859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500859).length < 2 ^ (prefixWord ++ tailWord_500859).sum := by decide
  have hdescent : baseEnd_500859 < baseStart_500859 := by decide
  rcases family_descends (prefixWord ++ tailWord_500859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500860 : List Nat := [2, 2, 2, 1, 1, 3, 5, 1, 1, 2, 3]
def baseStart_500860 : Nat := 118140960795 + 500860 * 2 ^ 59
def prefixEnd_500860 : Nat := 4983230072969 + 3 ^ 40 * 500860 * 2
def baseEnd_500860 : Nat := 257181920611015616646593

theorem tailTrace_500860 : CollatzResearch.WordTrace tailWord_500860 prefixEnd_500860 257181920611015616646593 := by
  unfold tailWord_500860
  simp only [CollatzResearch.WordTrace]
  refine ⟨9133932482738617461458017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12178576643651489948610689 9133932482738617461458017)
  ·
    refine ⟨6850449362053963096093513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9133932482738617461458017 6850449362053963096093513)
    ·
      refine ⟨5137837021540472322070135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6850449362053963096093513 5137837021540472322070135)
      ·
        refine ⟨7706755532310708483105203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5137837021540472322070135 7706755532310708483105203)
        ·
          refine ⟨11560133298466062724657805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7706755532310708483105203 11560133298466062724657805)
          ·
            refine ⟨4335049986924773521746677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11560133298466062724657805 4335049986924773521746677)
            ·
              refine ⟨406410936274197517663751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4335049986924773521746677 406410936274197517663751)
              ·
                refine ⟨609616404411296276495627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 406410936274197517663751 609616404411296276495627)
                ·
                  refine ⟨914424606616944414743441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 609616404411296276495627 914424606616944414743441)
                  ·
                    refine ⟨685818454962708311057581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 914424606616944414743441 685818454962708311057581)
                    ·
                      refine ⟨257181920611015616646593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 685818454962708311057581 257181920611015616646593)
                      ·
                        rfl

theorem cell23_500860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 5, 1, 1, 2, 3].length) (baseStart_500860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_500860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_500860 prefixEnd_500860 := by exact prefixLift 500860
  have htrace : WordTrace (prefixWord ++ tailWord_500860) baseStart_500860 baseEnd_500860 := by
    simpa [prefixWord, tailWord_500860, baseEnd_500860] using wordTrace_append hprefix tailTrace_500860
  have hstable : (prefixWord ++ tailWord_500860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500860).length < 2 ^ (prefixWord ++ tailWord_500860).sum := by decide
  have hdescent : baseEnd_500860 < baseStart_500860 := by decide
  rcases family_descends (prefixWord ++ tailWord_500860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500879 : List Nat := [1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 8]
def baseStart_500879 : Nat := 118140960795 + 500879 * 2 ^ 59
def prefixEnd_500879 : Nat := 4983230072969 + 3 ^ 40 * 500879 * 2
def baseEnd_500879 : Nat := 257191676743451042309005

theorem tailTrace_500879 : CollatzResearch.WordTrace tailWord_500879 prefixEnd_500879 257191676743451042309005 := by
  unfold tailWord_500879
  simp only [CollatzResearch.WordTrace]
  refine ⟨18268557952408401167857691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12179038634938934111905127 18268557952408401167857691)
  ·
    refine ⟨27402836928612601751786537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18268557952408401167857691 27402836928612601751786537)
    ·
      refine ⟨20552127696459451313839903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27402836928612601751786537 20552127696459451313839903)
      ·
        refine ⟨30828191544689176970759855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20552127696459451313839903 30828191544689176970759855)
        ·
          refine ⟨46242287317033765456139783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30828191544689176970759855 46242287317033765456139783)
          ·
            refine ⟨69363430975550648184209675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46242287317033765456139783 69363430975550648184209675)
            ·
              refine ⟨104045146463325972276314513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69363430975550648184209675 104045146463325972276314513)
              ·
                refine ⟨78033859847494479207235885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104045146463325972276314513 78033859847494479207235885)
                ·
                  refine ⟨29262697442810429702713457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78033859847494479207235885 29262697442810429702713457)
                  ·
                    refine ⟨21947023082107822277035093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29262697442810429702713457 21947023082107822277035093)
                    ·
                      refine ⟨257191676743451042309005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 21947023082107822277035093 257191676743451042309005)
                      ·
                        rfl

theorem cell23_500879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 8].length) (baseStart_500879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_500879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_500879 prefixEnd_500879 := by exact prefixLift 500879
  have htrace : WordTrace (prefixWord ++ tailWord_500879) baseStart_500879 baseEnd_500879 := by
    simpa [prefixWord, tailWord_500879, baseEnd_500879] using wordTrace_append hprefix tailTrace_500879
  have hstable : (prefixWord ++ tailWord_500879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500879).length < 2 ^ (prefixWord ++ tailWord_500879).sum := by decide
  have hdescent : baseEnd_500879 < baseStart_500879 := by decide
  rcases family_descends (prefixWord ++ tailWord_500879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500883 : List Nat := [1, 1, 1, 2, 1, 2, 5, 2, 3, 3, 2]
def baseStart_500883 : Nat := 118140960795 + 500883 * 2 ^ 59
def prefixEnd_500883 : Nat := 4983230072969 + 3 ^ 40 * 500883 * 2
def baseEnd_500883 : Nat := 257193730666069026658987

theorem tailTrace_500883 : CollatzResearch.WordTrace tailWord_500883 prefixEnd_500883 257193730666069026658987 := by
  unfold tailWord_500883
  simp only [CollatzResearch.WordTrace]
  refine ⟨18268703844393909851003303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12179135896262606567335535 18268703844393909851003303)
  ·
    refine ⟨27403055766590864776504955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18268703844393909851003303 27403055766590864776504955)
    ·
      refine ⟨41104583649886297164757433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27403055766590864776504955 41104583649886297164757433)
      ·
        refine ⟨30828437737414722873568075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41104583649886297164757433 30828437737414722873568075)
        ·
          refine ⟨46242656606122084310352113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30828437737414722873568075 46242656606122084310352113)
          ·
            refine ⟨34681992454591563232764085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46242656606122084310352113 34681992454591563232764085)
            ·
              refine ⟨3251436792617959053071633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34681992454591563232764085 3251436792617959053071633)
              ·
                refine ⟨2438577594463469289803725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3251436792617959053071633 2438577594463469289803725)
                ·
                  refine ⟨914466597923800983676397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2438577594463469289803725 914466597923800983676397)
                  ·
                    refine ⟨342924974221425368878649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 914466597923800983676397 342924974221425368878649)
                    ·
                      refine ⟨257193730666069026658987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 342924974221425368878649 257193730666069026658987)
                      ·
                        rfl

theorem cell23_500883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 2, 3, 3, 2].length) (baseStart_500883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_500883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_500883 prefixEnd_500883 := by exact prefixLift 500883
  have htrace : WordTrace (prefixWord ++ tailWord_500883) baseStart_500883 baseEnd_500883 := by
    simpa [prefixWord, tailWord_500883, baseEnd_500883] using wordTrace_append hprefix tailTrace_500883
  have hstable : (prefixWord ++ tailWord_500883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500883).length < 2 ^ (prefixWord ++ tailWord_500883).sum := by decide
  have hdescent : baseEnd_500883 < baseStart_500883 := by decide
  rcases family_descends (prefixWord ++ tailWord_500883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500890 : List Nat := [3, 1, 1, 5, 1, 2, 2, 1, 1, 3, 3]
def baseStart_500890 : Nat := 118140960795 + 500890 * 2 ^ 59
def prefixEnd_500890 : Nat := 4983230072969 + 3 ^ 40 * 500890 * 2
def baseEnd_500890 : Nat := 257197325030650499271455

theorem tailTrace_500890 : CollatzResearch.WordTrace tailWord_500890 prefixEnd_500890 257197325030650499271455 := by
  unfold tailWord_500890
  simp only [CollatzResearch.WordTrace]
  refine ⟨4567239788842137511627031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12179306103579033364338749 4567239788842137511627031)
  ·
    refine ⟨6850859683263206267440547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4567239788842137511627031 6850859683263206267440547)
    ·
      refine ⟨10276289524894809401160821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6850859683263206267440547 10276289524894809401160821)
      ·
        refine ⟨963402142958888381358827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10276289524894809401160821 963402142958888381358827)
        ·
          refine ⟨1445103214438332572038241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 963402142958888381358827 1445103214438332572038241)
          ·
            refine ⟨1083827410828749429028681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1445103214438332572038241 1083827410828749429028681)
            ·
              refine ⟨812870558121562071771511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1083827410828749429028681 812870558121562071771511)
              ·
                refine ⟨1219305837182343107657267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 812870558121562071771511 1219305837182343107657267)
                ·
                  refine ⟨1828958755773514661485901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1219305837182343107657267 1828958755773514661485901)
                  ·
                    refine ⟨685859533415067998057213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1828958755773514661485901 685859533415067998057213)
                    ·
                      refine ⟨257197325030650499271455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 685859533415067998057213 257197325030650499271455)
                      ·
                        rfl

theorem cell23_500890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_500890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_500890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_500890 prefixEnd_500890 := by exact prefixLift 500890
  have htrace : WordTrace (prefixWord ++ tailWord_500890) baseStart_500890 baseEnd_500890 := by
    simpa [prefixWord, tailWord_500890, baseEnd_500890] using wordTrace_append hprefix tailTrace_500890
  have hstable : (prefixWord ++ tailWord_500890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500890).length < 2 ^ (prefixWord ++ tailWord_500890).sum := by decide
  have hdescent : baseEnd_500890 < baseStart_500890 := by decide
  rcases family_descends (prefixWord ++ tailWord_500890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500896 : List Nat := [2, 1, 1, 4, 2, 1, 1, 2, 2, 3, 4]
def baseStart_500896 : Nat := 118140960795 + 500896 * 2 ^ 59
def prefixEnd_500896 : Nat := 4983230072969 + 3 ^ 40 * 500896 * 2
def baseEnd_500896 : Nat := 257200405914577475796427

theorem tailTrace_500896 : CollatzResearch.WordTrace tailWord_500896 prefixEnd_500896 257200405914577475796427 := by
  unfold tailWord_500896
  simp only [CollatzResearch.WordTrace]
  refine ⟨9134588996673406535613271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12179451995564542047484361 9134588996673406535613271)
  ·
    refine ⟨13701883495010109803419907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9134588996673406535613271 13701883495010109803419907)
    ·
      refine ⟨20552825242515164705129861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13701883495010109803419907 20552825242515164705129861)
      ·
        refine ⟨3853654732971593382211849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20552825242515164705129861 3853654732971593382211849)
        ·
          refine ⟨2890241049728695036658887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3853654732971593382211849 2890241049728695036658887)
          ·
            refine ⟨4335361574593042554988331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2890241049728695036658887 4335361574593042554988331)
            ·
              refine ⟨6503042361889563832482497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4335361574593042554988331 6503042361889563832482497)
              ·
                refine ⟨4877281771417172874361873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6503042361889563832482497 4877281771417172874361873)
                ·
                  refine ⟨3657961328562879655771405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4877281771417172874361873 3657961328562879655771405)
                  ·
                    refine ⟨1371735498211079870914277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3657961328562879655771405 1371735498211079870914277)
                    ·
                      refine ⟨257200405914577475796427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1371735498211079870914277 257200405914577475796427)
                      ·
                        rfl

theorem cell23_500896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 2, 2, 3, 4].length) (baseStart_500896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_500896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_500896 prefixEnd_500896 := by exact prefixLift 500896
  have htrace : WordTrace (prefixWord ++ tailWord_500896) baseStart_500896 baseEnd_500896 := by
    simpa [prefixWord, tailWord_500896, baseEnd_500896] using wordTrace_append hprefix tailTrace_500896
  have hstable : (prefixWord ++ tailWord_500896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500896).length < 2 ^ (prefixWord ++ tailWord_500896).sum := by decide
  have hdescent : baseEnd_500896 < baseStart_500896 := by decide
  rcases family_descends (prefixWord ++ tailWord_500896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500900 : List Nat := [2, 3, 1, 2, 3, 1, 2, 1, 3, 3, 2]
def baseStart_500900 : Nat := 118140960795 + 500900 * 2 ^ 59
def prefixEnd_500900 : Nat := 4983230072969 + 3 ^ 40 * 500900 * 2
def baseEnd_500900 : Nat := 257202459837195460146409

theorem tailTrace_500900 : CollatzResearch.WordTrace tailWord_500900 prefixEnd_500900 257202459837195460146409 := by
  unfold tailWord_500900
  simp only [CollatzResearch.WordTrace]
  refine ⟨9134661942666160877186077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12179549256888214502914769 9134661942666160877186077)
  ·
    refine ⟨3425498228499810328944779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9134661942666160877186077 3425498228499810328944779)
    ·
      refine ⟨5138247342749715493417169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3425498228499810328944779 5138247342749715493417169)
      ·
        refine ⟨3853685507062286620062877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5138247342749715493417169 3853685507062286620062877)
        ·
          refine ⟨1445132065148357482523579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3853685507062286620062877 1445132065148357482523579)
          ·
            refine ⟨2167698097722536223785369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1445132065148357482523579 2167698097722536223785369)
            ·
              refine ⟨1625773573291902167839027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2167698097722536223785369 1625773573291902167839027)
              ·
                refine ⟨2438660359937853251758541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1625773573291902167839027 2438660359937853251758541)
                ·
                  refine ⟨914497634976694969409453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2438660359937853251758541 914497634976694969409453)
                  ·
                    refine ⟨342936613116260613528545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 914497634976694969409453 342936613116260613528545)
                    ·
                      refine ⟨257202459837195460146409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 342936613116260613528545 257202459837195460146409)
                      ·
                        rfl

theorem cell23_500900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 1, 3, 3, 2].length) (baseStart_500900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_500900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_500900 prefixEnd_500900 := by exact prefixLift 500900
  have htrace : WordTrace (prefixWord ++ tailWord_500900) baseStart_500900 baseEnd_500900 := by
    simpa [prefixWord, tailWord_500900, baseEnd_500900] using wordTrace_append hprefix tailTrace_500900
  have hstable : (prefixWord ++ tailWord_500900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500900).length < 2 ^ (prefixWord ++ tailWord_500900).sum := by decide
  have hdescent : baseEnd_500900 < baseStart_500900 := by decide
  rcases family_descends (prefixWord ++ tailWord_500900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500936 : List Nat := [2, 1, 3, 1, 2, 1, 3, 3, 7]
def baseStart_500936 : Nat := 118140960795 + 500936 * 2 ^ 59
def prefixEnd_500936 : Nat := 4983230072969 + 3 ^ 40 * 500936 * 2
def baseEnd_500936 : Nat := 28580105015639702144027

theorem tailTrace_500936 : CollatzResearch.WordTrace tailWord_500936 prefixEnd_500936 28580105015639702144027 := by
  unfold tailWord_500936
  simp only [CollatzResearch.WordTrace]
  refine ⟨9135318456600949951341331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12180424608801266601788441 9135318456600949951341331)
  ·
    refine ⟨13702977684901424927011997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9135318456600949951341331 13702977684901424927011997)
    ·
      refine ⟨5138616631838034347629499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13702977684901424927011997 5138616631838034347629499)
      ·
        refine ⟨7707924947757051521444249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5138616631838034347629499 7707924947757051521444249)
        ·
          refine ⟨5780943710817788641083187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7707924947757051521444249 5780943710817788641083187)
          ·
            refine ⟨8671415566226682961624781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5780943710817788641083187 8671415566226682961624781)
            ·
              refine ⟨3251780837335006110609293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8671415566226682961624781 3251780837335006110609293)
              ·
                refine ⟨1219417814000627291478485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3251780837335006110609293 1219417814000627291478485)
                ·
                  refine ⟨28580105015639702144027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1219417814000627291478485 28580105015639702144027)
                  ·
                    rfl

theorem cell23_500936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 3, 7].length) (baseStart_500936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_500936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_500936 prefixEnd_500936 := by exact prefixLift 500936
  have htrace : WordTrace (prefixWord ++ tailWord_500936) baseStart_500936 baseEnd_500936 := by
    simpa [prefixWord, tailWord_500936, baseEnd_500936] using wordTrace_append hprefix tailTrace_500936
  have hstable : (prefixWord ++ tailWord_500936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500936).length < 2 ^ (prefixWord ++ tailWord_500936).sum := by decide
  have hdescent : baseEnd_500936 < baseStart_500936 := by decide
  rcases family_descends (prefixWord ++ tailWord_500936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500941 : List Nat := [1, 6, 2, 2, 2, 1, 1, 1, 1, 3, 3]
def baseStart_500941 : Nat := 118140960795 + 500941 * 2 ^ 59
def prefixEnd_500941 : Nat := 4983230072969 + 3 ^ 40 * 500941 * 2
def baseEnd_500941 : Nat := 257223512544029799733721

theorem tailTrace_500941 : CollatzResearch.WordTrace tailWord_500941 prefixEnd_500941 257223512544029799733721 := by
  unfold tailWord_500941
  simp only [CollatzResearch.WordTrace]
  refine ⟨18270819278183785756614677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12180546185455857171076451 18270819278183785756614677)
  ·
    refine ⟨856444653664864957341313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 18270819278183785756614677 856444653664864957341313)
    ·
      refine ⟨642333490248648718005985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 856444653664864957341313 642333490248648718005985)
      ·
        refine ⟨481750117686486538504489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 642333490248648718005985 481750117686486538504489)
        ·
          refine ⟨361312588264864903878367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 481750117686486538504489 361312588264864903878367)
          ·
            refine ⟨541968882397297355817551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 361312588264864903878367 541968882397297355817551)
            ·
              refine ⟨812953323595946033726327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 541968882397297355817551 812953323595946033726327)
              ·
                refine ⟨1219429985393919050589491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 812953323595946033726327 1219429985393919050589491)
                ·
                  refine ⟨1829144978090878575884237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1219429985393919050589491 1829144978090878575884237)
                  ·
                    refine ⟨685929366784079465956589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1829144978090878575884237 685929366784079465956589)
                    ·
                      refine ⟨257223512544029799733721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 685929366784079465956589 257223512544029799733721)
                      ·
                        rfl

theorem cell23_500941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_500941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_500941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_500941 prefixEnd_500941 := by exact prefixLift 500941
  have htrace : WordTrace (prefixWord ++ tailWord_500941) baseStart_500941 baseEnd_500941 := by
    simpa [prefixWord, tailWord_500941, baseEnd_500941] using wordTrace_append hprefix tailTrace_500941
  have hstable : (prefixWord ++ tailWord_500941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500941).length < 2 ^ (prefixWord ++ tailWord_500941).sum := by decide
  have hdescent : baseEnd_500941 < baseStart_500941 := by decide
  rcases family_descends (prefixWord ++ tailWord_500941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500970 : List Nat := [3, 1, 3, 1, 1, 3, 3, 3, 5]
def baseStart_500970 : Nat := 118140960795 + 500970 * 2 ^ 59
def prefixEnd_500970 : Nat := 4983230072969 + 3 ^ 40 * 500970 * 2
def baseEnd_500970 : Nat := 28582044831445576252343

theorem tailTrace_500970 : CollatzResearch.WordTrace tailWord_500970 prefixEnd_500970 28582044831445576252343 := by
  unfold tailWord_500970
  simp only [CollatzResearch.WordTrace]
  refine ⟨4567969248769680927355091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12181251330052482472946909 4567969248769680927355091)
  ·
    refine ⟨6851953873154521391032637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4567969248769680927355091 6851953873154521391032637)
    ·
      refine ⟨2569482702432945521637239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6851953873154521391032637 2569482702432945521637239)
      ·
        refine ⟨3854224053649418282455859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2569482702432945521637239 3854224053649418282455859)
        ·
          refine ⟨5781336080474127423683789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3854224053649418282455859 5781336080474127423683789)
          ·
            refine ⟨2168001030177797783881421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5781336080474127423683789 2168001030177797783881421)
            ·
              refine ⟨813000386316674168955533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2168001030177797783881421 813000386316674168955533)
              ·
                refine ⟨304875144868752813358325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 813000386316674168955533 304875144868752813358325)
                ·
                  refine ⟨28582044831445576252343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 304875144868752813358325 28582044831445576252343)
                  ·
                    rfl

theorem cell23_500970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 3, 3, 5].length) (baseStart_500970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_500970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_500970 prefixEnd_500970 := by exact prefixLift 500970
  have htrace : WordTrace (prefixWord ++ tailWord_500970) baseStart_500970 baseEnd_500970 := by
    simpa [prefixWord, tailWord_500970, baseEnd_500970] using wordTrace_append hprefix tailTrace_500970
  have hstable : (prefixWord ++ tailWord_500970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500970).length < 2 ^ (prefixWord ++ tailWord_500970).sum := by decide
  have hdescent : baseEnd_500970 < baseStart_500970 := by decide
  rcases family_descends (prefixWord ++ tailWord_500970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_500993 : List Nat := [1, 2, 4, 1, 1, 4, 1, 1, 1, 2, 5]
def baseStart_500993 : Nat := 118140960795 + 500993 * 2 ^ 59
def prefixEnd_500993 : Nat := 4983230072969 + 3 ^ 40 * 500993 * 2
def baseEnd_500993 : Nat := 257250213538063596283481

theorem tailTrace_500993 : CollatzResearch.WordTrace tailWord_500993 prefixEnd_500993 257250213538063596283481 := by
  unfold tailWord_500993
  simp only [CollatzResearch.WordTrace]
  refine ⟨18272715873995398637507633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12181810582663599091671755 18272715873995398637507633)
  ·
    refine ⟨13704536905496548978130725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18272715873995398637507633 13704536905496548978130725)
    ·
      refine ⟨2569600669780602933399511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13704536905496548978130725 2569600669780602933399511)
      ·
        refine ⟨3854401004670904400099267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2569600669780602933399511 3854401004670904400099267)
        ·
          refine ⟨5781601507006356600148901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3854401004670904400099267 5781601507006356600148901)
          ·
            refine ⟨1084050282563691862527919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5781601507006356600148901 1084050282563691862527919)
            ·
              refine ⟨1626075423845537793791879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1084050282563691862527919 1626075423845537793791879)
              ·
                refine ⟨2439113135768306690687819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1626075423845537793791879 2439113135768306690687819)
                ·
                  refine ⟨3658669703652460036031729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2439113135768306690687819 3658669703652460036031729)
                  ·
                    refine ⟨2744002277739345027023797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3658669703652460036031729 2744002277739345027023797)
                    ·
                      refine ⟨257250213538063596283481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2744002277739345027023797 257250213538063596283481)
                      ·
                        rfl

theorem cell23_500993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 1, 1, 2, 5].length) (baseStart_500993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_500993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_500993 prefixEnd_500993 := by exact prefixLift 500993
  have htrace : WordTrace (prefixWord ++ tailWord_500993) baseStart_500993 baseEnd_500993 := by
    simpa [prefixWord, tailWord_500993, baseEnd_500993] using wordTrace_append hprefix tailTrace_500993
  have hstable : (prefixWord ++ tailWord_500993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_500993).length < 2 ^ (prefixWord ++ tailWord_500993).sum := by decide
  have hdescent : baseEnd_500993 < baseStart_500993 := by decide
  rcases family_descends (prefixWord ++ tailWord_500993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501013 : List Nat := [1, 3, 2, 1, 2, 1, 1, 3, 5, 4]
def baseStart_501013 : Nat := 118140960795 + 501013 * 2 ^ 59
def prefixEnd_501013 : Nat := 4983230072969 + 3 ^ 40 * 501013 * 2
def baseEnd_501013 : Nat := 85753494383717839344463

theorem tailTrace_501013 : CollatzResearch.WordTrace tailWord_501013 prefixEnd_501013 85753494383717839344463 := by
  unfold tailWord_501013
  simp only [CollatzResearch.WordTrace]
  refine ⟨18273445333922942053235693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12182296889281961368823795 18273445333922942053235693)
  ·
    refine ⟨6852542000221103269963385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18273445333922942053235693 6852542000221103269963385)
    ·
      refine ⟨5139406500165827452472539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6852542000221103269963385 5139406500165827452472539)
      ·
        refine ⟨7709109750248741178708809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5139406500165827452472539 7709109750248741178708809)
        ·
          refine ⟨5781832312686555884031607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7709109750248741178708809 5781832312686555884031607)
          ·
            refine ⟨8672748469029833826047411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5781832312686555884031607 8672748469029833826047411)
            ·
              refine ⟨13009122703544750739071117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8672748469029833826047411 13009122703544750739071117)
              ·
                refine ⟨4878421013829281527151669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13009122703544750739071117 4878421013829281527151669)
                ·
                  refine ⟨457351970046495143170469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4878421013829281527151669 457351970046495143170469)
                  ·
                    refine ⟨85753494383717839344463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 457351970046495143170469 85753494383717839344463)
                    ·
                      rfl

theorem cell23_501013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 3, 5, 4].length) (baseStart_501013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_501013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_501013 prefixEnd_501013 := by exact prefixLift 501013
  have htrace : WordTrace (prefixWord ++ tailWord_501013) baseStart_501013 baseEnd_501013 := by
    simpa [prefixWord, tailWord_501013, baseEnd_501013] using wordTrace_append hprefix tailTrace_501013
  have hstable : (prefixWord ++ tailWord_501013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501013).length < 2 ^ (prefixWord ++ tailWord_501013).sum := by decide
  have hdescent : baseEnd_501013 < baseStart_501013 := by decide
  rcases family_descends (prefixWord ++ tailWord_501013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501037 : List Nat := [1, 5, 3, 1, 1, 1, 2, 2, 2, 1, 4]
def baseStart_501037 : Nat := 118140960795 + 501037 * 2 ^ 59
def prefixEnd_501037 : Nat := 4983230072969 + 3 ^ 40 * 501037 * 2
def baseEnd_501037 : Nat := 257272806686861424133279

theorem tailTrace_501037 : CollatzResearch.WordTrace tailWord_501037 prefixEnd_501037 257272806686861424133279 := by
  unfold tailWord_501037
  simp only [CollatzResearch.WordTrace]
  refine ⟨18274320685835994152109365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12182880457223996101406243 18274320685835994152109365)
  ·
    refine ⟨1713217564297124451760253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18274320685835994152109365 1713217564297124451760253)
    ·
      refine ⟨642456586611421669410095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1713217564297124451760253 642456586611421669410095)
      ·
        refine ⟨963684879917132504115143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 642456586611421669410095 963684879917132504115143)
        ·
          refine ⟨1445527319875698756172715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 963684879917132504115143 1445527319875698756172715)
          ·
            refine ⟨2168290979813548134259073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1445527319875698756172715 2168290979813548134259073)
            ·
              refine ⟨1626218234860161100694305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2168290979813548134259073 1626218234860161100694305)
              ·
                refine ⟨1219663676145120825520729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1626218234860161100694305 1219663676145120825520729)
                ·
                  refine ⟨914747757108840619140547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1219663676145120825520729 914747757108840619140547)
                  ·
                    refine ⟨1372121635663260928710821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 914747757108840619140547 1372121635663260928710821)
                    ·
                      refine ⟨257272806686861424133279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1372121635663260928710821 257272806686861424133279)
                      ·
                        rfl

theorem cell23_501037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_501037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_501037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_501037 prefixEnd_501037 := by exact prefixLift 501037
  have htrace : WordTrace (prefixWord ++ tailWord_501037) baseStart_501037 baseEnd_501037 := by
    simpa [prefixWord, tailWord_501037, baseEnd_501037] using wordTrace_append hprefix tailTrace_501037
  have hstable : (prefixWord ++ tailWord_501037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501037).length < 2 ^ (prefixWord ++ tailWord_501037).sum := by decide
  have hdescent : baseEnd_501037 < baseStart_501037 := by decide
  rcases family_descends (prefixWord ++ tailWord_501037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501043 : List Nat := [1, 1, 1, 2, 5, 2, 1, 4, 6]
def baseStart_501043 : Nat := 118140960795 + 501043 * 2 ^ 59
def prefixEnd_501043 : Nat := 4983230072969 + 3 ^ 40 * 501043 * 2
def baseEnd_501043 : Nat := 28586209730087600073139

theorem tailTrace_501043 : CollatzResearch.WordTrace tailWord_501043 prefixEnd_501043 28586209730087600073139 := by
  unfold tailWord_501043
  simp only [CollatzResearch.WordTrace]
  refine ⟨18274539523814257176827783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12183026349209504784551855 18274539523814257176827783)
  ·
    refine ⟨27411809285721385765241675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18274539523814257176827783 27411809285721385765241675)
    ·
      refine ⟨41117713928582078647862513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27411809285721385765241675 41117713928582078647862513)
      ·
        refine ⟨30838285446436558985896885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41117713928582078647862513 30838285446436558985896885)
        ·
          refine ⟨2891089260603427404927833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30838285446436558985896885 2891089260603427404927833)
          ·
            refine ⟨2168316945452570553695875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2891089260603427404927833 2168316945452570553695875)
            ·
              refine ⟨3252475418178855830543813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2168316945452570553695875 3252475418178855830543813)
              ·
                refine ⟨609839140908535468226965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3252475418178855830543813 609839140908535468226965)
                ·
                  refine ⟨28586209730087600073139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 609839140908535468226965 28586209730087600073139)
                  ·
                    rfl

theorem cell23_501043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 4, 6].length) (baseStart_501043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_501043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_501043 prefixEnd_501043 := by exact prefixLift 501043
  have htrace : WordTrace (prefixWord ++ tailWord_501043) baseStart_501043 baseEnd_501043 := by
    simpa [prefixWord, tailWord_501043, baseEnd_501043] using wordTrace_append hprefix tailTrace_501043
  have hstable : (prefixWord ++ tailWord_501043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501043).length < 2 ^ (prefixWord ++ tailWord_501043).sum := by decide
  have hdescent : baseEnd_501043 < baseStart_501043 := by decide
  rcases family_descends (prefixWord ++ tailWord_501043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501073 : List Nat := [1, 2, 2, 1, 4, 1, 1, 3, 3, 5]
def baseStart_501073 : Nat := 118140960795 + 501073 * 2 ^ 59
def prefixEnd_501073 : Nat := 4983230072969 + 3 ^ 40 * 501073 * 2
def baseEnd_501073 : Nat := 85763763996807761094371

theorem tailTrace_501073 : CollatzResearch.WordTrace tailWord_501073 prefixEnd_501073 85763763996807761094371 := by
  unfold tailWord_501073
  simp only [CollatzResearch.WordTrace]
  refine ⟨18275633713705572300419873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12183755809137048200279915 18275633713705572300419873)
  ·
    refine ⟨13706725285279179225314905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18275633713705572300419873 13706725285279179225314905)
    ·
      refine ⟨10280043963959384418986179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13706725285279179225314905 10280043963959384418986179)
      ·
        refine ⟨15420065945939076628479269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10280043963959384418986179 15420065945939076628479269)
        ·
          refine ⟨2891262364863576867839863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15420065945939076628479269 2891262364863576867839863)
          ·
            refine ⟨4336893547295365301759795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2891262364863576867839863 4336893547295365301759795)
            ·
              refine ⟨6505340320943047952639693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4336893547295365301759795 6505340320943047952639693)
              ·
                refine ⟨2439502620353642982239885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6505340320943047952639693 2439502620353642982239885)
                ·
                  refine ⟨914813482632616118339957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2439502620353642982239885 914813482632616118339957)
                  ·
                    refine ⟨85763763996807761094371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 914813482632616118339957 85763763996807761094371)
                    ·
                      rfl

theorem cell23_501073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 3, 3, 5].length) (baseStart_501073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_501073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_501073 prefixEnd_501073 := by exact prefixLift 501073
  have htrace : WordTrace (prefixWord ++ tailWord_501073) baseStart_501073 baseEnd_501073 := by
    simpa [prefixWord, tailWord_501073, baseEnd_501073] using wordTrace_append hprefix tailTrace_501073
  have hstable : (prefixWord ++ tailWord_501073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501073).length < 2 ^ (prefixWord ++ tailWord_501073).sum := by decide
  have hdescent : baseEnd_501073 < baseStart_501073 := by decide
  rcases family_descends (prefixWord ++ tailWord_501073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501080 : List Nat := [2, 1, 2, 2, 1, 1, 5, 1, 1, 5, 2]
def baseStart_501080 : Nat := 118140960795 + 501080 * 2 ^ 59
def prefixEnd_501080 : Nat := 4983230072969 + 3 ^ 40 * 501080 * 2
def baseEnd_501080 : Nat := 257294886355004755895581

theorem tailTrace_501080 : CollatzResearch.WordTrace tailWord_501080 prefixEnd_501080 257294886355004755895581 := by
  unfold tailWord_501080
  simp only [CollatzResearch.WordTrace]
  refine ⟨9137944512340106247962347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12183926016453474997283129 9137944512340106247962347)
  ·
    refine ⟨13706916768510159371943521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9137944512340106247962347 13706916768510159371943521)
    ·
      refine ⟨10280187576382619528957641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13706916768510159371943521 10280187576382619528957641)
      ·
        refine ⟨7710140682286964646718231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10280187576382619528957641 7710140682286964646718231)
        ·
          refine ⟨11565211023430446970077347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7710140682286964646718231 11565211023430446970077347)
          ·
            refine ⟨17347816535145670455116021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11565211023430446970077347 17347816535145670455116021)
            ·
              refine ⟨1626357800169906605167127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17347816535145670455116021 1626357800169906605167127)
              ·
                refine ⟨2439536700254859907750691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1626357800169906605167127 2439536700254859907750691)
                ·
                  refine ⟨3659305050382289861626037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2439536700254859907750691 3659305050382289861626037)
                  ·
                    refine ⟨343059848473339674527441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3659305050382289861626037 343059848473339674527441)
                    ·
                      refine ⟨257294886355004755895581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 343059848473339674527441 257294886355004755895581)
                      ·
                        rfl

theorem cell23_501080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 1, 1, 5, 2].length) (baseStart_501080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_501080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_501080 prefixEnd_501080 := by exact prefixLift 501080
  have htrace : WordTrace (prefixWord ++ tailWord_501080) baseStart_501080 baseEnd_501080 := by
    simpa [prefixWord, tailWord_501080, baseEnd_501080] using wordTrace_append hprefix tailTrace_501080
  have hstable : (prefixWord ++ tailWord_501080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501080).length < 2 ^ (prefixWord ++ tailWord_501080).sum := by decide
  have hdescent : baseEnd_501080 < baseStart_501080 := by decide
  rcases family_descends (prefixWord ++ tailWord_501080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501113 : List Nat := [1, 2, 1, 3, 2, 1, 3, 1, 3, 1, 5]
def baseStart_501113 : Nat := 118140960795 + 501113 * 2 ^ 59
def prefixEnd_501113 : Nat := 4983230072969 + 3 ^ 40 * 501113 * 2
def baseEnd_501113 : Nat := 257311831216603126782929

theorem tailTrace_501113 : CollatzResearch.WordTrace tailWord_501113 prefixEnd_501113 257311831216603126782929 := by
  unfold tailWord_501113
  simp only [CollatzResearch.WordTrace]
  refine ⟨18277092633560659131875993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12184728422373772754583995 18277092633560659131875993)
  ·
    refine ⟨13707819475170494348906995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18277092633560659131875993 13707819475170494348906995)
    ·
      refine ⟨20561729212755741523360493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13707819475170494348906995 20561729212755741523360493)
      ·
        refine ⟨7710648454783403071260185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20561729212755741523360493 7710648454783403071260185)
        ·
          refine ⟨5782986341087552303445139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7710648454783403071260185 5782986341087552303445139)
          ·
            refine ⟨8674479511631328455167709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5782986341087552303445139 8674479511631328455167709)
            ·
              refine ⟨3252929816861748170687891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8674479511631328455167709 3252929816861748170687891)
              ·
                refine ⟨4879394725292622256031837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3252929816861748170687891 4879394725292622256031837)
                ·
                  refine ⟨1829773021984733346011939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4879394725292622256031837 1829773021984733346011939)
                  ·
                    refine ⟨2744659532977100019017909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1829773021984733346011939 2744659532977100019017909)
                    ·
                      refine ⟨257311831216603126782929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2744659532977100019017909 257311831216603126782929)
                      ·
                        rfl

theorem cell23_501113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 1, 3, 1, 5].length) (baseStart_501113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_501113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_501113 prefixEnd_501113 := by exact prefixLift 501113
  have htrace : WordTrace (prefixWord ++ tailWord_501113) baseStart_501113 baseEnd_501113 := by
    simpa [prefixWord, tailWord_501113, baseEnd_501113] using wordTrace_append hprefix tailTrace_501113
  have hstable : (prefixWord ++ tailWord_501113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501113).length < 2 ^ (prefixWord ++ tailWord_501113).sum := by decide
  have hdescent : baseEnd_501113 < baseStart_501113 := by decide
  rcases family_descends (prefixWord ++ tailWord_501113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501120 : List Nat := [2, 1, 1, 2, 1, 2, 1, 7, 2, 4]
def baseStart_501120 : Nat := 118140960795 + 501120 * 2 ^ 59
def prefixEnd_501120 : Nat := 4983230072969 + 3 ^ 40 * 501120 * 2
def baseEnd_501120 : Nat := 85771808527061533131799

theorem tailTrace_501120 : CollatzResearch.WordTrace tailWord_501120 prefixEnd_501120 85771808527061533131799 := by
  unfold tailWord_501120
  simp only [CollatzResearch.WordTrace]
  refine ⟨9138673972267649663690407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12184898629690199551587209 9138673972267649663690407)
  ·
    refine ⟨13708010958401474495535611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9138673972267649663690407 13708010958401474495535611)
    ·
      refine ⟨20562016437602211743303417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13708010958401474495535611 20562016437602211743303417)
      ·
        refine ⟨15421512328201658807477563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20562016437602211743303417 15421512328201658807477563)
        ·
          refine ⟨23132268492302488211216345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15421512328201658807477563 23132268492302488211216345)
          ·
            refine ⟨17349201369226866158412259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23132268492302488211216345 17349201369226866158412259)
            ·
              refine ⟨26023802053840299237618389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17349201369226866158412259 26023802053840299237618389)
              ·
                refine ⟨609932860636882013381681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 26023802053840299237618389 609932860636882013381681)
                ·
                  refine ⟨457449645477661510036261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 609932860636882013381681 457449645477661510036261)
                  ·
                    refine ⟨85771808527061533131799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 457449645477661510036261 85771808527061533131799)
                    ·
                      rfl

theorem cell23_501120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 7, 2, 4].length) (baseStart_501120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_501120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_501120 prefixEnd_501120 := by exact prefixLift 501120
  have htrace : WordTrace (prefixWord ++ tailWord_501120) baseStart_501120 baseEnd_501120 := by
    simpa [prefixWord, tailWord_501120, baseEnd_501120] using wordTrace_append hprefix tailTrace_501120
  have hstable : (prefixWord ++ tailWord_501120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501120).length < 2 ^ (prefixWord ++ tailWord_501120).sum := by decide
  have hdescent : baseEnd_501120 < baseStart_501120 := by decide
  rcases family_descends (prefixWord ++ tailWord_501120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501127 : List Nat := [1, 1, 4, 2, 2, 3, 2, 2, 1, 1, 4]
def baseStart_501127 : Nat := 118140960795 + 501127 * 2 ^ 59
def prefixEnd_501127 : Nat := 4983230072969 + 3 ^ 40 * 501127 * 2
def baseEnd_501127 : Nat := 257319019945766072007865

theorem tailTrace_501127 : CollatzResearch.WordTrace tailWord_501127 prefixEnd_501127 257319019945766072007865 := by
  unfold tailWord_501127
  simp only [CollatzResearch.WordTrace]
  refine ⟨18277603255509939522885635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12185068837006626348590423 18277603255509939522885635)
  ·
    refine ⟨27416404883264909284328453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18277603255509939522885635 27416404883264909284328453)
    ·
      refine ⟨5140575915612170490811585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27416404883264909284328453 5140575915612170490811585)
      ·
        refine ⟨3855431936709127868108689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5140575915612170490811585 3855431936709127868108689)
        ·
          refine ⟨2891573952531845901081517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3855431936709127868108689 2891573952531845901081517)
          ·
            refine ⟨1084340232199442212905569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2891573952531845901081517 1084340232199442212905569)
            ·
              refine ⟨813255174149581659679177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1084340232199442212905569 813255174149581659679177)
              ·
                refine ⟨609941380612186244759383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 813255174149581659679177 609941380612186244759383)
                ·
                  refine ⟨914912070918279367139075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 609941380612186244759383 914912070918279367139075)
                  ·
                    refine ⟨1372368106377419050708613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 914912070918279367139075 1372368106377419050708613)
                    ·
                      refine ⟨257319019945766072007865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1372368106377419050708613 257319019945766072007865)
                      ·
                        rfl

theorem cell23_501127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 2, 2, 1, 1, 4].length) (baseStart_501127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_501127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_501127 prefixEnd_501127 := by exact prefixLift 501127
  have htrace : WordTrace (prefixWord ++ tailWord_501127) baseStart_501127 baseEnd_501127 := by
    simpa [prefixWord, tailWord_501127, baseEnd_501127] using wordTrace_append hprefix tailTrace_501127
  have hstable : (prefixWord ++ tailWord_501127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501127).length < 2 ^ (prefixWord ++ tailWord_501127).sum := by decide
  have hdescent : baseEnd_501127 < baseStart_501127 := by decide
  rcases family_descends (prefixWord ++ tailWord_501127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501193 : List Nat := [1, 2, 1, 1, 2, 1, 3, 2, 4, 6]
def baseStart_501193 : Nat := 118140960795 + 501193 * 2 ^ 59
def prefixEnd_501193 : Nat := 4983230072969 + 3 ^ 40 * 501193 * 2
def baseEnd_501193 : Nat := 85784303222987604594187

theorem tailTrace_501193 : CollatzResearch.WordTrace tailWord_501193 prefixEnd_501193 85784303222987604594187 := by
  unfold tailWord_501193
  simp only [CollatzResearch.WordTrace]
  refine ⟨18280010473270832794788233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12186673648847221863192155 18280010473270832794788233)
  ·
    refine ⟨13710007854953124596091175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18280010473270832794788233 13710007854953124596091175)
    ·
      refine ⟨20565011782429686894136763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13710007854953124596091175 20565011782429686894136763)
      ·
        refine ⟨30847517673644530341205145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20565011782429686894136763 30847517673644530341205145)
        ·
          refine ⟨23135638255233397755903859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30847517673644530341205145 23135638255233397755903859)
          ·
            refine ⟨34703457382850096633855789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23135638255233397755903859 34703457382850096633855789)
            ·
              refine ⟨13013796518568786237695921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34703457382850096633855789 13013796518568786237695921)
              ·
                refine ⟨9760347388926589678271941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13013796518568786237695921 9760347388926589678271941)
                ·
                  refine ⟨1830065135423735564675989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9760347388926589678271941 1830065135423735564675989)
                  ·
                    refine ⟨85784303222987604594187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1830065135423735564675989 85784303222987604594187)
                    ·
                      rfl

theorem cell23_501193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 2, 4, 6].length) (baseStart_501193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_501193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_501193 prefixEnd_501193 := by exact prefixLift 501193
  have htrace : WordTrace (prefixWord ++ tailWord_501193) baseStart_501193 baseEnd_501193 := by
    simpa [prefixWord, tailWord_501193, baseEnd_501193] using wordTrace_append hprefix tailTrace_501193
  have hstable : (prefixWord ++ tailWord_501193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501193).length < 2 ^ (prefixWord ++ tailWord_501193).sum := by decide
  have hdescent : baseEnd_501193 < baseStart_501193 := by decide
  rcases family_descends (prefixWord ++ tailWord_501193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501234 : List Nat := [3, 2, 1, 4, 1, 1, 1, 3, 1, 4, 2]
def baseStart_501234 : Nat := 118140960795 + 501234 * 2 ^ 59
def prefixEnd_501234 : Nat := 4983230072969 + 3 ^ 40 * 501234 * 2
def baseEnd_501234 : Nat := 257373962375797153369873

theorem tailTrace_501234 : CollatzResearch.WordTrace tailWord_501234 prefixEnd_501234 257373962375797153369873 := by
  unfold tailWord_501234
  simp only [CollatzResearch.WordTrace]
  refine ⟨4570376466530574199257689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12187670577414864531353837 4570376466530574199257689)
  ·
    refine ⟨3427782349897930649443267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4570376466530574199257689 3427782349897930649443267)
    ·
      refine ⟨5141673524846895974164901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3427782349897930649443267 5141673524846895974164901)
      ·
        refine ⟨964063785908792995155919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5141673524846895974164901 964063785908792995155919)
        ·
          refine ⟨1446095678863189492733879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 964063785908792995155919 1446095678863189492733879)
          ·
            refine ⟨2169143518294784239100819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1446095678863189492733879 2169143518294784239100819)
            ·
              refine ⟨3253715277442176358651229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2169143518294784239100819 3253715277442176358651229)
              ·
                refine ⟨1220143229040816134494211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3253715277442176358651229 1220143229040816134494211)
                ·
                  refine ⟨1830214843561224201741317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1220143229040816134494211 1830214843561224201741317)
                  ·
                    refine ⟨343165283167729537826497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1830214843561224201741317 343165283167729537826497)
                    ·
                      refine ⟨257373962375797153369873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 343165283167729537826497 257373962375797153369873)
                      ·
                        rfl

theorem cell23_501234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 3, 1, 4, 2].length) (baseStart_501234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_501234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_501234 prefixEnd_501234 := by exact prefixLift 501234
  have htrace : WordTrace (prefixWord ++ tailWord_501234) baseStart_501234 baseEnd_501234 := by
    simpa [prefixWord, tailWord_501234, baseEnd_501234] using wordTrace_append hprefix tailTrace_501234
  have hstable : (prefixWord ++ tailWord_501234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501234).length < 2 ^ (prefixWord ++ tailWord_501234).sum := by decide
  have hdescent : baseEnd_501234 < baseStart_501234 := by decide
  rcases family_descends (prefixWord ++ tailWord_501234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501240 : List Nat := [2, 1, 2, 1, 1, 6, 1, 2, 7]
def baseStart_501240 : Nat := 118140960795 + 501240 * 2 ^ 59
def prefixEnd_501240 : Nat := 4983230072969 + 3 ^ 40 * 501240 * 2
def baseEnd_501240 : Nat := 28597449251080458877205

theorem tailTrace_501240 : CollatzResearch.WordTrace tailWord_501240 prefixEnd_501240 28597449251080458877205 := by
  unfold tailWord_501240
  simp only [CollatzResearch.WordTrace]
  refine ⟨9140862352050279910874587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12187816469400373214499449 9140862352050279910874587)
  ·
    refine ⟨13711293528075419866311881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9140862352050279910874587 13711293528075419866311881)
    ·
      refine ⟨10283470146056564899733911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13711293528075419866311881 10283470146056564899733911)
      ·
        refine ⟨15425205219084847349600867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10283470146056564899733911 15425205219084847349600867)
        ·
          refine ⟨23137807828627271024401301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15425205219084847349600867 23137807828627271024401301)
          ·
            refine ⟨1084584741966903329268811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 23137807828627271024401301 1084584741966903329268811)
            ·
              refine ⟨1626877112950354993903217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1084584741966903329268811 1626877112950354993903217)
              ·
                refine ⟨1220157834712766245427413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1626877112950354993903217 1220157834712766245427413)
                ·
                  refine ⟨28597449251080458877205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1220157834712766245427413 28597449251080458877205)
                  ·
                    rfl

theorem cell23_501240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 2, 7].length) (baseStart_501240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_501240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_501240 prefixEnd_501240 := by exact prefixLift 501240
  have htrace : WordTrace (prefixWord ++ tailWord_501240) baseStart_501240 baseEnd_501240 := by
    simpa [prefixWord, tailWord_501240, baseEnd_501240] using wordTrace_append hprefix tailTrace_501240
  have hstable : (prefixWord ++ tailWord_501240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501240).length < 2 ^ (prefixWord ++ tailWord_501240).sum := by decide
  have hdescent : baseEnd_501240 < baseStart_501240 := by decide
  rcases family_descends (prefixWord ++ tailWord_501240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501243 : List Nat := [1, 1, 1, 1, 1, 3, 2, 2, 2, 1, 8]
def baseStart_501243 : Nat := 118140960795 + 501243 * 2 ^ 59
def prefixEnd_501243 : Nat := 4983230072969 + 3 ^ 40 * 501243 * 2
def baseEnd_501243 : Nat := 257378583701687618157331

theorem tailTrace_501243 : CollatzResearch.WordTrace tailWord_501243 prefixEnd_501243 257378583701687618157331 := by
  unfold tailWord_501243
  simp only [CollatzResearch.WordTrace]
  refine ⟨18281834123089691334108383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12187889415393127556072255 18281834123089691334108383)
  ·
    refine ⟨27422751184634537001162575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18281834123089691334108383 27422751184634537001162575)
    ·
      refine ⟨41134126776951805501743863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27422751184634537001162575 41134126776951805501743863)
      ·
        refine ⟨61701190165427708252615795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41134126776951805501743863 61701190165427708252615795)
        ·
          refine ⟨92551785248141562378923693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61701190165427708252615795 92551785248141562378923693)
          ·
            refine ⟨34706919468053085892096385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92551785248141562378923693 34706919468053085892096385)
            ·
              refine ⟨26030189601039814419072289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34706919468053085892096385 26030189601039814419072289)
              ·
                refine ⟨19522642200779860814304217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26030189601039814419072289 19522642200779860814304217)
                ·
                  refine ⟨14641981650584895610728163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19522642200779860814304217 14641981650584895610728163)
                  ·
                    refine ⟨21962972475877343416092245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14641981650584895610728163 21962972475877343416092245)
                    ·
                      refine ⟨257378583701687618157331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 21962972475877343416092245 257378583701687618157331)
                      ·
                        rfl

theorem cell23_501243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 2, 1, 8].length) (baseStart_501243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_501243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_501243 prefixEnd_501243 := by exact prefixLift 501243
  have htrace : WordTrace (prefixWord ++ tailWord_501243) baseStart_501243 baseEnd_501243 := by
    simpa [prefixWord, tailWord_501243, baseEnd_501243] using wordTrace_append hprefix tailTrace_501243
  have hstable : (prefixWord ++ tailWord_501243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501243).length < 2 ^ (prefixWord ++ tailWord_501243).sum := by decide
  have hdescent : baseEnd_501243 < baseStart_501243 := by decide
  rcases family_descends (prefixWord ++ tailWord_501243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501257 : List Nat := [1, 2, 1, 1, 3, 1, 6, 3, 5]
def baseStart_501257 : Nat := 118140960795 + 501257 * 2 ^ 59
def prefixEnd_501257 : Nat := 4983230072969 + 3 ^ 40 * 501257 * 2
def baseEnd_501257 : Nat := 28598419158983395931363

theorem tailTrace_501257 : CollatzResearch.WordTrace tailWord_501257 prefixEnd_501257 28598419158983395931363 := by
  unfold tailWord_501257
  simp only [CollatzResearch.WordTrace]
  refine ⟨18282344745038971725118025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12188229830025981150078683 18282344745038971725118025)
  ·
    refine ⟨13711758558779228793838519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18282344745038971725118025 13711758558779228793838519)
    ·
      refine ⟨20567637838168843190757779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13711758558779228793838519 20567637838168843190757779)
      ·
        refine ⟨30851456757253264786136669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20567637838168843190757779 30851456757253264786136669)
        ·
          refine ⟨11569296283969974294801251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30851456757253264786136669 11569296283969974294801251)
          ·
            refine ⟨17353944425954961442201877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11569296283969974294801251 17353944425954961442201877)
            ·
              refine ⟨813466144966638817603213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 17353944425954961442201877 813466144966638817603213)
              ·
                refine ⟨305049804362489556601205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 813466144966638817603213 305049804362489556601205)
                ·
                  refine ⟨28598419158983395931363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 305049804362489556601205 28598419158983395931363)
                  ·
                    rfl

theorem cell23_501257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 6, 3, 5].length) (baseStart_501257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_501257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_501257 prefixEnd_501257 := by exact prefixLift 501257
  have htrace : WordTrace (prefixWord ++ tailWord_501257) baseStart_501257 baseEnd_501257 := by
    simpa [prefixWord, tailWord_501257, baseEnd_501257] using wordTrace_append hprefix tailTrace_501257
  have hstable : (prefixWord ++ tailWord_501257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501257).length < 2 ^ (prefixWord ++ tailWord_501257).sum := by decide
  have hdescent : baseEnd_501257 < baseStart_501257 := by decide
  rcases family_descends (prefixWord ++ tailWord_501257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501268 : List Nat := [2, 4, 3, 1, 2, 1, 1, 1, 4, 2, 2]
def baseStart_501268 : Nat := 118140960795 + 501268 * 2 ^ 59
def prefixEnd_501268 : Nat := 4983230072969 + 3 ^ 40 * 501268 * 2
def baseEnd_501268 : Nat := 257391420718050020344717

theorem tailTrace_501268 : CollatzResearch.WordTrace tailWord_501268 prefixEnd_501268 257391420718050020344717 := by
  unfold tailWord_501268
  simp only [CollatzResearch.WordTrace]
  refine ⟨9141372973999560301884229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12188497298666080402512305 9141372973999560301884229)
  ·
    refine ⟨1714007432624917556603293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9141372973999560301884229 1714007432624917556603293)
    ·
      refine ⟨642752787234344083726235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1714007432624917556603293 642752787234344083726235)
      ·
        refine ⟨964129180851516125589353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 642752787234344083726235 964129180851516125589353)
        ·
          refine ⟨723096885638637094192015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 964129180851516125589353 723096885638637094192015)
          ·
            refine ⟨1084645328457955641288023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 723096885638637094192015 1084645328457955641288023)
            ·
              refine ⟨1626967992686933461932035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1084645328457955641288023 1626967992686933461932035)
              ·
                refine ⟨2440451989030400192898053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1626967992686933461932035 2440451989030400192898053)
                ·
                  refine ⟨457584747943200036168385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2440451989030400192898053 457584747943200036168385)
                  ·
                    refine ⟨343188560957400027126289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 457584747943200036168385 343188560957400027126289)
                    ·
                      refine ⟨257391420718050020344717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 343188560957400027126289 257391420718050020344717)
                      ·
                        rfl

theorem cell23_501268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 1, 4, 2, 2].length) (baseStart_501268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_501268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_501268 prefixEnd_501268 := by exact prefixLift 501268
  have htrace : WordTrace (prefixWord ++ tailWord_501268) baseStart_501268 baseEnd_501268 := by
    simpa [prefixWord, tailWord_501268, baseEnd_501268] using wordTrace_append hprefix tailTrace_501268
  have hstable : (prefixWord ++ tailWord_501268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501268).length < 2 ^ (prefixWord ++ tailWord_501268).sum := by decide
  have hdescent : baseEnd_501268 < baseStart_501268 := by decide
  rcases family_descends (prefixWord ++ tailWord_501268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501347 : List Nat := [1, 1, 1, 5, 1, 4, 1, 3, 6]
def baseStart_501347 : Nat := 118140960795 + 501347 * 2 ^ 59
def prefixEnd_501347 : Nat := 4983230072969 + 3 ^ 40 * 501347 * 2
def baseEnd_501347 : Nat := 28603553965528356806317

theorem tailTrace_501347 : CollatzResearch.WordTrace tailWord_501347 prefixEnd_501347 28603553965528356806317 := by
  unfold tailWord_501347
  simp only [CollatzResearch.WordTrace]
  refine ⟨18285627314712917095894295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12190418209808611397262863 18285627314712917095894295)
  ·
    refine ⟨27428440972069375643841443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18285627314712917095894295 27428440972069375643841443)
    ·
      refine ⟨41142661458104063465762165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27428440972069375643841443 41142661458104063465762165)
      ·
        refine ⟨3857124511697255949915203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41142661458104063465762165 3857124511697255949915203)
        ·
          refine ⟨5785686767545883924872805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3857124511697255949915203 5785686767545883924872805)
          ·
            refine ⟨1084816268914853235913651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5785686767545883924872805 1084816268914853235913651)
            ·
              refine ⟨1627224403372279853870477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1084816268914853235913651 1627224403372279853870477)
              ·
                refine ⟨610209151264604945201429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1627224403372279853870477 610209151264604945201429)
                ·
                  refine ⟨28603553965528356806317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 610209151264604945201429 28603553965528356806317)
                  ·
                    rfl

theorem cell23_501347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 3, 6].length) (baseStart_501347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_501347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_501347 prefixEnd_501347 := by exact prefixLift 501347
  have htrace : WordTrace (prefixWord ++ tailWord_501347) baseStart_501347 baseEnd_501347 := by
    simpa [prefixWord, tailWord_501347, baseEnd_501347] using wordTrace_append hprefix tailTrace_501347
  have hstable : (prefixWord ++ tailWord_501347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501347).length < 2 ^ (prefixWord ++ tailWord_501347).sum := by decide
  have hdescent : baseEnd_501347 < baseStart_501347 := by decide
  rcases family_descends (prefixWord ++ tailWord_501347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501370 : List Nat := [3, 1, 1, 1, 1, 1, 1, 3, 2, 4, 5]
def baseStart_501370 : Nat := 118140960795 + 501370 * 2 ^ 59
def prefixEnd_501370 : Nat := 4983230072969 + 3 ^ 40 * 501370 * 2
def baseEnd_501370 : Nat := 257443795744808621269247

theorem tailTrace_501370 : CollatzResearch.WordTrace tailWord_501370 prefixEnd_501370 257443795744808621269247 := by
  unfold tailWord_501370
  simp only [CollatzResearch.WordTrace]
  refine ⟨4571616548407398005995391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12190977462419728015987709 4571616548407398005995391)
  ·
    refine ⟨6857424822611097008993087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4571616548407398005995391 6857424822611097008993087)
    ·
      refine ⟨10286137233916645513489631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6857424822611097008993087 10286137233916645513489631)
      ·
        refine ⟨15429205850874968270234447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10286137233916645513489631 15429205850874968270234447)
        ·
          refine ⟨23143808776312452405351671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15429205850874968270234447 23143808776312452405351671)
          ·
            refine ⟨34715713164468678608027507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23143808776312452405351671 34715713164468678608027507)
            ·
              refine ⟨52073569746703017912041261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34715713164468678608027507 52073569746703017912041261)
              ·
                refine ⟨19527588655013631717015473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52073569746703017912041261 19527588655013631717015473)
                ·
                  refine ⟨14645691491260223787761605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19527588655013631717015473 14645691491260223787761605)
                  ·
                    refine ⟨2746067154611291960205301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14645691491260223787761605 2746067154611291960205301)
                    ·
                      refine ⟨257443795744808621269247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2746067154611291960205301 257443795744808621269247)
                      ·
                        rfl

theorem cell23_501370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 2, 4, 5].length) (baseStart_501370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_501370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_501370 prefixEnd_501370 := by exact prefixLift 501370
  have htrace : WordTrace (prefixWord ++ tailWord_501370) baseStart_501370 baseEnd_501370 := by
    simpa [prefixWord, tailWord_501370, baseEnd_501370] using wordTrace_append hprefix tailTrace_501370
  have hstable : (prefixWord ++ tailWord_501370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501370).length < 2 ^ (prefixWord ++ tailWord_501370).sum := by decide
  have hdescent : baseEnd_501370 < baseStart_501370 := by decide
  rcases family_descends (prefixWord ++ tailWord_501370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501417 : List Nat := [1, 2, 1, 1, 1, 1, 2, 2, 7, 2, 3]
def baseStart_501417 : Nat := 118140960795 + 501417 * 2 ^ 59
def prefixEnd_501417 : Nat := 4983230072969 + 3 ^ 40 * 501417 * 2
def baseEnd_501417 : Nat := 257467929335569937381531

theorem tailTrace_501417 : CollatzResearch.WordTrace tailWord_501417 prefixEnd_501417 257467929335569937381531 := by
  unfold tailWord_501417
  simp only [CollatzResearch.WordTrace]
  refine ⟨18288180424459319050942505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12192120282972879367295003 18288180424459319050942505)
  ·
    refine ⟨13716135318344489288206879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18288180424459319050942505 13716135318344489288206879)
    ·
      refine ⟨20574202977516733932310319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13716135318344489288206879 20574202977516733932310319)
      ·
        refine ⟨30861304466275100898465479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20574202977516733932310319 30861304466275100898465479)
        ·
          refine ⟨46291956699412651347698219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30861304466275100898465479 46291956699412651347698219)
          ·
            refine ⟨69437935049118977021547329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46291956699412651347698219 69437935049118977021547329)
            ·
              refine ⟨52078451286839232766160497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69437935049118977021547329 52078451286839232766160497)
              ·
                refine ⟨39058838465129424574620373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52078451286839232766160497 39058838465129424574620373)
                ·
                  refine ⟨915441526526470888467665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 39058838465129424574620373 915441526526470888467665)
                  ·
                    refine ⟨686581144894853166350749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 915441526526470888467665 686581144894853166350749)
                    ·
                      refine ⟨257467929335569937381531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 686581144894853166350749 257467929335569937381531)
                      ·
                        rfl

theorem cell23_501417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 7, 2, 3].length) (baseStart_501417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_501417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_501417 prefixEnd_501417 := by exact prefixLift 501417
  have htrace : WordTrace (prefixWord ++ tailWord_501417) baseStart_501417 baseEnd_501417 := by
    simpa [prefixWord, tailWord_501417, baseEnd_501417] using wordTrace_append hprefix tailTrace_501417
  have hstable : (prefixWord ++ tailWord_501417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501417).length < 2 ^ (prefixWord ++ tailWord_501417).sum := by decide
  have hdescent : baseEnd_501417 < baseStart_501417 := by decide
  rcases family_descends (prefixWord ++ tailWord_501417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501427 : List Nat := [1, 1, 1, 2, 3, 3, 1, 4, 1, 2, 4]
def baseStart_501427 : Nat := 118140960795 + 501427 * 2 ^ 59
def prefixEnd_501427 : Nat := 4983230072969 + 3 ^ 40 * 501427 * 2
def baseEnd_501427 : Nat := 257473064142114898256485

theorem tailTrace_501427 : CollatzResearch.WordTrace tailWord_501427 prefixEnd_501427 257473064142114898256485 := by
  unfold tailWord_501427
  simp only [CollatzResearch.WordTrace]
  refine ⟨18288545154423090758806535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12192363436282060505871023 18288545154423090758806535)
  ·
    refine ⟨27432817731634636138209803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18288545154423090758806535 27432817731634636138209803)
    ·
      refine ⟨41149226597451954207314705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27432817731634636138209803 41149226597451954207314705)
      ·
        refine ⟨30861919948088965655486029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41149226597451954207314705 30861919948088965655486029)
        ·
          refine ⟨11573219980533362120807261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30861919948088965655486029 11573219980533362120807261)
          ·
            refine ⟨4339957492700010795302723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11573219980533362120807261 4339957492700010795302723)
            ·
              refine ⟨6509936239050016192954085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4339957492700010795302723 6509936239050016192954085)
              ·
                refine ⟨1220613044821878036178891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6509936239050016192954085 1220613044821878036178891)
                ·
                  refine ⟨1830919567232817054268337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1220613044821878036178891 1830919567232817054268337)
                  ·
                    refine ⟨1373189675424612790701253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1830919567232817054268337 1373189675424612790701253)
                    ·
                      refine ⟨257473064142114898256485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1373189675424612790701253 257473064142114898256485)
                      ·
                        rfl

theorem cell23_501427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 4, 1, 2, 4].length) (baseStart_501427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_501427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_501427 prefixEnd_501427 := by exact prefixLift 501427
  have htrace : WordTrace (prefixWord ++ tailWord_501427) baseStart_501427 baseEnd_501427 := by
    simpa [prefixWord, tailWord_501427, baseEnd_501427] using wordTrace_append hprefix tailTrace_501427
  have hstable : (prefixWord ++ tailWord_501427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501427).length < 2 ^ (prefixWord ++ tailWord_501427).sum := by decide
  have hdescent : baseEnd_501427 < baseStart_501427 := by decide
  rcases family_descends (prefixWord ++ tailWord_501427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501431 : List Nat := [1, 1, 3, 1, 5, 1, 4, 1, 1, 1, 4]
def baseStart_501431 : Nat := 118140960795 + 501431 * 2 ^ 59
def prefixEnd_501431 : Nat := 4983230072969 + 3 ^ 40 * 501431 * 2
def baseEnd_501431 : Nat := 257475118064732882606467

theorem tailTrace_501431 : CollatzResearch.WordTrace tailWord_501431 prefixEnd_501431 257475118064732882606467 := by
  unfold tailWord_501431
  simp only [CollatzResearch.WordTrace]
  refine ⟨18288691046408599441952147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12192460697605732961301431 18288691046408599441952147)
  ·
    refine ⟨27433036569612899162928221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18288691046408599441952147 27433036569612899162928221)
    ·
      refine ⟨10287388713604837186098083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27433036569612899162928221 10287388713604837186098083)
      ·
        refine ⟨15431083070407255779147125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10287388713604837186098083 15431083070407255779147125)
        ·
          refine ⟨1446664037850680229295043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15431083070407255779147125 1446664037850680229295043)
          ·
            refine ⟨2169996056776020343942565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1446664037850680229295043 2169996056776020343942565)
            ·
              refine ⟨406874260645503814489231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2169996056776020343942565 406874260645503814489231)
              ·
                refine ⟨610311390968255721733847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 406874260645503814489231 610311390968255721733847)
                ·
                  refine ⟨915467086452383582600771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 610311390968255721733847 915467086452383582600771)
                  ·
                    refine ⟨1373200629678575373901157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 915467086452383582600771 1373200629678575373901157)
                    ·
                      refine ⟨257475118064732882606467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1373200629678575373901157 257475118064732882606467)
                      ·
                        rfl

theorem cell23_501431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 4, 1, 1, 1, 4].length) (baseStart_501431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_501431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_501431 prefixEnd_501431 := by exact prefixLift 501431
  have htrace : WordTrace (prefixWord ++ tailWord_501431) baseStart_501431 baseEnd_501431 := by
    simpa [prefixWord, tailWord_501431, baseEnd_501431] using wordTrace_append hprefix tailTrace_501431
  have hstable : (prefixWord ++ tailWord_501431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501431).length < 2 ^ (prefixWord ++ tailWord_501431).sum := by decide
  have hdescent : baseEnd_501431 < baseStart_501431 := by decide
  rcases family_descends (prefixWord ++ tailWord_501431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501442 : List Nat := [3, 5, 1, 2, 1, 1, 2, 1, 3, 1, 3]
def baseStart_501442 : Nat := 118140960795 + 501442 * 2 ^ 59
def prefixEnd_501442 : Nat := 4983230072969 + 3 ^ 40 * 501442 * 2
def baseEnd_501442 : Nat := 257480766351932339568917

theorem tailTrace_501442 : CollatzResearch.WordTrace tailWord_501442 prefixEnd_501442 257480766351932339568917 := by
  unfold tailWord_501442
  simp only [CollatzResearch.WordTrace]
  refine ⟨4572273062342187080150645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12192728166245832213735053 4572273062342187080150645)
  ·
    refine ⟨428650599594580038764123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4572273062342187080150645 428650599594580038764123)
    ·
      refine ⟨642975899391870058146185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 428650599594580038764123 642975899391870058146185)
      ·
        refine ⟨482231924543902543609639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 642975899391870058146185 482231924543902543609639)
        ·
          refine ⟨723347886815853815414459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 482231924543902543609639 723347886815853815414459)
          ·
            refine ⟨1085021830223780723121689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 723347886815853815414459 1085021830223780723121689)
            ·
              refine ⟨813766372667835542341267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1085021830223780723121689 813766372667835542341267)
              ·
                refine ⟨1220649559001753313511901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 813766372667835542341267 1220649559001753313511901)
                ·
                  refine ⟨457743584625657492566963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1220649559001753313511901 457743584625657492566963)
                  ·
                    refine ⟨686615376938486238850445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 457743584625657492566963 686615376938486238850445)
                    ·
                      refine ⟨257480766351932339568917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 686615376938486238850445 257480766351932339568917)
                      ·
                        rfl

theorem cell23_501442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_501442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_501442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_501442 prefixEnd_501442 := by exact prefixLift 501442
  have htrace : WordTrace (prefixWord ++ tailWord_501442) baseStart_501442 baseEnd_501442 := by
    simpa [prefixWord, tailWord_501442, baseEnd_501442] using wordTrace_append hprefix tailTrace_501442
  have hstable : (prefixWord ++ tailWord_501442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501442).length < 2 ^ (prefixWord ++ tailWord_501442).sum := by decide
  have hdescent : baseEnd_501442 < baseStart_501442 := by decide
  rcases family_descends (prefixWord ++ tailWord_501442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501448 : List Nat := [2, 1, 3, 1, 2, 2, 1, 6, 1, 2, 2]
def baseStart_501448 : Nat := 118140960795 + 501448 * 2 ^ 59
def prefixEnd_501448 : Nat := 4983230072969 + 3 ^ 40 * 501448 * 2
def baseEnd_501448 : Nat := 257483847235859316093889

theorem tailTrace_501448 : CollatzResearch.WordTrace tailWord_501448 prefixEnd_501448 257483847235859316093889 := by
  unfold tailWord_501448
  simp only [CollatzResearch.WordTrace]
  refine ⟨9144655543673505672660499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12192874058231340896880665 9144655543673505672660499)
  ·
    refine ⟨13716983315510258508990749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9144655543673505672660499 13716983315510258508990749)
    ·
      refine ⟨5143868743316346940871531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13716983315510258508990749 5143868743316346940871531)
      ·
        refine ⟨7715803114974520411307297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5143868743316346940871531 7715803114974520411307297)
        ·
          refine ⟨5786852336230890308480473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7715803114974520411307297 5786852336230890308480473)
          ·
            refine ⟨4340139252173167731360355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5786852336230890308480473 4340139252173167731360355)
            ·
              refine ⟨6510208878259751597040533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4340139252173167731360355 6510208878259751597040533)
              ·
                refine ⟨305166041168425856111275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6510208878259751597040533 305166041168425856111275)
                ·
                  refine ⟨457749061752638784166913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 305166041168425856111275 457749061752638784166913)
                  ·
                    refine ⟨343311796314479088125185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 457749061752638784166913 343311796314479088125185)
                    ·
                      refine ⟨257483847235859316093889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 343311796314479088125185 257483847235859316093889)
                      ·
                        rfl

theorem cell23_501448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 6, 1, 2, 2].length) (baseStart_501448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_501448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_501448 prefixEnd_501448 := by exact prefixLift 501448
  have htrace : WordTrace (prefixWord ++ tailWord_501448) baseStart_501448 baseEnd_501448 := by
    simpa [prefixWord, tailWord_501448, baseEnd_501448] using wordTrace_append hprefix tailTrace_501448
  have hstable : (prefixWord ++ tailWord_501448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501448).length < 2 ^ (prefixWord ++ tailWord_501448).sum := by decide
  have hdescent : baseEnd_501448 < baseStart_501448 := by decide
  rcases family_descends (prefixWord ++ tailWord_501448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501458 : List Nat := [3, 2, 2, 2, 2, 2, 3, 1, 2, 4]
def baseStart_501458 : Nat := 118140960795 + 501458 * 2 ^ 59
def prefixEnd_501458 : Nat := 4983230072969 + 3 ^ 40 * 501458 * 2
def baseEnd_501458 : Nat := 85829660680801425656281

theorem tailTrace_501458 : CollatzResearch.WordTrace tailWord_501458 prefixEnd_501458 85829660680801425656281 := by
  unfold tailWord_501458
  simp only [CollatzResearch.WordTrace]
  refine ⟨4572418954327695763296257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12193117211540522035456685 4572418954327695763296257)
  ·
    refine ⟨3429314215745771822472193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4572418954327695763296257 3429314215745771822472193)
    ·
      refine ⟨2571985661809328866854145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3429314215745771822472193 2571985661809328866854145)
      ·
        refine ⟨1928989246356996650140609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2571985661809328866854145 1928989246356996650140609)
        ·
          refine ⟨1446741934767747487605457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1928989246356996650140609 1446741934767747487605457)
          ·
            refine ⟨1085056451075810615704093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1446741934767747487605457 1085056451075810615704093)
            ·
              refine ⟨406896169153428980889035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1085056451075810615704093 406896169153428980889035)
              ·
                refine ⟨610344253730143471333553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 406896169153428980889035 610344253730143471333553)
                ·
                  refine ⟨457758190297607603500165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 610344253730143471333553 457758190297607603500165)
                  ·
                    refine ⟨85829660680801425656281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 457758190297607603500165 85829660680801425656281)
                    ·
                      rfl

theorem cell23_501458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 3, 1, 2, 4].length) (baseStart_501458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_501458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_501458 prefixEnd_501458 := by exact prefixLift 501458
  have htrace : WordTrace (prefixWord ++ tailWord_501458) baseStart_501458 baseEnd_501458 := by
    simpa [prefixWord, tailWord_501458, baseEnd_501458] using wordTrace_append hprefix tailTrace_501458
  have hstable : (prefixWord ++ tailWord_501458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501458).length < 2 ^ (prefixWord ++ tailWord_501458).sum := by decide
  have hdescent : baseEnd_501458 < baseStart_501458 := by decide
  rcases family_descends (prefixWord ++ tailWord_501458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501477 : List Nat := [1, 3, 1, 4, 1, 1, 1, 1, 1, 4, 5]
def baseStart_501477 : Nat := 118140960795 + 501477 * 2 ^ 59
def prefixEnd_501477 : Nat := 4983230072969 + 3 ^ 40 * 501477 * 2
def baseEnd_501477 : Nat := 257498738174839702631255

theorem tailTrace_501477 : CollatzResearch.WordTrace tailWord_501477 prefixEnd_501477 257498738174839702631255 := by
  unfold tailWord_501477
  simp only [CollatzResearch.WordTrace]
  refine ⟨18290368804241949298126685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12193579202827966198751123 18290368804241949298126685)
  ·
    refine ⟨6858888301590730986797507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18290368804241949298126685 6858888301590730986797507)
    ·
      refine ⟨10288332452386096480196261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6858888301590730986797507 10288332452386096480196261)
      ·
        refine ⟨1929062334822393090036799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10288332452386096480196261 1929062334822393090036799)
        ·
          refine ⟨2893593502233589635055199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1929062334822393090036799 2893593502233589635055199)
          ·
            refine ⟨4340390253350384452582799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2893593502233589635055199 4340390253350384452582799)
            ·
              refine ⟨6510585380025576678874199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4340390253350384452582799 6510585380025576678874199)
              ·
                refine ⟨9765878070038365018311299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6510585380025576678874199 9765878070038365018311299)
                ·
                  refine ⟨14648817105057547527466949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9765878070038365018311299 14648817105057547527466949)
                  ·
                    refine ⟨2746653207198290161400053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14648817105057547527466949 2746653207198290161400053)
                    ·
                      refine ⟨257498738174839702631255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2746653207198290161400053 257498738174839702631255)
                      ·
                        rfl

theorem cell23_501477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_501477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_501477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_501477 prefixEnd_501477 := by exact prefixLift 501477
  have htrace : WordTrace (prefixWord ++ tailWord_501477) baseStart_501477 baseEnd_501477 := by
    simpa [prefixWord, tailWord_501477, baseEnd_501477] using wordTrace_append hprefix tailTrace_501477
  have hstable : (prefixWord ++ tailWord_501477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501477).length < 2 ^ (prefixWord ++ tailWord_501477).sum := by decide
  have hdescent : baseEnd_501477 < baseStart_501477 := by decide
  rcases family_descends (prefixWord ++ tailWord_501477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501491 : List Nat := [1, 1, 1, 2, 2, 3, 4, 3, 1, 3, 2]
def baseStart_501491 : Nat := 118140960795 + 501491 * 2 ^ 59
def prefixEnd_501491 : Nat := 4983230072969 + 3 ^ 40 * 501491 * 2
def baseEnd_501491 : Nat := 257505926904002647856191

theorem tailTrace_501491 : CollatzResearch.WordTrace tailWord_501491 prefixEnd_501491 257505926904002647856191 := by
  unfold tailWord_501491
  simp only [CollatzResearch.WordTrace]
  refine ⟨18290879426191229689136327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12193919617460819792757551 18290879426191229689136327)
  ·
    refine ⟨27436319139286844533704491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18290879426191229689136327 27436319139286844533704491)
    ·
      refine ⟨41154478708930266800556737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27436319139286844533704491 41154478708930266800556737)
      ·
        refine ⟨30865859031697700100417553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41154478708930266800556737 30865859031697700100417553)
        ·
          refine ⟨23149394273773275075313165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30865859031697700100417553 23149394273773275075313165)
          ·
            refine ⟨8681022852664978153242437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23149394273773275075313165 8681022852664978153242437)
            ·
              refine ⟨1627691784874683403732957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8681022852664978153242437 1627691784874683403732957)
              ·
                refine ⟨610384419328006276399859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1627691784874683403732957 610384419328006276399859)
                ·
                  refine ⟨915576628992009414599789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 610384419328006276399859 915576628992009414599789)
                  ·
                    refine ⟨343341235872003530474921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 915576628992009414599789 343341235872003530474921)
                    ·
                      refine ⟨257505926904002647856191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 343341235872003530474921 257505926904002647856191)
                      ·
                        rfl

theorem cell23_501491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 3, 1, 3, 2].length) (baseStart_501491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_501491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_501491 prefixEnd_501491 := by exact prefixLift 501491
  have htrace : WordTrace (prefixWord ++ tailWord_501491) baseStart_501491 baseEnd_501491 := by
    simpa [prefixWord, tailWord_501491, baseEnd_501491] using wordTrace_append hprefix tailTrace_501491
  have hstable : (prefixWord ++ tailWord_501491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501491).length < 2 ^ (prefixWord ++ tailWord_501491).sum := by decide
  have hdescent : baseEnd_501491 < baseStart_501491 := by decide
  rcases family_descends (prefixWord ++ tailWord_501491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501504 : List Nat := [2, 1, 1, 2, 1, 1, 2, 4, 3, 4, 2]
def baseStart_501504 : Nat := 118140960795 + 501504 * 2 ^ 59
def prefixEnd_501504 : Nat := 4983230072969 + 3 ^ 40 * 501504 * 2
def baseEnd_501504 : Nat := 257512602152511096993631

theorem tailTrace_501504 : CollatzResearch.WordTrace tailWord_501504 prefixEnd_501504 257512602152511096993631 := by
  unfold tailWord_501504
  simp only [CollatzResearch.WordTrace]
  refine ⟨9145676787572066454679783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12194235716762755272906377 9145676787572066454679783)
  ·
    refine ⟨13718515181358099682019675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9145676787572066454679783 13718515181358099682019675)
    ·
      refine ⟨20577772772037149523029513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13718515181358099682019675 20577772772037149523029513)
      ·
        refine ⟨15433329579027862142272135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20577772772037149523029513 15433329579027862142272135)
        ·
          refine ⟨23149994368541793213408203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15433329579027862142272135 23149994368541793213408203)
          ·
            refine ⟨34724991552812689820112305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23149994368541793213408203 34724991552812689820112305)
            ·
              refine ⟨26043743664609517365084229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34724991552812689820112305 26043743664609517365084229)
              ·
                refine ⟨4883201937114284505953293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26043743664609517365084229 4883201937114284505953293)
                ·
                  refine ⟨1831200726417856689732485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4883201937114284505953293 1831200726417856689732485)
                  ·
                    refine ⟨343350136203348129324841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1831200726417856689732485 343350136203348129324841)
                    ·
                      refine ⟨257512602152511096993631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 343350136203348129324841 257512602152511096993631)
                      ·
                        rfl

theorem cell23_501504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 4, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 4, 3, 4, 2].length) (baseStart_501504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_501504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_501504 prefixEnd_501504 := by exact prefixLift 501504
  have htrace : WordTrace (prefixWord ++ tailWord_501504) baseStart_501504 baseEnd_501504 := by
    simpa [prefixWord, tailWord_501504, baseEnd_501504] using wordTrace_append hprefix tailTrace_501504
  have hstable : (prefixWord ++ tailWord_501504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501504).length < 2 ^ (prefixWord ++ tailWord_501504).sum := by decide
  have hdescent : baseEnd_501504 < baseStart_501504 := by decide
  rcases family_descends (prefixWord ++ tailWord_501504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501555 : List Nat := [1, 1, 1, 2, 7, 1, 2, 2, 2, 2, 2]
def baseStart_501555 : Nat := 118140960795 + 501555 * 2 ^ 59
def prefixEnd_501555 : Nat := 4983230072969 + 3 ^ 40 * 501555 * 2
def baseEnd_501555 : Nat := 257538789665890397455897

theorem tailTrace_501555 : CollatzResearch.WordTrace tailWord_501555 prefixEnd_501555 257538789665890397455897 := by
  unfold tailWord_501555
  simp only [CollatzResearch.WordTrace]
  refine ⟨18293213697959368619466119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12195475798639579079644079 18293213697959368619466119)
  ·
    refine ⟨27439820546939052929199179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18293213697959368619466119 27439820546939052929199179)
    ·
      refine ⟨41159730820408579393798769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27439820546939052929199179 41159730820408579393798769)
      ·
        refine ⟨30869798115306434545349077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41159730820408579393798769 30869798115306434545349077)
        ·
          refine ⟨723510893327494559656619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 30869798115306434545349077 723510893327494559656619)
          ·
            refine ⟨1085266339991241839484929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 723510893327494559656619 1085266339991241839484929)
            ·
              refine ⟨813949754993431379613697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1085266339991241839484929 813949754993431379613697)
              ·
                refine ⟨610462316245073534710273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 813949754993431379613697 610462316245073534710273)
                ·
                  refine ⟨457846737183805151032705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 610462316245073534710273 457846737183805151032705)
                  ·
                    refine ⟨343385052887853863274529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 457846737183805151032705 343385052887853863274529)
                    ·
                      refine ⟨257538789665890397455897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 343385052887853863274529 257538789665890397455897)
                      ·
                        rfl

theorem cell23_501555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 2, 2, 2, 2, 2].length) (baseStart_501555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_501555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_501555 prefixEnd_501555 := by exact prefixLift 501555
  have htrace : WordTrace (prefixWord ++ tailWord_501555) baseStart_501555 baseEnd_501555 := by
    simpa [prefixWord, tailWord_501555, baseEnd_501555] using wordTrace_append hprefix tailTrace_501555
  have hstable : (prefixWord ++ tailWord_501555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501555).length < 2 ^ (prefixWord ++ tailWord_501555).sum := by decide
  have hdescent : baseEnd_501555 < baseStart_501555 := by decide
  rcases family_descends (prefixWord ++ tailWord_501555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501594 : List Nat := [3, 1, 1, 2, 1, 3, 3, 1, 1, 3, 4]
def baseStart_501594 : Nat := 118140960795 + 501594 * 2 ^ 59
def prefixEnd_501594 : Nat := 4983230072969 + 3 ^ 40 * 501594 * 2
def baseEnd_501594 : Nat := 257558815411415744868217

theorem tailTrace_501594 : CollatzResearch.WordTrace tailWord_501594 prefixEnd_501594 257558815411415744868217 := by
  unfold tailWord_501594
  simp only [CollatzResearch.WordTrace]
  refine ⟨4573659036204519570033959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12196424096545385520090557 4573659036204519570033959)
  ·
    refine ⟨6860488554306779355050939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4573659036204519570033959 6860488554306779355050939)
    ·
      refine ⟨10290732831460169032576409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6860488554306779355050939 10290732831460169032576409)
      ·
        refine ⟨7718049623595126774432307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10290732831460169032576409 7718049623595126774432307)
        ·
          refine ⟨11577074435392690161648461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7718049623595126774432307 11577074435392690161648461)
          ·
            refine ⟨4341402913272258810618173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11577074435392690161648461 4341402913272258810618173)
            ·
              refine ⟨1628026092477097053981815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4341402913272258810618173 1628026092477097053981815)
              ·
                refine ⟨2442039138715645580972723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1628026092477097053981815 2442039138715645580972723)
                ·
                  refine ⟨3663058708073468371459085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2442039138715645580972723 3663058708073468371459085)
                  ·
                    refine ⟨1373647015527550639297157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3663058708073468371459085 1373647015527550639297157)
                    ·
                      refine ⟨257558815411415744868217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1373647015527550639297157 257558815411415744868217)
                      ·
                        rfl

theorem cell23_501594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 1, 1, 3, 4].length) (baseStart_501594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_501594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_501594 prefixEnd_501594 := by exact prefixLift 501594
  have htrace : WordTrace (prefixWord ++ tailWord_501594) baseStart_501594 baseEnd_501594 := by
    simpa [prefixWord, tailWord_501594, baseEnd_501594] using wordTrace_append hprefix tailTrace_501594
  have hstable : (prefixWord ++ tailWord_501594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501594).length < 2 ^ (prefixWord ++ tailWord_501594).sum := by decide
  have hdescent : baseEnd_501594 < baseStart_501594 := by decide
  rcases family_descends (prefixWord ++ tailWord_501594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501644 : List Nat := [2, 2, 1, 2, 1, 2, 1, 1, 1, 7, 3]
def baseStart_501644 : Nat := 118140960795 + 501644 * 2 ^ 59
def prefixEnd_501644 : Nat := 4983230072969 + 3 ^ 40 * 501644 * 2
def baseEnd_501644 : Nat := 257584489444140549242987

theorem tailTrace_501644 : CollatzResearch.WordTrace tailWord_501644 prefixEnd_501644 257584489444140549242987 := by
  unfold tailWord_501644
  simp only [CollatzResearch.WordTrace]
  refine ⟨9148229897318468409727993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12197639863091291212970657 9148229897318468409727993)
  ·
    refine ⟨6861172422988851307295995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9148229897318468409727993 6861172422988851307295995)
    ·
      refine ⟨10291758634483276960943993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6861172422988851307295995 10291758634483276960943993)
      ·
        refine ⟨7718818975862457720707995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10291758634483276960943993 7718818975862457720707995)
        ·
          refine ⟨11578228463793686581061993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7718818975862457720707995 11578228463793686581061993)
          ·
            refine ⟨8683671347845264935796495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11578228463793686581061993 8683671347845264935796495)
            ·
              refine ⟨13025507021767897403694743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8683671347845264935796495 13025507021767897403694743)
              ·
                refine ⟨19538260532651846105542115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13025507021767897403694743 19538260532651846105542115)
                ·
                  refine ⟨29307390798977769158313173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19538260532651846105542115 29307390798977769158313173)
                  ·
                    refine ⟨686891971851041464647965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29307390798977769158313173 686891971851041464647965)
                    ·
                      refine ⟨257584489444140549242987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 686891971851041464647965 257584489444140549242987)
                      ·
                        rfl

theorem cell23_501644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 1, 7, 3].length) (baseStart_501644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_501644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_501644 prefixEnd_501644 := by exact prefixLift 501644
  have htrace : WordTrace (prefixWord ++ tailWord_501644) baseStart_501644 baseEnd_501644 := by
    simpa [prefixWord, tailWord_501644, baseEnd_501644] using wordTrace_append hprefix tailTrace_501644
  have hstable : (prefixWord ++ tailWord_501644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501644).length < 2 ^ (prefixWord ++ tailWord_501644).sum := by decide
  have hdescent : baseEnd_501644 < baseStart_501644 := by decide
  rcases family_descends (prefixWord ++ tailWord_501644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501655 : List Nat := [1, 1, 3, 3, 1, 5, 1, 3, 1, 4]
def baseStart_501655 : Nat := 118140960795 + 501655 * 2 ^ 59
def prefixEnd_501655 : Nat := 4983230072969 + 3 ^ 40 * 501655 * 2
def baseEnd_501655 : Nat := 85863379243780002068479

theorem tailTrace_501655 : CollatzResearch.WordTrace tailWord_501655 prefixEnd_501655 85863379243780002068479 := by
  unfold tailWord_501655
  simp only [CollatzResearch.WordTrace]
  refine ⟨18296860997597085698106419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12197907331731390465404279 18296860997597085698106419)
  ·
    refine ⟨27445291496395628547159629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18296860997597085698106419 27445291496395628547159629)
    ·
      refine ⟨10291984311148360705184861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27445291496395628547159629 10291984311148360705184861)
      ·
        refine ⟨3859494116680635264444323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10291984311148360705184861 3859494116680635264444323)
        ·
          refine ⟨5789241175020952896666485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3859494116680635264444323 5789241175020952896666485)
          ·
            refine ⟨542741360158214334062483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5789241175020952896666485 542741360158214334062483)
            ·
              refine ⟨814112040237321501093725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 542741360158214334062483 814112040237321501093725)
              ·
                refine ⟨305292015088995562910147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 814112040237321501093725 305292015088995562910147)
                ·
                  refine ⟨457938022633493344365221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 305292015088995562910147 457938022633493344365221)
                  ·
                    refine ⟨85863379243780002068479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 457938022633493344365221 85863379243780002068479)
                    ·
                      rfl

theorem cell23_501655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 1, 3, 1, 4].length) (baseStart_501655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_501655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_501655 prefixEnd_501655 := by exact prefixLift 501655
  have htrace : WordTrace (prefixWord ++ tailWord_501655) baseStart_501655 baseEnd_501655 := by
    simpa [prefixWord, tailWord_501655, baseEnd_501655] using wordTrace_append hprefix tailTrace_501655
  have hstable : (prefixWord ++ tailWord_501655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501655).length < 2 ^ (prefixWord ++ tailWord_501655).sum := by decide
  have hdescent : baseEnd_501655 < baseStart_501655 := by decide
  rcases family_descends (prefixWord ++ tailWord_501655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501664 : List Nat := [2, 1, 1, 4, 1, 1, 1, 2, 5, 5]
def baseStart_501664 : Nat := 118140960795 + 501664 * 2 ^ 59
def prefixEnd_501664 : Nat := 4983230072969 + 3 ^ 40 * 501664 * 2
def baseEnd_501664 : Nat := 85864919685743490330965

theorem tailTrace_501664 : CollatzResearch.WordTrace tailWord_501664 prefixEnd_501664 85864919685743490330965 := by
  unfold tailWord_501664
  simp only [CollatzResearch.WordTrace]
  refine ⟨9148594627282240117592023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12198126169709653490122697 9148594627282240117592023)
  ·
    refine ⟨13722891940923360176388035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9148594627282240117592023 13722891940923360176388035)
    ·
      refine ⟨20584337911385040264582053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13722891940923360176388035 20584337911385040264582053)
      ·
        refine ⟨3859563358384695049609135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20584337911385040264582053 3859563358384695049609135)
        ·
          refine ⟨5789345037577042574413703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3859563358384695049609135 5789345037577042574413703)
          ·
            refine ⟨8684017556365563861620555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5789345037577042574413703 8684017556365563861620555)
            ·
              refine ⟨13026026334548345792430833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8684017556365563861620555 13026026334548345792430833)
              ·
                refine ⟨9769519750911259344323125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13026026334548345792430833 9769519750911259344323125)
                ·
                  refine ⟨915892476647930563530293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9769519750911259344323125 915892476647930563530293)
                  ·
                    refine ⟨85864919685743490330965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 915892476647930563530293 85864919685743490330965)
                    ·
                      rfl

theorem cell23_501664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 2, 5, 5].length) (baseStart_501664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_501664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_501664 prefixEnd_501664 := by exact prefixLift 501664
  have htrace : WordTrace (prefixWord ++ tailWord_501664) baseStart_501664 baseEnd_501664 := by
    simpa [prefixWord, tailWord_501664, baseEnd_501664] using wordTrace_append hprefix tailTrace_501664
  have hstable : (prefixWord ++ tailWord_501664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501664).length < 2 ^ (prefixWord ++ tailWord_501664).sum := by decide
  have hdescent : baseEnd_501664 < baseStart_501664 := by decide
  rcases family_descends (prefixWord ++ tailWord_501664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501672 : List Nat := [2, 1, 6, 2, 1, 2, 1, 1, 3, 4]
def baseStart_501672 : Nat := 118140960795 + 501672 * 2 ^ 59
def prefixEnd_501672 : Nat := 4983230072969 + 3 ^ 40 * 501672 * 2
def baseEnd_501672 : Nat := 85866288967488813230953

theorem tailTrace_501672 : CollatzResearch.WordTrace tailWord_501672 prefixEnd_501672 85866288967488813230953 := by
  unfold tailWord_501672
  simp only [CollatzResearch.WordTrace]
  refine ⟨9148740519267748800737635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12198320692356998400983513 9148740519267748800737635)
  ·
    refine ⟨13723110778901623201106453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9148740519267748800737635 13723110778901623201106453)
    ·
      refine ⟨643270817761013587551865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 13723110778901623201106453 643270817761013587551865)
      ·
        refine ⟨482453113320760190663899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 643270817761013587551865 482453113320760190663899)
        ·
          refine ⟨723679669981140285995849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 482453113320760190663899 723679669981140285995849)
          ·
            refine ⟨542759752485855214496887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 723679669981140285995849 542759752485855214496887)
            ·
              refine ⟨814139628728782821745331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 542759752485855214496887 814139628728782821745331)
              ·
                refine ⟨1221209443093174232617997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 814139628728782821745331 1221209443093174232617997)
                ·
                  refine ⟨457953541159940337231749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1221209443093174232617997 457953541159940337231749)
                  ·
                    refine ⟨85866288967488813230953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 457953541159940337231749 85866288967488813230953)
                    ·
                      rfl

theorem cell23_501672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_501672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_501672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_501672 prefixEnd_501672 := by exact prefixLift 501672
  have htrace : WordTrace (prefixWord ++ tailWord_501672) baseStart_501672 baseEnd_501672 := by
    simpa [prefixWord, tailWord_501672, baseEnd_501672] using wordTrace_append hprefix tailTrace_501672
  have hstable : (prefixWord ++ tailWord_501672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501672).length < 2 ^ (prefixWord ++ tailWord_501672).sum := by decide
  have hdescent : baseEnd_501672 < baseStart_501672 := by decide
  rcases family_descends (prefixWord ++ tailWord_501672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501701 : List Nat := [1, 3, 1, 1, 1, 1, 1, 8, 1, 1, 4]
def baseStart_501701 : Nat := 118140960795 + 501701 * 2 ^ 59
def prefixEnd_501701 : Nat := 4983230072969 + 3 ^ 40 * 501701 * 2
def baseEnd_501701 : Nat := 257613757841446826230225

theorem tailTrace_501701 : CollatzResearch.WordTrace tailWord_501701 prefixEnd_501701 257613757841446826230225 := by
  unfold tailWord_501701
  simp only [CollatzResearch.WordTrace]
  refine ⟨18298538755430435554280957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12199025836953623702853971 18298538755430435554280957)
  ·
    refine ⟨6861952033286413332855359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18298538755430435554280957 6861952033286413332855359)
    ·
      refine ⟨10292928049929619999283039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6861952033286413332855359 10292928049929619999283039)
      ·
        refine ⟨15439392074894429998924559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10292928049929619999283039 15439392074894429998924559)
        ·
          refine ⟨23159088112341644998386839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15439392074894429998924559 23159088112341644998386839)
          ·
            refine ⟨34738632168512467497580259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23159088112341644998386839 34738632168512467497580259)
            ·
              refine ⟨52107948252768701246370389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34738632168512467497580259 52107948252768701246370389)
              ·
                refine ⟨610640018587133217730903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 52107948252768701246370389 610640018587133217730903)
                ·
                  refine ⟨915960027880699826596355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 610640018587133217730903 915960027880699826596355)
                  ·
                    refine ⟨1373940041821049739894533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 915960027880699826596355 1373940041821049739894533)
                    ·
                      refine ⟨257613757841446826230225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1373940041821049739894533 257613757841446826230225)
                      ·
                        rfl

theorem cell23_501701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 8, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 8, 1, 1, 4].length) (baseStart_501701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_501701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_501701 prefixEnd_501701 := by exact prefixLift 501701
  have htrace : WordTrace (prefixWord ++ tailWord_501701) baseStart_501701 baseEnd_501701 := by
    simpa [prefixWord, tailWord_501701, baseEnd_501701] using wordTrace_append hprefix tailTrace_501701
  have hstable : (prefixWord ++ tailWord_501701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501701).length < 2 ^ (prefixWord ++ tailWord_501701).sum := by decide
  have hdescent : baseEnd_501701 < baseStart_501701 := by decide
  rcases family_descends (prefixWord ++ tailWord_501701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501744 : List Nat := [2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 6]
def baseStart_501744 : Nat := 118140960795 + 501744 * 2 ^ 59
def prefixEnd_501744 : Nat := 4983230072969 + 3 ^ 40 * 501744 * 2
def baseEnd_501744 : Nat := 257635837509590157992527

theorem tailTrace_501744 : CollatzResearch.WordTrace tailWord_501744 prefixEnd_501744 257635837509590157992527 := by
  unfold tailWord_501744
  simp only [CollatzResearch.WordTrace]
  refine ⟨9150053547137326949048143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12200071396183102598730857 9150053547137326949048143)
  ·
    refine ⟨13725080320705990423572215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9150053547137326949048143 13725080320705990423572215)
    ·
      refine ⟨20587620481058985635358323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13725080320705990423572215 20587620481058985635358323)
      ·
        refine ⟨30881430721588478453037485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20587620481058985635358323 30881430721588478453037485)
        ·
          refine ⟨11580536520595679419889057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30881430721588478453037485 11580536520595679419889057)
          ·
            refine ⟨8685402390446759564916793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11580536520595679419889057 8685402390446759564916793)
            ·
              refine ⟨6514051792835069673687595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8685402390446759564916793 6514051792835069673687595)
              ·
                refine ⟨9771077689252604510531393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6514051792835069673687595 9771077689252604510531393)
                ·
                  refine ⟨7328308266939453382898545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9771077689252604510531393 7328308266939453382898545)
                  ·
                    refine ⟨5496231200204590037173909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7328308266939453382898545 5496231200204590037173909)
                    ·
                      refine ⟨257635837509590157992527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5496231200204590037173909 257635837509590157992527)
                      ·
                        rfl

theorem cell23_501744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 6].length) (baseStart_501744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_501744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_501744 prefixEnd_501744 := by exact prefixLift 501744
  have htrace : WordTrace (prefixWord ++ tailWord_501744) baseStart_501744 baseEnd_501744 := by
    simpa [prefixWord, tailWord_501744, baseEnd_501744] using wordTrace_append hprefix tailTrace_501744
  have hstable : (prefixWord ++ tailWord_501744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501744).length < 2 ^ (prefixWord ++ tailWord_501744).sum := by decide
  have hdescent : baseEnd_501744 < baseStart_501744 := by decide
  rcases family_descends (prefixWord ++ tailWord_501744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501768 : List Nat := [2, 1, 3, 2, 1, 2, 2, 2, 4, 1, 3]
def baseStart_501768 : Nat := 118140960795 + 501768 * 2 ^ 59
def prefixEnd_501768 : Nat := 4983230072969 + 3 ^ 40 * 501768 * 2
def baseEnd_501768 : Nat := 257648161045298064092417

theorem tailTrace_501768 : CollatzResearch.WordTrace tailWord_501768 prefixEnd_501768 257648161045298064092417 := by
  unfold tailWord_501768
  simp only [CollatzResearch.WordTrace]
  refine ⟨9150491223093852998484979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12200654964125137331313305 9150491223093852998484979)
  ·
    refine ⟨13725736834640779497727469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9150491223093852998484979 13725736834640779497727469)
    ·
      refine ⟨5147151312990292311647801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13725736834640779497727469 5147151312990292311647801)
      ·
        refine ⟨3860363484742719233735851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5147151312990292311647801 3860363484742719233735851)
        ·
          refine ⟨5790545227114078850603777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3860363484742719233735851 5790545227114078850603777)
          ·
            refine ⟨4342908920335559137952833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5790545227114078850603777 4342908920335559137952833)
            ·
              refine ⟨3257181690251669353464625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4342908920335559137952833 3257181690251669353464625)
              ·
                refine ⟨2442886267688752015098469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3257181690251669353464625 2442886267688752015098469)
                ·
                  refine ⟨458041175191641002830963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2442886267688752015098469 458041175191641002830963)
                  ·
                    refine ⟨687061762787461504246445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 458041175191641002830963 687061762787461504246445)
                    ·
                      refine ⟨257648161045298064092417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 687061762787461504246445 257648161045298064092417)
                      ·
                        rfl

theorem cell23_501768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 2, 2, 4, 1, 3].length) (baseStart_501768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_501768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_501768 prefixEnd_501768 := by exact prefixLift 501768
  have htrace : WordTrace (prefixWord ++ tailWord_501768) baseStart_501768 baseEnd_501768 := by
    simpa [prefixWord, tailWord_501768, baseEnd_501768] using wordTrace_append hprefix tailTrace_501768
  have hstable : (prefixWord ++ tailWord_501768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501768).length < 2 ^ (prefixWord ++ tailWord_501768).sum := by decide
  have hdescent : baseEnd_501768 < baseStart_501768 := by decide
  rcases family_descends (prefixWord ++ tailWord_501768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501811 : List Nat := [1, 1, 1, 2, 4, 1, 2, 2, 2, 4, 3]
def baseStart_501811 : Nat := 118140960795 + 501811 * 2 ^ 59
def prefixEnd_501811 : Nat := 4983230072969 + 3 ^ 40 * 501811 * 2
def baseEnd_501811 : Nat := 257670240713441395854719

theorem tailTrace_501811 : CollatzResearch.WordTrace tailWord_501811 prefixEnd_501811 257670240713441395854719 := by
  unfold tailWord_501811
  simp only [CollatzResearch.WordTrace]
  refine ⟨18302550785031924340785287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12201700523354616227190191 18302550785031924340785287)
  ·
    refine ⟨27453826177547886511177931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18302550785031924340785287 27453826177547886511177931)
    ·
      refine ⟨41180739266321829766766897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27453826177547886511177931 41180739266321829766766897)
      ·
        refine ⟨30885554449741372325075173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41180739266321829766766897 30885554449741372325075173)
        ·
          refine ⟨5791041459326507310951595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30885554449741372325075173 5791041459326507310951595)
          ·
            refine ⟨8686562188989760966427393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5791041459326507310951595 8686562188989760966427393)
            ·
              refine ⟨6514921641742320724820545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8686562188989760966427393 6514921641742320724820545)
              ·
                refine ⟨4886191231306740543615409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6514921641742320724820545 4886191231306740543615409)
                ·
                  refine ⟨3664643423480055407711557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4886191231306740543615409 3664643423480055407711557)
                  ·
                    refine ⟨687120641902510388945917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3664643423480055407711557 687120641902510388945917)
                    ·
                      refine ⟨257670240713441395854719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 687120641902510388945917 257670240713441395854719)
                      ·
                        rfl

theorem cell23_501811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 2, 2, 4, 3].length) (baseStart_501811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_501811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_501811 prefixEnd_501811 := by exact prefixLift 501811
  have htrace : WordTrace (prefixWord ++ tailWord_501811) baseStart_501811 baseEnd_501811 := by
    simpa [prefixWord, tailWord_501811, baseEnd_501811] using wordTrace_append hprefix tailTrace_501811
  have hstable : (prefixWord ++ tailWord_501811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501811).length < 2 ^ (prefixWord ++ tailWord_501811).sum := by decide
  have hdescent : baseEnd_501811 < baseStart_501811 := by decide
  rcases family_descends (prefixWord ++ tailWord_501811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501848 : List Nat := [2, 1, 2, 2, 1, 6, 1, 1, 7]
def baseStart_501848 : Nat := 118140960795 + 501848 * 2 ^ 59
def prefixEnd_501848 : Nat := 4983230072969 + 3 ^ 40 * 501848 * 2
def baseEnd_501848 : Nat := 28632137721961972343561

theorem tailTrace_501848 : CollatzResearch.WordTrace tailWord_501848 prefixEnd_501848 28632137721961972343561 := by
  unfold tailWord_501848
  simp only [CollatzResearch.WordTrace]
  refine ⟨9151950142948939829941099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12202600190598586439921465 9151950142948939829941099)
  ·
    refine ⟨13727925214423409744911649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9151950142948939829941099 13727925214423409744911649)
    ·
      refine ⟨10295943910817557308683737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13727925214423409744911649 10295943910817557308683737)
      ·
        refine ⟨7721957933113167981512803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10295943910817557308683737 7721957933113167981512803)
        ·
          refine ⟨11582936899669751972269205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7721957933113167981512803 11582936899669751972269205)
          ·
            refine ⟨542950167172019623700119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 11582936899669751972269205 542950167172019623700119)
            ·
              refine ⟨814425250758029435550179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 542950167172019623700119 814425250758029435550179)
              ·
                refine ⟨1221637876137044153325269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 814425250758029435550179 1221637876137044153325269)
                ·
                  refine ⟨28632137721961972343561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1221637876137044153325269 28632137721961972343561)
                  ·
                    rfl

theorem cell23_501848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 1, 1, 7].length) (baseStart_501848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_501848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_501848 prefixEnd_501848 := by exact prefixLift 501848
  have htrace : WordTrace (prefixWord ++ tailWord_501848) baseStart_501848 baseEnd_501848 := by
    simpa [prefixWord, tailWord_501848, baseEnd_501848] using wordTrace_append hprefix tailTrace_501848
  have hstable : (prefixWord ++ tailWord_501848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501848).length < 2 ^ (prefixWord ++ tailWord_501848).sum := by decide
  have hdescent : baseEnd_501848 < baseStart_501848 := by decide
  rcases family_descends (prefixWord ++ tailWord_501848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501961 : List Nat := [1, 2, 1, 1, 2, 1, 1, 4, 2, 1, 7]
def baseStart_501961 : Nat := 118140960795 + 501961 * 2 ^ 59
def prefixEnd_501961 : Nat := 4983230072969 + 3 ^ 40 * 501961 * 2
def baseEnd_501961 : Nat := 257747262811615808979029

theorem tailTrace_501961 : CollatzResearch.WordTrace tailWord_501961 prefixEnd_501961 257747262811615808979029 := by
  unfold tailWord_501961
  simp only [CollatzResearch.WordTrace]
  refine ⟨18308021734488499958745737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12205347822992333305830491 18308021734488499958745737)
  ·
    refine ⟨13731016300866374969059303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18308021734488499958745737 13731016300866374969059303)
    ·
      refine ⟨20596524451299562453588955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13731016300866374969059303 20596524451299562453588955)
      ·
        refine ⟨30894786676949343680383433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20596524451299562453588955 30894786676949343680383433)
        ·
          refine ⟨23171090007712007760287575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30894786676949343680383433 23171090007712007760287575)
          ·
            refine ⟨34756635011568011640431363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23171090007712007760287575 34756635011568011640431363)
            ·
              refine ⟨52134952517352017460647045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34756635011568011640431363 52134952517352017460647045)
              ·
                refine ⟨9775303597003503273871321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52134952517352017460647045 9775303597003503273871321)
                ·
                  refine ⟨7331477697752627455403491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9775303597003503273871321 7331477697752627455403491)
                  ·
                    refine ⟨10997216546628941183105237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7331477697752627455403491 10997216546628941183105237)
                    ·
                      refine ⟨257747262811615808979029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 10997216546628941183105237 257747262811615808979029)
                      ·
                        rfl

theorem cell23_501961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 4, 2, 1, 7].length) (baseStart_501961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_501961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_501961 prefixEnd_501961 := by exact prefixLift 501961
  have htrace : WordTrace (prefixWord ++ tailWord_501961) baseStart_501961 baseEnd_501961 := by
    simpa [prefixWord, tailWord_501961, baseEnd_501961] using wordTrace_append hprefix tailTrace_501961
  have hstable : (prefixWord ++ tailWord_501961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501961).length < 2 ^ (prefixWord ++ tailWord_501961).sum := by decide
  have hdescent : baseEnd_501961 < baseStart_501961 := by decide
  rcases family_descends (prefixWord ++ tailWord_501961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501985 : List Nat := [1, 2, 3, 1, 3, 1, 4, 2, 1, 5]
def baseStart_501985 : Nat := 118140960795 + 501985 * 2 ^ 59
def prefixEnd_501985 : Nat := 4983230072969 + 3 ^ 40 * 501985 * 2
def baseEnd_501985 : Nat := 85919862115774571692973

theorem tailTrace_501985 : CollatzResearch.WordTrace tailWord_501985 prefixEnd_501985 85919862115774571692973 := by
  unfold tailWord_501985
  simp only [CollatzResearch.WordTrace]
  refine ⟨18308897086401552057619409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12205931390934368038412939 18308897086401552057619409)
  ·
    refine ⟨13731672814801164043214557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18308897086401552057619409 13731672814801164043214557)
    ·
      refine ⟨5149377305550436516205459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13731672814801164043214557 5149377305550436516205459)
      ·
        refine ⟨7724065958325654774308189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5149377305550436516205459 7724065958325654774308189)
        ·
          refine ⟨2896524734372120540365571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7724065958325654774308189 2896524734372120540365571)
          ·
            refine ⟨4344787101558180810548357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2896524734372120540365571 4344787101558180810548357)
            ·
              refine ⟨814647581542158901977817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4344787101558180810548357 814647581542158901977817)
              ·
                refine ⟨610985686156619176483363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 814647581542158901977817 610985686156619176483363)
                ·
                  refine ⟨916478529234928764725045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 610985686156619176483363 916478529234928764725045)
                  ·
                    refine ⟨85919862115774571692973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 916478529234928764725045 85919862115774571692973)
                    ·
                      rfl

theorem cell23_501985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 4, 2, 1, 5].length) (baseStart_501985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_501985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_501985 prefixEnd_501985 := by exact prefixLift 501985
  have htrace : WordTrace (prefixWord ++ tailWord_501985) baseStart_501985 baseEnd_501985 := by
    simpa [prefixWord, tailWord_501985, baseEnd_501985] using wordTrace_append hprefix tailTrace_501985
  have hstable : (prefixWord ++ tailWord_501985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501985).length < 2 ^ (prefixWord ++ tailWord_501985).sum := by decide
  have hdescent : baseEnd_501985 < baseStart_501985 := by decide
  rcases family_descends (prefixWord ++ tailWord_501985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501998 : List Nat := [4, 1, 2, 1, 1, 1, 1, 3, 3, 6]
def baseStart_501998 : Nat := 118140960795 + 501998 * 2 ^ 59
def prefixEnd_501998 : Nat := 4983230072969 + 3 ^ 40 * 501998 * 2
def baseEnd_501998 : Nat := 85922087198610721405453

theorem tailTrace_501998 : CollatzResearch.WordTrace tailWord_501998 prefixEnd_501998 85922087198610721405453 := by
  unfold tailWord_501998
  simp only [CollatzResearch.WordTrace]
  refine ⟨2288671404419306909730331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12206247490236303518561765 2288671404419306909730331)
  ·
    refine ⟨3433007106628960364595497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2288671404419306909730331 3433007106628960364595497)
    ·
      refine ⟨2574755329971720273446623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3433007106628960364595497 2574755329971720273446623)
      ·
        refine ⟨3862132994957580410169935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2574755329971720273446623 3862132994957580410169935)
        ·
          refine ⟨5793199492436370615254903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3862132994957580410169935 5793199492436370615254903)
          ·
            refine ⟨8689799238654555922882355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5793199492436370615254903 8689799238654555922882355)
            ·
              refine ⟨13034698857981833884323533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8689799238654555922882355 13034698857981833884323533)
              ·
                refine ⟨4888012071743187706621325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13034698857981833884323533 4888012071743187706621325)
                ·
                  refine ⟨1833004526903695389982997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4888012071743187706621325 1833004526903695389982997)
                  ·
                    refine ⟨85922087198610721405453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1833004526903695389982997 85922087198610721405453)
                    ·
                      rfl

theorem cell23_501998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 3, 3, 6].length) (baseStart_501998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_501998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_501998 prefixEnd_501998 := by exact prefixLift 501998
  have htrace : WordTrace (prefixWord ++ tailWord_501998) baseStart_501998 baseEnd_501998 := by
    simpa [prefixWord, tailWord_501998, baseEnd_501998] using wordTrace_append hprefix tailTrace_501998
  have hstable : (prefixWord ++ tailWord_501998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501998).length < 2 ^ (prefixWord ++ tailWord_501998).sum := by decide
  have hdescent : baseEnd_501998 < baseStart_501998 := by decide
  rcases family_descends (prefixWord ++ tailWord_501998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_501999 : List Nat := [1, 1, 2, 1, 6, 1, 3, 3, 1, 1, 3]
def baseStart_501999 : Nat := 118140960795 + 501999 * 2 ^ 59
def prefixEnd_501999 : Nat := 4983230072969 + 3 ^ 40 * 501999 * 2
def baseEnd_501999 : Nat := 257766775076486660303855

theorem tailTrace_501999 : CollatzResearch.WordTrace tailWord_501999 prefixEnd_501999 257766775076486660303855 := by
  unfold tailWord_501999
  simp only [CollatzResearch.WordTrace]
  refine ⟨18309407708350832448629051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12206271805567221632419367 18309407708350832448629051)
  ·
    refine ⟨27464111562526248672943577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18309407708350832448629051 27464111562526248672943577)
    ·
      refine ⟨20598083671894686504707683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27464111562526248672943577 20598083671894686504707683)
      ·
        refine ⟨30897125507842029757061525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20598083671894686504707683 30897125507842029757061525)
        ·
          refine ⟨1448302758180095144862259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 30897125507842029757061525 1448302758180095144862259)
          ·
            refine ⟨2172454137270142717293389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1448302758180095144862259 2172454137270142717293389)
            ·
              refine ⟨814670301476303518985021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2172454137270142717293389 814670301476303518985021)
              ·
                refine ⟨305501363053613819619383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 814670301476303518985021 305501363053613819619383)
                ·
                  refine ⟨458252044580420729429075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 305501363053613819619383 458252044580420729429075)
                  ·
                    refine ⟨687378066870631094143613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 458252044580420729429075 687378066870631094143613)
                    ·
                      refine ⟨257766775076486660303855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 687378066870631094143613 257766775076486660303855)
                      ·
                        rfl

theorem cell23_501999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 3, 3, 1, 1, 3].length) (baseStart_501999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_501999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_501999 prefixEnd_501999 := by exact prefixLift 501999
  have htrace : WordTrace (prefixWord ++ tailWord_501999) baseStart_501999 baseEnd_501999 := by
    simpa [prefixWord, tailWord_501999, baseEnd_501999] using wordTrace_append hprefix tailTrace_501999
  have hstable : (prefixWord ++ tailWord_501999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_501999).length < 2 ^ (prefixWord ++ tailWord_501999).sum := by decide
  have hdescent : baseEnd_501999 < baseStart_501999 := by decide
  rcases family_descends (prefixWord ++ tailWord_501999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502015 : List Nat := [1, 1, 2, 2, 1, 4, 2, 4, 2, 4]
def baseStart_502015 : Nat := 118140960795 + 502015 * 2 ^ 59
def prefixEnd_502015 : Nat := 4983230072969 + 3 ^ 40 * 502015 * 2
def baseEnd_502015 : Nat := 85924996922319532567927

theorem tailTrace_502015 : CollatzResearch.WordTrace tailWord_502015 prefixEnd_502015 85924996922319532567927 := by
  unfold tailWord_502015
  simp only [CollatzResearch.WordTrace]
  refine ⟨18309991276292867181211499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12206660850861911454140999 18309991276292867181211499)
  ·
    refine ⟨27464986914439300771817249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18309991276292867181211499 27464986914439300771817249)
    ·
      refine ⟨20598740185829475578862937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27464986914439300771817249 20598740185829475578862937)
      ·
        refine ⟨15449055139372106684147203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20598740185829475578862937 15449055139372106684147203)
        ·
          refine ⟨23173582709058160026220805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15449055139372106684147203 23173582709058160026220805)
          ·
            refine ⟨4345046757948405004916401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23173582709058160026220805 4345046757948405004916401)
            ·
              refine ⟨3258785068461303753687301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4345046757948405004916401 3258785068461303753687301)
              ·
                refine ⟨611022200336494453816369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3258785068461303753687301 611022200336494453816369)
                ·
                  refine ⟨458266650252370840362277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 611022200336494453816369 458266650252370840362277)
                  ·
                    refine ⟨85924996922319532567927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 458266650252370840362277 85924996922319532567927)
                    ·
                      rfl

theorem cell23_502015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 4, 2, 4].length) (baseStart_502015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_502015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_502015 prefixEnd_502015 := by exact prefixLift 502015
  have htrace : WordTrace (prefixWord ++ tailWord_502015) baseStart_502015 baseEnd_502015 := by
    simpa [prefixWord, tailWord_502015, baseEnd_502015] using wordTrace_append hprefix tailTrace_502015
  have hstable : (prefixWord ++ tailWord_502015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502015).length < 2 ^ (prefixWord ++ tailWord_502015).sum := by decide
  have hdescent : baseEnd_502015 < baseStart_502015 := by decide
  rcases family_descends (prefixWord ++ tailWord_502015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502028 : List Nat := [2, 2, 1, 2, 2, 2, 4, 8]
def baseStart_502028 : Nat := 118140960795 + 502028 * 2 ^ 59
def prefixEnd_502028 : Nat := 4983230072969 + 3 ^ 40 * 502028 * 2
def baseEnd_502028 : Nat := 9547469111683964697823

theorem tailTrace_502028 : CollatzResearch.WordTrace tailWord_502028 prefixEnd_502028 9547469111683964697823 := by
  unfold tailWord_502028
  simp only [CollatzResearch.WordTrace]
  refine ⟨9155232712622885200717369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12206976950163846934289825 9155232712622885200717369)
  ·
    refine ⟨6866424534467163900538027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9155232712622885200717369 6866424534467163900538027)
    ·
      refine ⟨10299636801700745850807041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6866424534467163900538027 10299636801700745850807041)
      ·
        refine ⟨7724727601275559388105281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10299636801700745850807041 7724727601275559388105281)
        ·
          refine ⟨5793545700956669541078961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7724727601275559388105281 5793545700956669541078961)
          ·
            refine ⟨4345159275717502155809221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5793545700956669541078961 4345159275717502155809221)
            ·
              refine ⟨814717364197031654214229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4345159275717502155809221 814717364197031654214229)
              ·
                refine ⟨9547469111683964697823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 814717364197031654214229 9547469111683964697823)
                ·
                  rfl

theorem cell23_502028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 4, 8].length) (baseStart_502028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_502028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_502028 prefixEnd_502028 := by exact prefixLift 502028
  have htrace : WordTrace (prefixWord ++ tailWord_502028) baseStart_502028 baseEnd_502028 := by
    simpa [prefixWord, tailWord_502028, baseEnd_502028] using wordTrace_append hprefix tailTrace_502028
  have hstable : (prefixWord ++ tailWord_502028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502028).length < 2 ^ (prefixWord ++ tailWord_502028).sum := by decide
  have hdescent : baseEnd_502028 < baseStart_502028 := by decide
  rcases family_descends (prefixWord ++ tailWord_502028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502042 : List Nat := [3, 1, 1, 3, 4, 1, 1, 1, 3, 2, 3]
def baseStart_502042 : Nat := 118140960795 + 502042 * 2 ^ 59
def prefixEnd_502042 : Nat := 4983230072969 + 3 ^ 40 * 502042 * 2
def baseEnd_502042 : Nat := 257788854744629992066157

theorem tailTrace_502042 : CollatzResearch.WordTrace tailWord_502042 prefixEnd_502042 257788854744629992066157 := by
  unfold tailWord_502042
  simp only [CollatzResearch.WordTrace]
  refine ⟨4577744011798762698111095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12207317364796700528296253 4577744011798762698111095)
  ·
    refine ⟨6866616017698144047166643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4577744011798762698111095 6866616017698144047166643)
    ·
      refine ⟨10299924026547216070749965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6866616017698144047166643 10299924026547216070749965)
      ·
        refine ⟨3862471509955206026531237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10299924026547216070749965 3862471509955206026531237)
        ·
          refine ⟨724213408116601129974607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3862471509955206026531237 724213408116601129974607)
          ·
            refine ⟨1086320112174901694961911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 724213408116601129974607 1086320112174901694961911)
            ·
              refine ⟨1629480168262352542442867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1086320112174901694961911 1629480168262352542442867)
              ·
                refine ⟨2444220252393528813664301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1629480168262352542442867 2444220252393528813664301)
                ·
                  refine ⟨916582594647573305124113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2444220252393528813664301 916582594647573305124113)
                  ·
                    refine ⟨687436945985679978843085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 916582594647573305124113 687436945985679978843085)
                    ·
                      refine ⟨257788854744629992066157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 687436945985679978843085 257788854744629992066157)
                      ·
                        rfl

theorem cell23_502042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 1, 3, 2, 3].length) (baseStart_502042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_502042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_502042 prefixEnd_502042 := by exact prefixLift 502042
  have htrace : WordTrace (prefixWord ++ tailWord_502042) baseStart_502042 baseEnd_502042 := by
    simpa [prefixWord, tailWord_502042, baseEnd_502042] using wordTrace_append hprefix tailTrace_502042
  have hstable : (prefixWord ++ tailWord_502042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502042).length < 2 ^ (prefixWord ++ tailWord_502042).sum := by decide
  have hdescent : baseEnd_502042 < baseStart_502042 := by decide
  rcases family_descends (prefixWord ++ tailWord_502042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502062 : List Nat := [4, 1, 3, 3, 2, 10]
def baseStart_502062 : Nat := 118140960795 + 502062 * 2 ^ 59
def prefixEnd_502062 : Nat := 4983230072969 + 3 ^ 40 * 502062 * 2
def baseEnd_502062 : Nat := 1060901746328065488955

theorem tailTrace_502062 : CollatzResearch.WordTrace tailWord_502062 prefixEnd_502062 1060901746328065488955 := by
  unfold tailWord_502062
  simp only [CollatzResearch.WordTrace]
  refine ⟨2288963188390324276021555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12207803671415062805448293 2288963188390324276021555)
  ·
    refine ⟨3433444782585486414032333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2288963188390324276021555 3433444782585486414032333)
    ·
      refine ⟨1287541793469557405262125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3433444782585486414032333 1287541793469557405262125)
      ·
        refine ⟨482828172551084026973297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1287541793469557405262125 482828172551084026973297)
        ·
          refine ⟨362121129413313020229973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 482828172551084026973297 362121129413313020229973)
          ·
            refine ⟨1060901746328065488955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 362121129413313020229973 1060901746328065488955)
            ·
              rfl

theorem cell23_502062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 10].length) (baseStart_502062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_502062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_502062 prefixEnd_502062 := by exact prefixLift 502062
  have htrace : WordTrace (prefixWord ++ tailWord_502062) baseStart_502062 baseEnd_502062 := by
    simpa [prefixWord, tailWord_502062, baseEnd_502062] using wordTrace_append hprefix tailTrace_502062
  have hstable : (prefixWord ++ tailWord_502062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502062).length < 2 ^ (prefixWord ++ tailWord_502062).sum := by decide
  have hdescent : baseEnd_502062 < baseStart_502062 := by decide
  rcases family_descends (prefixWord ++ tailWord_502062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502072 : List Nat := [2, 1, 2, 1, 3, 1, 3, 4, 2, 1, 3]
def baseStart_502072 : Nat := 118140960795 + 502072 * 2 ^ 59
def prefixEnd_502072 : Nat := 4983230072969 + 3 ^ 40 * 502072 * 2
def baseEnd_502072 : Nat := 257804259164264874691019

theorem tailTrace_502072 : CollatzResearch.WordTrace tailWord_502072 prefixEnd_502072 257804259164264874691019 := by
  unfold tailWord_502072
  simp only [CollatzResearch.WordTrace]
  refine ⟨9156035118543182958018235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12208046824724243944024313 9156035118543182958018235)
  ·
    refine ⟨13734052677814774437027353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9156035118543182958018235 13734052677814774437027353)
    ·
      refine ⟨10300539508361080827770515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13734052677814774437027353 10300539508361080827770515)
      ·
        refine ⟨15450809262541621241655773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10300539508361080827770515 15450809262541621241655773)
        ·
          refine ⟨5794053473453107965620915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15450809262541621241655773 5794053473453107965620915)
          ·
            refine ⟨8691080210179661948431373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5794053473453107965620915 8691080210179661948431373)
            ·
              refine ⟨3259155078817373230661765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8691080210179661948431373 3259155078817373230661765)
              ·
                refine ⟨611091577278257480749081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3259155078817373230661765 611091577278257480749081)
                ·
                  refine ⟨458318682958693110561811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 611091577278257480749081 458318682958693110561811)
                  ·
                    refine ⟨687478024438039665842717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 458318682958693110561811 687478024438039665842717)
                    ·
                      refine ⟨257804259164264874691019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 687478024438039665842717 257804259164264874691019)
                      ·
                        rfl

theorem cell23_502072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 4, 2, 1, 3].length) (baseStart_502072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_502072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_502072 prefixEnd_502072 := by exact prefixLift 502072
  have htrace : WordTrace (prefixWord ++ tailWord_502072) baseStart_502072 baseEnd_502072 := by
    simpa [prefixWord, tailWord_502072, baseEnd_502072] using wordTrace_append hprefix tailTrace_502072
  have hstable : (prefixWord ++ tailWord_502072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502072).length < 2 ^ (prefixWord ++ tailWord_502072).sum := by decide
  have hdescent : baseEnd_502072 < baseStart_502072 := by decide
  rcases family_descends (prefixWord ++ tailWord_502072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502073 : List Nat := [1, 2, 1, 6, 1, 1, 4, 2, 1, 2, 2]
def baseStart_502073 : Nat := 118140960795 + 502073 * 2 ^ 59
def prefixEnd_502073 : Nat := 4983230072969 + 3 ^ 40 * 502073 * 2
def baseEnd_502073 : Nat := 257804772644919370778515

theorem tailTrace_502073 : CollatzResearch.WordTrace tailWord_502073 prefixEnd_502073 257804772644919370778515 := by
  unfold tailWord_502073
  simp only [CollatzResearch.WordTrace]
  refine ⟨18312106710082743086822873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12208071140055162057881915 18312106710082743086822873)
  ·
    refine ⟨13734080032562057315117155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18312106710082743086822873 13734080032562057315117155)
    ·
      refine ⟨20601120048843085972675733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13734080032562057315117155 20601120048843085972675733)
      ·
        refine ⟨965677502289519654969175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 20601120048843085972675733 965677502289519654969175)
        ·
          refine ⟨1448516253434279482453763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 965677502289519654969175 1448516253434279482453763)
          ·
            refine ⟨2172774380151419223680645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1448516253434279482453763 2172774380151419223680645)
            ·
              refine ⟨407395196278391104440121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2172774380151419223680645 407395196278391104440121)
              ·
                refine ⟨305546397208793328330091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 407395196278391104440121 305546397208793328330091)
                ·
                  refine ⟨458319595813189992495137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 305546397208793328330091 458319595813189992495137)
                  ·
                    refine ⟨343739696859892494371353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 458319595813189992495137 343739696859892494371353)
                    ·
                      refine ⟨257804772644919370778515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 343739696859892494371353 257804772644919370778515)
                      ·
                        rfl

theorem cell23_502073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 4, 2, 1, 2, 2].length) (baseStart_502073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_502073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_502073 prefixEnd_502073 := by exact prefixLift 502073
  have htrace : WordTrace (prefixWord ++ tailWord_502073) baseStart_502073 baseEnd_502073 := by
    simpa [prefixWord, tailWord_502073, baseEnd_502073] using wordTrace_append hprefix tailTrace_502073
  have hstable : (prefixWord ++ tailWord_502073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502073).length < 2 ^ (prefixWord ++ tailWord_502073).sum := by decide
  have hdescent : baseEnd_502073 < baseStart_502073 := by decide
  rcases family_descends (prefixWord ++ tailWord_502073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502088 : List Nat := [2, 1, 3, 1, 1, 2, 3, 1, 1, 8]
def baseStart_502088 : Nat := 118140960795 + 502088 * 2 ^ 59
def prefixEnd_502088 : Nat := 4983230072969 + 3 ^ 40 * 502088 * 2
def baseEnd_502088 : Nat := 85937491618245604030315

theorem tailTrace_502088 : CollatzResearch.WordTrace tailWord_502088 prefixEnd_502088 85937491618245604030315 := by
  unfold tailWord_502088
  simp only [CollatzResearch.WordTrace]
  refine ⟨9156326902514200324309459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12208435870018933765745945 9156326902514200324309459)
  ·
    refine ⟨13734490353771300486464189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9156326902514200324309459 13734490353771300486464189)
    ·
      refine ⟨5150433882664237682424071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13734490353771300486464189 5150433882664237682424071)
      ·
        refine ⟨7725650823996356523636107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5150433882664237682424071 7725650823996356523636107)
        ·
          refine ⟨11588476235994534785454161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7725650823996356523636107 11588476235994534785454161)
          ·
            refine ⟨8691357176995901089090621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11588476235994534785454161 8691357176995901089090621)
            ·
              refine ⟨3259258941373462908408983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8691357176995901089090621 3259258941373462908408983)
              ·
                refine ⟨4888888412060194362613475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3259258941373462908408983 4888888412060194362613475)
                ·
                  refine ⟨7333332618090291543920213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4888888412060194362613475 7333332618090291543920213)
                  ·
                    refine ⟨85937491618245604030315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 7333332618090291543920213 85937491618245604030315)
                    ·
                      rfl

theorem cell23_502088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 1, 1, 8].length) (baseStart_502088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_502088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_502088 prefixEnd_502088 := by exact prefixLift 502088
  have htrace : WordTrace (prefixWord ++ tailWord_502088) baseStart_502088 baseEnd_502088 := by
    simpa [prefixWord, tailWord_502088, baseEnd_502088] using wordTrace_append hprefix tailTrace_502088
  have hstable : (prefixWord ++ tailWord_502088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502088).length < 2 ^ (prefixWord ++ tailWord_502088).sum := by decide
  have hdescent : baseEnd_502088 < baseStart_502088 := by decide
  rcases family_descends (prefixWord ++ tailWord_502088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502110 : List Nat := [4, 4, 2, 1, 1, 1, 1, 3, 1, 2, 3]
def baseStart_502110 : Nat := 118140960795 + 502110 * 2 ^ 59
def prefixEnd_502110 : Nat := 4983230072969 + 3 ^ 40 * 502110 * 2
def baseEnd_502110 : Nat := 257823771429135726015845

theorem tailTrace_502110 : CollatzResearch.WordTrace tailWord_502110 prefixEnd_502110 257823771429135726015845 := by
  unfold tailWord_502110
  simp only [CollatzResearch.WordTrace]
  refine ⟨2289182026368587300739973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12208970807299132270613189 2289182026368587300739973)
  ·
    refine ⟨429221629944110118888745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2289182026368587300739973 429221629944110118888745)
    ·
      refine ⟨321916222458082589166559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 429221629944110118888745 321916222458082589166559)
      ·
        refine ⟨482874333687123883749839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321916222458082589166559 482874333687123883749839)
        ·
          refine ⟨724311500530685825624759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 482874333687123883749839 724311500530685825624759)
          ·
            refine ⟨1086467250796028738437139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 724311500530685825624759 1086467250796028738437139)
            ·
              refine ⟨1629700876194043107655709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1086467250796028738437139 1629700876194043107655709)
              ·
                refine ⟨611137828572766165370891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1629700876194043107655709 611137828572766165370891)
                ·
                  refine ⟨916706742859149248056337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 611137828572766165370891 916706742859149248056337)
                  ·
                    refine ⟨687530057144361936042253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 916706742859149248056337 687530057144361936042253)
                    ·
                      refine ⟨257823771429135726015845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 687530057144361936042253 257823771429135726015845)
                      ·
                        rfl

theorem cell23_502110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_502110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_502110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_502110 prefixEnd_502110 := by exact prefixLift 502110
  have htrace : WordTrace (prefixWord ++ tailWord_502110) baseStart_502110 baseEnd_502110 := by
    simpa [prefixWord, tailWord_502110, baseEnd_502110] using wordTrace_append hprefix tailTrace_502110
  have hstable : (prefixWord ++ tailWord_502110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502110).length < 2 ^ (prefixWord ++ tailWord_502110).sum := by decide
  have hdescent : baseEnd_502110 < baseStart_502110 := by decide
  rcases family_descends (prefixWord ++ tailWord_502110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502125 : List Nat := [1, 5, 1, 1, 1, 2, 1, 1, 4, 2, 4]
def baseStart_502125 : Nat := 118140960795 + 502125 * 2 ^ 59
def prefixEnd_502125 : Nat := 4983230072969 + 3 ^ 40 * 502125 * 2
def baseEnd_502125 : Nat := 257831473638953167328275

theorem tailTrace_502125 : CollatzResearch.WordTrace tailWord_502125 prefixEnd_502125 257831473638953167328275 := by
  unfold tailWord_502125
  simp only [CollatzResearch.WordTrace]
  refine ⟨18314003305894355967715829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12209335537262903978477219 18314003305894355967715829)
  ·
    refine ⟨1716937809927595871973359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18314003305894355967715829 1716937809927595871973359)
    ·
      refine ⟨2575406714891393807960039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1716937809927595871973359 2575406714891393807960039)
      ·
        refine ⟨3863110072337090711940059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2575406714891393807960039 3863110072337090711940059)
        ·
          refine ⟨5794665108505636067910089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3863110072337090711940059 5794665108505636067910089)
          ·
            refine ⟨4345998831379227050932567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5794665108505636067910089 4345998831379227050932567)
            ·
              refine ⟨6518998247068840576398851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4345998831379227050932567 6518998247068840576398851)
              ·
                refine ⟨9778497370603260864598277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6518998247068840576398851 9778497370603260864598277)
                ·
                  refine ⟨1833468256988111412112177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9778497370603260864598277 1833468256988111412112177)
                  ·
                    refine ⟨1375101192741083559084133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1833468256988111412112177 1375101192741083559084133)
                    ·
                      refine ⟨257831473638953167328275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1375101192741083559084133 257831473638953167328275)
                      ·
                        rfl

theorem cell23_502125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 1, 4, 2, 4].length) (baseStart_502125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_502125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_502125 prefixEnd_502125 := by exact prefixLift 502125
  have htrace : WordTrace (prefixWord ++ tailWord_502125) baseStart_502125 baseEnd_502125 := by
    simpa [prefixWord, tailWord_502125, baseEnd_502125] using wordTrace_append hprefix tailTrace_502125
  have hstable : (prefixWord ++ tailWord_502125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502125).length < 2 ^ (prefixWord ++ tailWord_502125).sum := by decide
  have hdescent : baseEnd_502125 < baseStart_502125 := by decide
  rcases family_descends (prefixWord ++ tailWord_502125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502138 : List Nat := [3, 1, 1, 1, 1, 1, 2, 1, 1, 3, 8]
def baseStart_502138 : Nat := 118140960795 + 502138 * 2 ^ 59
def prefixEnd_502138 : Nat := 4983230072969 + 3 ^ 40 * 502138 * 2
def baseEnd_502138 : Nat := 257838148887461616465715

theorem tailTrace_502138 : CollatzResearch.WordTrace tailWord_502138 prefixEnd_502138 257838148887461616465715 := by
  unfold tailWord_502138
  simp only [CollatzResearch.WordTrace]
  refine ⟨4578619363711814796984767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12209651636564839458626045 4578619363711814796984767)
  ·
    refine ⟨6867929045567722195477151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4578619363711814796984767 6867929045567722195477151)
    ·
      refine ⟨10301893568351583293215727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6867929045567722195477151 10301893568351583293215727)
      ·
        refine ⟨15452840352527374939823591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10301893568351583293215727 15452840352527374939823591)
        ·
          refine ⟨23179260528791062409735387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15452840352527374939823591 23179260528791062409735387)
          ·
            refine ⟨34768890793186593614603081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23179260528791062409735387 34768890793186593614603081)
            ·
              refine ⟨26076668094889945210952311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34768890793186593614603081 26076668094889945210952311)
              ·
                refine ⟨39115002142334917816428467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26076668094889945210952311 39115002142334917816428467)
                ·
                  refine ⟨58672503213502376724642701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39115002142334917816428467 58672503213502376724642701)
                  ·
                    refine ⟨22002188705063391271741013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58672503213502376724642701 22002188705063391271741013)
                    ·
                      refine ⟨257838148887461616465715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 22002188705063391271741013 257838148887461616465715)
                      ·
                        rfl

theorem cell23_502138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 1, 3, 8].length) (baseStart_502138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_502138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_502138 prefixEnd_502138 := by exact prefixLift 502138
  have htrace : WordTrace (prefixWord ++ tailWord_502138) baseStart_502138 baseEnd_502138 := by
    simpa [prefixWord, tailWord_502138, baseEnd_502138] using wordTrace_append hprefix tailTrace_502138
  have hstable : (prefixWord ++ tailWord_502138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502138).length < 2 ^ (prefixWord ++ tailWord_502138).sum := by decide
  have hdescent : baseEnd_502138 < baseStart_502138 := by decide
  rcases family_descends (prefixWord ++ tailWord_502138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502165 : List Nat := [1, 3, 2, 1, 1, 2, 1, 5, 2, 5]
def baseStart_502165 : Nat := 118140960795 + 502165 * 2 ^ 59
def prefixEnd_502165 : Nat := 4983230072969 + 3 ^ 40 * 502165 * 2
def baseEnd_502165 : Nat := 85950670955044336942697

theorem tailTrace_502165 : CollatzResearch.WordTrace tailWord_502165 prefixEnd_502165 85950670955044336942697 := by
  unfold tailWord_502165
  simp only [CollatzResearch.WordTrace]
  refine ⟨18315462225749442799171949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12210308150499628532781299 18315462225749442799171949)
  ·
    refine ⟨6868298334656041049689481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18315462225749442799171949 6868298334656041049689481)
    ·
      refine ⟨5151223750992030787267111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6868298334656041049689481 5151223750992030787267111)
      ·
        refine ⟨7726835626488046180900667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5151223750992030787267111 7726835626488046180900667)
        ·
          refine ⟨11590253439732069271351001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7726835626488046180900667 11590253439732069271351001)
          ·
            refine ⟨8692690079799051953513251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11590253439732069271351001 8692690079799051953513251)
            ·
              refine ⟨13039035119698577930269877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8692690079799051953513251 13039035119698577930269877)
              ·
                refine ⟨1222409542471741680962801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13039035119698577930269877 1222409542471741680962801)
                ·
                  refine ⟨916807156853806260722101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1222409542471741680962801 916807156853806260722101)
                  ·
                    refine ⟨85950670955044336942697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 916807156853806260722101 85950670955044336942697)
                    ·
                      rfl

theorem cell23_502165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 5, 2, 5].length) (baseStart_502165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_502165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_502165 prefixEnd_502165 := by exact prefixLift 502165
  have htrace : WordTrace (prefixWord ++ tailWord_502165) baseStart_502165 baseEnd_502165 := by
    simpa [prefixWord, tailWord_502165, baseEnd_502165] using wordTrace_append hprefix tailTrace_502165
  have hstable : (prefixWord ++ tailWord_502165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502165).length < 2 ^ (prefixWord ++ tailWord_502165).sum := by decide
  have hdescent : baseEnd_502165 < baseStart_502165 := by decide
  rcases family_descends (prefixWord ++ tailWord_502165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502175 : List Nat := [1, 1, 2, 5, 1, 1, 2, 2, 1, 2, 5]
def baseStart_502175 : Nat := 118140960795 + 502175 * 2 ^ 59
def prefixEnd_502175 : Nat := 4983230072969 + 3 ^ 40 * 502175 * 2
def baseEnd_502175 : Nat := 257857147671677971703045

theorem tailTrace_502175 : CollatzResearch.WordTrace tailWord_502175 prefixEnd_502175 257857147671677971703045 := by
  unfold tailWord_502175
  simp only [CollatzResearch.WordTrace]
  refine ⟨18315826955713214507035979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12210551303808809671357319 18315826955713214507035979)
  ·
    refine ⟨27473740433569821760553969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18315826955713214507035979 27473740433569821760553969)
    ·
      refine ⟨20605305325177366320415477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27473740433569821760553969 20605305325177366320415477)
      ·
        refine ⟨1931747374235378092538951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20605305325177366320415477 1931747374235378092538951)
        ·
          refine ⟨2897621061353067138808427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1931747374235378092538951 2897621061353067138808427)
          ·
            refine ⟨4346431592029600708212641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2897621061353067138808427 4346431592029600708212641)
            ·
              refine ⟨3259823694022200531159481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4346431592029600708212641 3259823694022200531159481)
              ·
                refine ⟨2444867770516650398369611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3259823694022200531159481 2444867770516650398369611)
                ·
                  refine ⟨3667301655774975597554417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2444867770516650398369611 3667301655774975597554417)
                  ·
                    refine ⟨2750476241831231698165813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3667301655774975597554417 2750476241831231698165813)
                    ·
                      refine ⟨257857147671677971703045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2750476241831231698165813 257857147671677971703045)
                      ·
                        rfl

theorem cell23_502175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_502175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_502175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_502175 prefixEnd_502175 := by exact prefixLift 502175
  have htrace : WordTrace (prefixWord ++ tailWord_502175) baseStart_502175 baseEnd_502175 := by
    simpa [prefixWord, tailWord_502175, baseEnd_502175] using wordTrace_append hprefix tailTrace_502175
  have hstable : (prefixWord ++ tailWord_502175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502175).length < 2 ^ (prefixWord ++ tailWord_502175).sum := by decide
  have hdescent : baseEnd_502175 < baseStart_502175 := by decide
  rcases family_descends (prefixWord ++ tailWord_502175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502202 : List Nat := [3, 1, 1, 1, 2, 1, 1, 5, 2, 4, 2]
def baseStart_502202 : Nat := 118140960795 + 502202 * 2 ^ 59
def prefixEnd_502202 : Nat := 4983230072969 + 3 ^ 40 * 502202 * 2
def baseEnd_502202 : Nat := 257871011649349366065421

theorem tailTrace_502202 : CollatzResearch.WordTrace tailWord_502202 prefixEnd_502202 257871011649349366065421 := by
  unfold tailWord_502202
  simp only [CollatzResearch.WordTrace]
  refine ⟨4579202931653849529567215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12211207817743598745512573 4579202931653849529567215)
  ·
    refine ⟨6868804397480774294350823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4579202931653849529567215 6868804397480774294350823)
    ·
      refine ⟨10303206596221161441526235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6868804397480774294350823 10303206596221161441526235)
      ·
        refine ⟨15454809894331742162289353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10303206596221161441526235 15454809894331742162289353)
        ·
          refine ⟨11591107420748806621717015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15454809894331742162289353 11591107420748806621717015)
          ·
            refine ⟨17386661131123209932575523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11591107420748806621717015 17386661131123209932575523)
            ·
              refine ⟨26079991696684814898863285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17386661131123209932575523 26079991696684814898863285)
              ·
                refine ⟨2444999221564201396768433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26079991696684814898863285 2444999221564201396768433)
                ·
                  refine ⟨1833749416173151047576325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2444999221564201396768433 1833749416173151047576325)
                  ·
                    refine ⟨343828015532465821420561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1833749416173151047576325 343828015532465821420561)
                    ·
                      refine ⟨257871011649349366065421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 343828015532465821420561 257871011649349366065421)
                      ·
                        rfl

theorem cell23_502202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 5, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 5, 2, 4, 2].length) (baseStart_502202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_502202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_502202 prefixEnd_502202 := by exact prefixLift 502202
  have htrace : WordTrace (prefixWord ++ tailWord_502202) baseStart_502202 baseEnd_502202 := by
    simpa [prefixWord, tailWord_502202, baseEnd_502202] using wordTrace_append hprefix tailTrace_502202
  have hstable : (prefixWord ++ tailWord_502202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502202).length < 2 ^ (prefixWord ++ tailWord_502202).sum := by decide
  have hdescent : baseEnd_502202 < baseStart_502202 := by decide
  rcases family_descends (prefixWord ++ tailWord_502202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502269 : List Nat := [1, 4, 1, 1, 1, 3, 3, 2, 3, 1, 3]
def baseStart_502269 : Nat := 118140960795 + 502269 * 2 ^ 59
def prefixEnd_502269 : Nat := 4983230072969 + 3 ^ 40 * 502269 * 2
def baseEnd_502269 : Nat := 257905414853200603927613

theorem tailTrace_502269 : CollatzResearch.WordTrace tailWord_502269 prefixEnd_502269 257905414853200603927613 := by
  unfold tailWord_502269
  simp only [CollatzResearch.WordTrace]
  refine ⟨18319255417372668560957861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12212836944915112373971907 18319255417372668560957861)
  ·
    refine ⟨3434860390757375355179599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18319255417372668560957861 3434860390757375355179599)
    ·
      refine ⟨5152290586136063032769399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3434860390757375355179599 5152290586136063032769399)
      ·
        refine ⟨7728435879204094549154099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5152290586136063032769399 7728435879204094549154099)
        ·
          refine ⟨11592653818806141823731149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7728435879204094549154099 11592653818806141823731149)
          ·
            refine ⟨4347245182052303183899181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11592653818806141823731149 4347245182052303183899181)
            ·
              refine ⟨1630216943269613693962193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4347245182052303183899181 1630216943269613693962193)
              ·
                refine ⟨1222662707452210270471645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1630216943269613693962193 1222662707452210270471645)
                ·
                  refine ⟨458498515294578851426867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1222662707452210270471645 458498515294578851426867)
                  ·
                    refine ⟨687747772941868277140301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 458498515294578851426867 687747772941868277140301)
                    ·
                      refine ⟨257905414853200603927613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 687747772941868277140301 257905414853200603927613)
                      ·
                        rfl

theorem cell23_502269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 2, 3, 1, 3].length) (baseStart_502269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_502269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_502269 prefixEnd_502269 := by exact prefixLift 502269
  have htrace : WordTrace (prefixWord ++ tailWord_502269) baseStart_502269 baseEnd_502269 := by
    simpa [prefixWord, tailWord_502269, baseEnd_502269] using wordTrace_append hprefix tailTrace_502269
  have hstable : (prefixWord ++ tailWord_502269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502269).length < 2 ^ (prefixWord ++ tailWord_502269).sum := by decide
  have hdescent : baseEnd_502269 < baseStart_502269 := by decide
  rcases family_descends (prefixWord ++ tailWord_502269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502326 : List Nat := [5, 1, 2, 1, 2, 1, 1, 4, 1, 1, 4]
def baseStart_502326 : Nat := 118140960795 + 502326 * 2 ^ 59
def prefixEnd_502326 : Nat := 4983230072969 + 3 ^ 40 * 502326 * 2
def baseEnd_502326 : Nat := 257934683250506880914851

theorem tailTrace_502326 : CollatzResearch.WordTrace tailWord_502326 prefixEnd_502326 257934683250506880914851 := by
  unfold tailWord_502326
  simp only [CollatzResearch.WordTrace]
  refine ⟨1145083398635385455986427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12214222918777444863855221 1145083398635385455986427)
  ·
    refine ⟨1717625097953078183979641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1145083398635385455986427 1717625097953078183979641)
    ·
      refine ⟨1288218823464808637984731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1717625097953078183979641 1288218823464808637984731)
      ·
        refine ⟨1932328235197212956977097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1288218823464808637984731 1932328235197212956977097)
        ·
          refine ⟨1449246176397909717732823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1932328235197212956977097 1449246176397909717732823)
          ·
            refine ⟨2173869264596864576599235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1449246176397909717732823 2173869264596864576599235)
            ·
              refine ⟨3260803896895296864898853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2173869264596864576599235 3260803896895296864898853)
              ·
                refine ⟨611400730667868162168535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3260803896895296864898853 611400730667868162168535)
                ·
                  refine ⟨917101096001802243252803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 611400730667868162168535 917101096001802243252803)
                  ·
                    refine ⟨1375651644002703364879205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 917101096001802243252803 1375651644002703364879205)
                    ·
                      refine ⟨257934683250506880914851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1375651644002703364879205 257934683250506880914851)
                      ·
                        rfl

theorem cell23_502326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 4, 1, 1, 4].length) (baseStart_502326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_502326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_502326 prefixEnd_502326 := by exact prefixLift 502326
  have htrace : WordTrace (prefixWord ++ tailWord_502326) baseStart_502326 baseEnd_502326 := by
    simpa [prefixWord, tailWord_502326, baseEnd_502326] using wordTrace_append hprefix tailTrace_502326
  have hstable : (prefixWord ++ tailWord_502326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502326).length < 2 ^ (prefixWord ++ tailWord_502326).sum := by decide
  have hdescent : baseEnd_502326 < baseStart_502326 := by decide
  rcases family_descends (prefixWord ++ tailWord_502326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502332 : List Nat := [2, 2, 2, 2, 3, 2, 1, 9]
def baseStart_502332 : Nat := 118140960795 + 502332 * 2 ^ 59
def prefixEnd_502332 : Nat := 4983230072969 + 3 ^ 40 * 502332 * 2
def baseEnd_502332 : Nat := 9553250523497550275549

theorem tailTrace_502332 : CollatzResearch.WordTrace tailWord_502332 prefixEnd_502332 9553250523497550275549 := by
  unfold tailWord_502332
  simp only [CollatzResearch.WordTrace]
  refine ⟨9160776608072215160250625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12214368810762953547000833 9160776608072215160250625)
  ·
    refine ⟨6870582456054161370187969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9160776608072215160250625 6870582456054161370187969)
    ·
      refine ⟨5152936842040621027640977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6870582456054161370187969 5152936842040621027640977)
      ·
        refine ⟨3864702631530465770730733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5152936842040621027640977 3864702631530465770730733)
        ·
          refine ⟨1449263486823924664024025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3864702631530465770730733 1449263486823924664024025)
          ·
            refine ⟨1086947615117943498018019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1449263486823924664024025 1086947615117943498018019)
            ·
              refine ⟨1630421422676915247027029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1086947615117943498018019 1630421422676915247027029)
              ·
                refine ⟨9553250523497550275549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1630421422676915247027029 9553250523497550275549)
                ·
                  rfl

theorem cell23_502332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 9].length) (baseStart_502332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_502332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_502332 prefixEnd_502332 := by exact prefixLift 502332
  have htrace : WordTrace (prefixWord ++ tailWord_502332) baseStart_502332 baseEnd_502332 := by
    simpa [prefixWord, tailWord_502332, baseEnd_502332] using wordTrace_append hprefix tailTrace_502332
  have hstable : (prefixWord ++ tailWord_502332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502332).length < 2 ^ (prefixWord ++ tailWord_502332).sum := by decide
  have hdescent : baseEnd_502332 < baseStart_502332 := by decide
  rcases family_descends (prefixWord ++ tailWord_502332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502345 : List Nat := [1, 2, 1, 1, 2, 2, 1, 1, 3, 9]
def baseStart_502345 : Nat := 118140960795 + 502345 * 2 ^ 59
def prefixEnd_502345 : Nat := 4983230072969 + 3 ^ 40 * 502345 * 2
def baseEnd_502345 : Nat := 85981479794314102192421

theorem tailTrace_502345 : CollatzResearch.WordTrace tailWord_502345 prefixEnd_502345 85981479794314102192421 := by
  unfold tailWord_502345
  simp only [CollatzResearch.WordTrace]
  refine ⟨18322027365097333540724489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12214684910064889027149659 18322027365097333540724489)
  ·
    refine ⟨13741520523823000155543367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18322027365097333540724489 13741520523823000155543367)
    ·
      refine ⟨20612280785734500233315051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13741520523823000155543367 20612280785734500233315051)
      ·
        refine ⟨30918421178601750349972577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20612280785734500233315051 30918421178601750349972577)
        ·
          refine ⟨23188815883951312762479433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30918421178601750349972577 23188815883951312762479433)
          ·
            refine ⟨17391611912963484571859575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23188815883951312762479433 17391611912963484571859575)
            ·
              refine ⟨26087417869445226857789363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17391611912963484571859575 26087417869445226857789363)
              ·
                refine ⟨39131126804167840286684045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26087417869445226857789363 39131126804167840286684045)
                ·
                  refine ⟨14674172551562940107506517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39131126804167840286684045 14674172551562940107506517)
                  ·
                    refine ⟨85981479794314102192421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 14674172551562940107506517 85981479794314102192421)
                    ·
                      rfl

theorem cell23_502345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 9].length) (baseStart_502345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_502345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_502345 prefixEnd_502345 := by exact prefixLift 502345
  have htrace : WordTrace (prefixWord ++ tailWord_502345) baseStart_502345 baseEnd_502345 := by
    simpa [prefixWord, tailWord_502345, baseEnd_502345] using wordTrace_append hprefix tailTrace_502345
  have hstable : (prefixWord ++ tailWord_502345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502345).length < 2 ^ (prefixWord ++ tailWord_502345).sum := by decide
  have hdescent : baseEnd_502345 < baseStart_502345 := by decide
  rcases family_descends (prefixWord ++ tailWord_502345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502349 : List Nat := [1, 6, 1, 1, 2, 3, 9]
def baseStart_502349 : Nat := 118140960795 + 502349 * 2 ^ 59
def prefixEnd_502349 : Nat := 4983230072969 + 3 ^ 40 * 502349 * 2
def baseEnd_502349 : Nat := 3184524608710620875645

theorem tailTrace_502349 : CollatzResearch.WordTrace tailWord_502349 prefixEnd_502349 3184524608710620875645 := by
  unfold tailWord_502349
  simp only [CollatzResearch.WordTrace]
  refine ⟨18322173257082842223870101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12214782171388561482580067 18322173257082842223870101)
  ·
    refine ⟨858851871425758229243911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 18322173257082842223870101 858851871425758229243911)
    ·
      refine ⟨1288277807138637343865867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 858851871425758229243911 1288277807138637343865867)
      ·
        refine ⟨1932416710707956015798801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1288277807138637343865867 1932416710707956015798801)
        ·
          refine ⟨1449312533030967011849101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1932416710707956015798801 1449312533030967011849101)
          ·
            refine ⟨543492199886612629443413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1449312533030967011849101 543492199886612629443413)
            ·
              refine ⟨3184524608710620875645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 543492199886612629443413 3184524608710620875645)
              ·
                rfl

theorem cell23_502349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 9].length) (baseStart_502349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_502349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_502349 prefixEnd_502349 := by exact prefixLift 502349
  have htrace : WordTrace (prefixWord ++ tailWord_502349) baseStart_502349 baseEnd_502349 := by
    simpa [prefixWord, tailWord_502349, baseEnd_502349] using wordTrace_append hprefix tailTrace_502349
  have hstable : (prefixWord ++ tailWord_502349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502349).length < 2 ^ (prefixWord ++ tailWord_502349).sum := by decide
  have hdescent : baseEnd_502349 < baseStart_502349 := by decide
  rcases family_descends (prefixWord ++ tailWord_502349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502355 : List Nat := [1, 1, 1, 2, 1, 1, 2, 1, 1, 5, 7]
def baseStart_502355 : Nat := 118140960795 + 502355 * 2 ^ 59
def prefixEnd_502355 : Nat := 4983230072969 + 3 ^ 40 * 502355 * 2
def baseEnd_502355 : Nat := 257949574189487267452217

theorem tailTrace_502355 : CollatzResearch.WordTrace tailWord_502355 prefixEnd_502355 257949574189487267452217 := by
  unfold tailWord_502355
  simp only [CollatzResearch.WordTrace]
  refine ⟨18322392095061105248588519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12214928063374070165725679 18322392095061105248588519)
  ·
    refine ⟨27483588142591657872882779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18322392095061105248588519 27483588142591657872882779)
    ·
      refine ⟨41225382213887486809324169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27483588142591657872882779 41225382213887486809324169)
      ·
        refine ⟨30919036660415615106993127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41225382213887486809324169 30919036660415615106993127)
        ·
          refine ⟨46378554990623422660489691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30919036660415615106993127 46378554990623422660489691)
          ·
            refine ⟨69567832485935133990734537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46378554990623422660489691 69567832485935133990734537)
            ·
              refine ⟨52175874364451350493050903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69567832485935133990734537 52175874364451350493050903)
              ·
                refine ⟨78263811546677025739576355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52175874364451350493050903 78263811546677025739576355)
                ·
                  refine ⟨117395717320015538609364533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78263811546677025739576355 117395717320015538609364533)
                  ·
                    refine ⟨11005848498751456744627925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 117395717320015538609364533 11005848498751456744627925)
                    ·
                      refine ⟨257949574189487267452217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 11005848498751456744627925 257949574189487267452217)
                      ·
                        rfl

theorem cell23_502355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 5, 7].length) (baseStart_502355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_502355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_502355 prefixEnd_502355 := by exact prefixLift 502355
  have htrace : WordTrace (prefixWord ++ tailWord_502355) baseStart_502355 baseEnd_502355 := by
    simpa [prefixWord, tailWord_502355, baseEnd_502355] using wordTrace_append hprefix tailTrace_502355
  have hstable : (prefixWord ++ tailWord_502355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502355).length < 2 ^ (prefixWord ++ tailWord_502355).sum := by decide
  have hdescent : baseEnd_502355 < baseStart_502355 := by decide
  rcases family_descends (prefixWord ++ tailWord_502355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502359 : List Nat := [1, 1, 3, 2, 2, 2, 1, 3, 4, 1, 3]
def baseStart_502359 : Nat := 118140960795 + 502359 * 2 ^ 59
def prefixEnd_502359 : Nat := 4983230072969 + 3 ^ 40 * 502359 * 2
def baseEnd_502359 : Nat := 257951628112105251802199

theorem tailTrace_502359 : CollatzResearch.WordTrace tailWord_502359 prefixEnd_502359 257951628112105251802199 := by
  unfold tailWord_502359
  simp only [CollatzResearch.WordTrace]
  refine ⟨18322537987046613931734131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12215025324697742621156087 18322537987046613931734131)
  ·
    refine ⟨27483806980569920897601197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18322537987046613931734131 27483806980569920897601197)
    ·
      refine ⟨10306427617713720336600449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27483806980569920897601197 10306427617713720336600449)
      ·
        refine ⟨7729820713285290252450337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10306427617713720336600449 7729820713285290252450337)
        ·
          refine ⟨5797365534963967689337753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7729820713285290252450337 5797365534963967689337753)
          ·
            refine ⟨4348024151222975767003315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5797365534963967689337753 4348024151222975767003315)
            ·
              refine ⟨6522036226834463650504973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4348024151222975767003315 6522036226834463650504973)
              ·
                refine ⟨2445763585062923868939365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6522036226834463650504973 2445763585062923868939365)
                ·
                  refine ⟨458580672199298225426131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2445763585062923868939365 458580672199298225426131)
                  ·
                    refine ⟨687871008298947338139197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 458580672199298225426131 687871008298947338139197)
                    ·
                      refine ⟨257951628112105251802199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 687871008298947338139197 257951628112105251802199)
                      ·
                        rfl

theorem cell23_502359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 3, 4, 1, 3].length) (baseStart_502359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_502359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_502359 prefixEnd_502359 := by exact prefixLift 502359
  have htrace : WordTrace (prefixWord ++ tailWord_502359) baseStart_502359 baseEnd_502359 := by
    simpa [prefixWord, tailWord_502359, baseEnd_502359] using wordTrace_append hprefix tailTrace_502359
  have hstable : (prefixWord ++ tailWord_502359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502359).length < 2 ^ (prefixWord ++ tailWord_502359).sum := by decide
  have hdescent : baseEnd_502359 < baseStart_502359 := by decide
  rcases family_descends (prefixWord ++ tailWord_502359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502426 : List Nat := [3, 1, 1, 6, 1, 1, 1, 1, 2, 6]
def baseStart_502426 : Nat := 118140960795 + 502426 * 2 ^ 59
def prefixEnd_502426 : Nat := 4983230072969 + 3 ^ 40 * 502426 * 2
def baseEnd_502426 : Nat := 85995343771985496554797

theorem tailTrace_502426 : CollatzResearch.WordTrace tailWord_502426 prefixEnd_502426 85995343771985496554797 := by
  unfold tailWord_502426
  simp only [CollatzResearch.WordTrace]
  refine ⟨4581245419450971093605783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12216654451869256249615421 4581245419450971093605783)
  ·
    refine ⟨6871868129176456640408675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4581245419450971093605783 6871868129176456640408675)
    ·
      refine ⟨10307802193764684960613013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6871868129176456640408675 10307802193764684960613013)
      ·
        refine ⟨483178227832719607528735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 10307802193764684960613013 483178227832719607528735)
        ·
          refine ⟨724767341749079411293103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 483178227832719607528735 724767341749079411293103)
          ·
            refine ⟨1087151012623619116939655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 724767341749079411293103 1087151012623619116939655)
            ·
              refine ⟨1630726518935428675409483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1087151012623619116939655 1630726518935428675409483)
              ·
                refine ⟨2446089778403143013114225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1630726518935428675409483 2446089778403143013114225)
                ·
                  refine ⟨1834567333802357259835669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2446089778403143013114225 1834567333802357259835669)
                  ·
                    refine ⟨85995343771985496554797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1834567333802357259835669 85995343771985496554797)
                    ·
                      rfl

theorem cell23_502426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 1, 2, 6].length) (baseStart_502426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_502426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_502426 prefixEnd_502426 := by exact prefixLift 502426
  have htrace : WordTrace (prefixWord ++ tailWord_502426) baseStart_502426 baseEnd_502426 := by
    simpa [prefixWord, tailWord_502426, baseEnd_502426] using wordTrace_append hprefix tailTrace_502426
  have hstable : (prefixWord ++ tailWord_502426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502426).length < 2 ^ (prefixWord ++ tailWord_502426).sum := by decide
  have hdescent : baseEnd_502426 < baseStart_502426 := by decide
  rcases family_descends (prefixWord ++ tailWord_502426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502433 : List Nat := [1, 2, 3, 3, 3, 1, 2, 1, 1, 4, 2]
def baseStart_502433 : Nat := 118140960795 + 502433 * 2 ^ 59
def prefixEnd_502433 : Nat := 4983230072969 + 3 ^ 40 * 502433 * 2
def baseEnd_502433 : Nat := 257989625680537962276859

theorem tailTrace_502433 : CollatzResearch.WordTrace tailWord_502433 prefixEnd_502433 257989625680537962276859 := by
  unfold tailWord_502433
  simp only [CollatzResearch.WordTrace]
  refine ⟨18325236988778524569927953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12216824659185683046618635 18325236988778524569927953)
  ·
    refine ⟨13743927741583893427445965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18325236988778524569927953 13743927741583893427445965)
    ·
      refine ⟨5153972903093960035292237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13743927741583893427445965 5153972903093960035292237)
      ·
        refine ⟨1932739838660235013234589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5153972903093960035292237 1932739838660235013234589)
        ·
          refine ⟨724777439497588129962971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1932739838660235013234589 724777439497588129962971)
          ·
            refine ⟨1087166159246382194944457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 724777439497588129962971 1087166159246382194944457)
            ·
              refine ⟨815374619434786646208343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1087166159246382194944457 815374619434786646208343)
              ·
                refine ⟨1223061929152179969312515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 815374619434786646208343 1223061929152179969312515)
                ·
                  refine ⟨1834592893728269953968773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1223061929152179969312515 1834592893728269953968773)
                  ·
                    refine ⟨343986167574050616369145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1834592893728269953968773 343986167574050616369145)
                    ·
                      refine ⟨257989625680537962276859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 343986167574050616369145 257989625680537962276859)
                      ·
                        rfl

theorem cell23_502433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 2, 1, 1, 4, 2].length) (baseStart_502433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_502433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_502433 prefixEnd_502433 := by exact prefixLift 502433
  have htrace : WordTrace (prefixWord ++ tailWord_502433) baseStart_502433 baseEnd_502433 := by
    simpa [prefixWord, tailWord_502433, baseEnd_502433] using wordTrace_append hprefix tailTrace_502433
  have hstable : (prefixWord ++ tailWord_502433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502433).length < 2 ^ (prefixWord ++ tailWord_502433).sum := by decide
  have hdescent : baseEnd_502433 < baseStart_502433 := by decide
  rcases family_descends (prefixWord ++ tailWord_502433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502454 : List Nat := [5, 1, 3, 1, 2, 2, 2, 1, 1, 3, 2]
def baseStart_502454 : Nat := 118140960795 + 502454 * 2 ^ 59
def prefixEnd_502454 : Nat := 4983230072969 + 3 ^ 40 * 502454 * 2
def baseEnd_502454 : Nat := 258000408774282380114263

theorem tailTrace_502454 : CollatzResearch.WordTrace tailWord_502454 prefixEnd_502454 258000408774282380114263 := by
  unfold tailWord_502454
  simp only [CollatzResearch.WordTrace]
  refine ⟨1145375182606402822277651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12217335281134963437628277 1145375182606402822277651)
  ·
    refine ⟨1718062773909604233416477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1145375182606402822277651 1718062773909604233416477)
    ·
      refine ⟨644273540216101587531179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1718062773909604233416477 644273540216101587531179)
      ·
        refine ⟨966410310324152381296769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 644273540216101587531179 966410310324152381296769)
        ·
          refine ⟨724807732743114285972577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 966410310324152381296769 724807732743114285972577)
          ·
            refine ⟨543605799557335714479433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 724807732743114285972577 543605799557335714479433)
            ·
              refine ⟨407704349668001785859575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 543605799557335714479433 407704349668001785859575)
              ·
                refine ⟨611556524502002678789363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 407704349668001785859575 611556524502002678789363)
                ·
                  refine ⟨917334786753004018184045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 611556524502002678789363 917334786753004018184045)
                  ·
                    refine ⟨344000545032376506819017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 917334786753004018184045 344000545032376506819017)
                    ·
                      refine ⟨258000408774282380114263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 344000545032376506819017 258000408774282380114263)
                      ·
                        rfl

theorem cell23_502454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 2, 1, 1, 3, 2].length) (baseStart_502454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_502454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_502454 prefixEnd_502454 := by exact prefixLift 502454
  have htrace : WordTrace (prefixWord ++ tailWord_502454) baseStart_502454 baseEnd_502454 := by
    simpa [prefixWord, tailWord_502454, baseEnd_502454] using wordTrace_append hprefix tailTrace_502454
  have hstable : (prefixWord ++ tailWord_502454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502454).length < 2 ^ (prefixWord ++ tailWord_502454).sum := by decide
  have hdescent : baseEnd_502454 < baseStart_502454 := by decide
  rcases family_descends (prefixWord ++ tailWord_502454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502512 : List Nat := [2, 1, 1, 1, 3, 1, 3, 1, 10]
def baseStart_502512 : Nat := 118140960795 + 502512 * 2 ^ 59
def prefixEnd_502512 : Nat := 4983230072969 + 3 ^ 40 * 502512 * 2
def baseEnd_502512 : Nat := 28670021183582572576555

theorem tailTrace_502512 : CollatzResearch.WordTrace tailWord_502512 prefixEnd_502512 28670021183582572576555 := by
  unfold tailWord_502512
  simp only [CollatzResearch.WordTrace]
  refine ⟨9164059177746160531026895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12218745570328214041369193 9164059177746160531026895)
  ·
    refine ⟨13746088766619240796540343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9164059177746160531026895 13746088766619240796540343)
    ·
      refine ⟨20619133149928861194810515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13746088766619240796540343 20619133149928861194810515)
      ·
        refine ⟨30928699724893291792215773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20619133149928861194810515 30928699724893291792215773)
        ·
          refine ⟨11598262396834984422080915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30928699724893291792215773 11598262396834984422080915)
          ·
            refine ⟨17397393595252476633121373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11598262396834984422080915 17397393595252476633121373)
            ·
              refine ⟨6524022598219678737420515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17397393595252476633121373 6524022598219678737420515)
              ·
                refine ⟨9786033897329518106130773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6524022598219678737420515 9786033897329518106130773)
                ·
                  refine ⟨28670021183582572576555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 9786033897329518106130773 28670021183582572576555)
                  ·
                    rfl

theorem cell23_502512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 10].length) (baseStart_502512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_502512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_502512 prefixEnd_502512 := by exact prefixLift 502512
  have htrace : WordTrace (prefixWord ++ tailWord_502512) baseStart_502512 baseEnd_502512 := by
    simpa [prefixWord, tailWord_502512, baseEnd_502512] using wordTrace_append hprefix tailTrace_502512
  have hstable : (prefixWord ++ tailWord_502512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502512).length < 2 ^ (prefixWord ++ tailWord_502512).sum := by decide
  have hdescent : baseEnd_502512 < baseStart_502512 := by decide
  rcases family_descends (prefixWord ++ tailWord_502512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502529 : List Nat := [1, 2, 4, 1, 1, 1, 1, 6, 6]
def baseStart_502529 : Nat := 118140960795 + 502529 * 2 ^ 59
def prefixEnd_502529 : Nat := 4983230072969 + 3 ^ 40 * 502529 * 2
def baseEnd_502529 : Nat := 28670991091485509630713

theorem tailTrace_502529 : CollatzResearch.WordTrace tailWord_502529 prefixEnd_502529 28670991091485509630713 := by
  unfold tailWord_502529
  simp only [CollatzResearch.WordTrace]
  refine ⟨18328738396430732965422641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12219158930953821976948427 18328738396430732965422641)
  ·
    refine ⟨13746553797323049724066981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18328738396430732965422641 13746553797323049724066981)
    ·
      refine ⟨2577478836998071823262559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13746553797323049724066981 2577478836998071823262559)
      ·
        refine ⟨3866218255497107734893839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2577478836998071823262559 3866218255497107734893839)
        ·
          refine ⟨5799327383245661602340759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3866218255497107734893839 5799327383245661602340759)
          ·
            refine ⟨8698991074868492403511139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5799327383245661602340759 8698991074868492403511139)
            ·
              refine ⟨13048486612302738605266709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8698991074868492403511139 13048486612302738605266709)
              ·
                refine ⟨611647809951690872121877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13048486612302738605266709 611647809951690872121877)
                ·
                  refine ⟨28670991091485509630713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 611647809951690872121877 28670991091485509630713)
                  ·
                    rfl

theorem cell23_502529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 6, 6].length) (baseStart_502529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_502529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_502529 prefixEnd_502529 := by exact prefixLift 502529
  have htrace : WordTrace (prefixWord ++ tailWord_502529) baseStart_502529 baseEnd_502529 := by
    simpa [prefixWord, tailWord_502529, baseEnd_502529] using wordTrace_append hprefix tailTrace_502529
  have hstable : (prefixWord ++ tailWord_502529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502529).length < 2 ^ (prefixWord ++ tailWord_502529).sum := by decide
  have hdescent : baseEnd_502529 < baseStart_502529 := by decide
  rcases family_descends (prefixWord ++ tailWord_502529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502599 : List Nat := [1, 1, 4, 1, 2, 1, 1, 3, 3, 1, 5]
def baseStart_502599 : Nat := 118140960795 + 502599 * 2 ^ 59
def prefixEnd_502599 : Nat := 4983230072969 + 3 ^ 40 * 502599 * 2
def baseEnd_502599 : Nat := 258074863469184312801095

theorem tailTrace_502599 : CollatzResearch.WordTrace tailWord_502599 prefixEnd_502599 258074863469184312801095 := by
  unfold tailWord_502599
  simp only [CollatzResearch.WordTrace]
  refine ⟨18331291506177134920470851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12220861004118089946980567 18331291506177134920470851)
  ·
    refine ⟨27496937259265702380706277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18331291506177134920470851 27496937259265702380706277)
    ·
      refine ⟨5155675736112319196382427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27496937259265702380706277 5155675736112319196382427)
      ·
        refine ⟨7733513604168478794573641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5155675736112319196382427 7733513604168478794573641)
        ·
          refine ⟨5800135203126359095930231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7733513604168478794573641 5800135203126359095930231)
          ·
            refine ⟨8700202804689538643895347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5800135203126359095930231 8700202804689538643895347)
            ·
              refine ⟨13050304207034307965843021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8700202804689538643895347 13050304207034307965843021)
              ·
                refine ⟨4893864077637865487191133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13050304207034307965843021 4893864077637865487191133)
                ·
                  refine ⟨1835199029114199557696675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4893864077637865487191133 1835199029114199557696675)
                  ·
                    refine ⟨2752798543671299336545013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1835199029114199557696675 2752798543671299336545013)
                    ·
                      refine ⟨258074863469184312801095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2752798543671299336545013 258074863469184312801095)
                      ·
                        rfl

theorem cell23_502599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 3, 3, 1, 5].length) (baseStart_502599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_502599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_502599 prefixEnd_502599 := by exact prefixLift 502599
  have htrace : WordTrace (prefixWord ++ tailWord_502599) baseStart_502599 baseEnd_502599 := by
    simpa [prefixWord, tailWord_502599, baseEnd_502599] using wordTrace_append hprefix tailTrace_502599
  have hstable : (prefixWord ++ tailWord_502599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502599).length < 2 ^ (prefixWord ++ tailWord_502599).sum := by decide
  have hdescent : baseEnd_502599 < baseStart_502599 := by decide
  rcases family_descends (prefixWord ++ tailWord_502599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502656 : List Nat := [2, 1, 1, 2, 1, 2, 2, 1, 2, 7, 2]
def baseStart_502656 : Nat := 118140960795 + 502656 * 2 ^ 59
def prefixEnd_502656 : Nat := 4983230072969 + 3 ^ 40 * 502656 * 2
def baseEnd_502656 : Nat := 258104131866490589788333

theorem tailTrace_502656 : CollatzResearch.WordTrace tailWord_502656 prefixEnd_502656 258104131866490589788333 := by
  unfold tailWord_502656
  simp only [CollatzResearch.WordTrace]
  refine ⟨9166685233485316827647911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12222246977980422436863881 9166685233485316827647911)
  ·
    refine ⟨13750027850227975241471867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9166685233485316827647911 13750027850227975241471867)
    ·
      refine ⟨20625041775341962862207801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13750027850227975241471867 20625041775341962862207801)
      ·
        refine ⟨15468781331506472146655851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20625041775341962862207801 15468781331506472146655851)
        ·
          refine ⟨23203171997259708219983777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15468781331506472146655851 23203171997259708219983777)
          ·
            refine ⟨17402378997944781164987833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23203171997259708219983777 17402378997944781164987833)
            ·
              refine ⟨13051784248458585873740875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17402378997944781164987833 13051784248458585873740875)
              ·
                refine ⟨19577676372687878810611313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13051784248458585873740875 19577676372687878810611313)
                ·
                  refine ⟨14683257279515909107958485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19577676372687878810611313 14683257279515909107958485)
                  ·
                    refine ⟨344138842488654119717777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 14683257279515909107958485 344138842488654119717777)
                    ·
                      refine ⟨258104131866490589788333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 344138842488654119717777 258104131866490589788333)
                      ·
                        rfl

theorem cell23_502656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 2, 7, 2].length) (baseStart_502656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_502656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_502656 prefixEnd_502656 := by exact prefixLift 502656
  have htrace : WordTrace (prefixWord ++ tailWord_502656) baseStart_502656 baseEnd_502656 := by
    simpa [prefixWord, tailWord_502656, baseEnd_502656] using wordTrace_append hprefix tailTrace_502656
  have hstable : (prefixWord ++ tailWord_502656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502656).length < 2 ^ (prefixWord ++ tailWord_502656).sum := by decide
  have hdescent : baseEnd_502656 < baseStart_502656 := by decide
  rcases family_descends (prefixWord ++ tailWord_502656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502663 : List Nat := [1, 1, 4, 2, 3, 1, 3, 1, 1, 3, 3]
def baseStart_502663 : Nat := 118140960795 + 502663 * 2 ^ 59
def prefixEnd_502663 : Nat := 4983230072969 + 3 ^ 40 * 502663 * 2
def baseEnd_502663 : Nat := 258107726231072062400801

theorem tailTrace_502663 : CollatzResearch.WordTrace tailWord_502663 prefixEnd_502663 258107726231072062400801 := by
  unfold tailWord_502663
  simp only [CollatzResearch.WordTrace]
  refine ⟨18333625777945273850800643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12222417185296849233867095 18333625777945273850800643)
  ·
    refine ⟨27500438666917910776200965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18333625777945273850800643 27500438666917910776200965)
    ·
      refine ⟨5156332250047108270537681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27500438666917910776200965 5156332250047108270537681)
      ·
        refine ⟨3867249187535331202903261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5156332250047108270537681 3867249187535331202903261)
        ·
          refine ⟨1450218445325749201088723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3867249187535331202903261 1450218445325749201088723)
          ·
            refine ⟨2175327667988623801633085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1450218445325749201088723 2175327667988623801633085)
            ·
              refine ⟨815747875495733925612407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2175327667988623801633085 815747875495733925612407)
              ·
                refine ⟨1223621813243600888418611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 815747875495733925612407 1223621813243600888418611)
                ·
                  refine ⟨1835432719865401332627917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1223621813243600888418611 1835432719865401332627917)
                  ·
                    refine ⟨688287269949525499735469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1835432719865401332627917 688287269949525499735469)
                    ·
                      refine ⟨258107726231072062400801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 688287269949525499735469 258107726231072062400801)
                      ·
                        rfl

theorem cell23_502663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 3, 1, 1, 3, 3].length) (baseStart_502663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_502663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_502663 prefixEnd_502663 := by exact prefixLift 502663
  have htrace : WordTrace (prefixWord ++ tailWord_502663) baseStart_502663 baseEnd_502663 := by
    simpa [prefixWord, tailWord_502663, baseEnd_502663] using wordTrace_append hprefix tailTrace_502663
  have hstable : (prefixWord ++ tailWord_502663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502663).length < 2 ^ (prefixWord ++ tailWord_502663).sum := by decide
  have hdescent : baseEnd_502663 < baseStart_502663 := by decide
  rcases family_descends (prefixWord ++ tailWord_502663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502676 : List Nat := [2, 4, 2, 1, 1, 1, 1, 1, 1, 4, 5]
def baseStart_502676 : Nat := 118140960795 + 502676 * 2 ^ 59
def prefixEnd_502676 : Nat := 4983230072969 + 3 ^ 40 * 502676 * 2
def baseEnd_502676 : Nat := 258114401479580511538241

theorem tailTrace_502676 : CollatzResearch.WordTrace tailWord_502676 prefixEnd_502676 258114401479580511538241 := by
  unfold tailWord_502676
  simp only [CollatzResearch.WordTrace]
  refine ⟨9167049963449088535511941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12222733284598784714015921 9167049963449088535511941)
  ·
    refine ⟨1718821868146704100408489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9167049963449088535511941 1718821868146704100408489)
    ·
      refine ⟨1289116401110028075306367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1718821868146704100408489 1289116401110028075306367)
      ·
        refine ⟨1933674601665042112959551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1289116401110028075306367 1933674601665042112959551)
        ·
          refine ⟨2900511902497563169439327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1933674601665042112959551 2900511902497563169439327)
          ·
            refine ⟨4350767853746344754158991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2900511902497563169439327 4350767853746344754158991)
            ·
              refine ⟨6526151780619517131238487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4350767853746344754158991 6526151780619517131238487)
              ·
                refine ⟨9789227670929275696857731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6526151780619517131238487 9789227670929275696857731)
                ·
                  refine ⟨14683841506393913545286597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9789227670929275696857731 14683841506393913545286597)
                  ·
                    refine ⟨2753220282448858789741237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14683841506393913545286597 2753220282448858789741237)
                    ·
                      refine ⟨258114401479580511538241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2753220282448858789741237 258114401479580511538241)
                      ·
                        rfl

theorem cell23_502676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_502676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_502676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_502676 prefixEnd_502676 := by exact prefixLift 502676
  have htrace : WordTrace (prefixWord ++ tailWord_502676) baseStart_502676 baseEnd_502676 := by
    simpa [prefixWord, tailWord_502676, baseEnd_502676] using wordTrace_append hprefix tailTrace_502676
  have hstable : (prefixWord ++ tailWord_502676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502676).length < 2 ^ (prefixWord ++ tailWord_502676).sum := by decide
  have hdescent : baseEnd_502676 < baseStart_502676 := by decide
  rcases family_descends (prefixWord ++ tailWord_502676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502736 : List Nat := [2, 1, 1, 1, 1, 2, 3, 2, 4, 3, 3]
def baseStart_502736 : Nat := 118140960795 + 502736 * 2 ^ 59
def prefixEnd_502736 : Nat := 4983230072969 + 3 ^ 40 * 502736 * 2
def baseEnd_502736 : Nat := 258145210318850276787965

theorem tailTrace_502736 : CollatzResearch.WordTrace tailWord_502736 prefixEnd_502736 258145210318850276787965 := by
  unfold tailWord_502736
  simp only [CollatzResearch.WordTrace]
  refine ⟨9168144153340403659104031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12224192204453871545472041 9168144153340403659104031)
  ·
    refine ⟨13752216230010605488656047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9168144153340403659104031 13752216230010605488656047)
    ·
      refine ⟨20628324345015908232984071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13752216230010605488656047 20628324345015908232984071)
      ·
        refine ⟨30942486517523862349476107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20628324345015908232984071 30942486517523862349476107)
        ·
          refine ⟨46413729776285793524214161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30942486517523862349476107 46413729776285793524214161)
          ·
            refine ⟨34810297332214345143160621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46413729776285793524214161 34810297332214345143160621)
            ·
              refine ⟨13053861499580379428685233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34810297332214345143160621 13053861499580379428685233)
              ·
                refine ⟨9790396124685284571513925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13053861499580379428685233 9790396124685284571513925)
                ·
                  refine ⟨1835699273378490857158861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9790396124685284571513925 1835699273378490857158861)
                  ·
                    refine ⟨688387227516934071434573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1835699273378490857158861 688387227516934071434573)
                    ·
                      refine ⟨258145210318850276787965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 688387227516934071434573 258145210318850276787965)
                      ·
                        rfl

theorem cell23_502736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 4, 3, 3].length) (baseStart_502736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_502736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_502736 prefixEnd_502736 := by exact prefixLift 502736
  have htrace : WordTrace (prefixWord ++ tailWord_502736) baseStart_502736 baseEnd_502736 := by
    simpa [prefixWord, tailWord_502736, baseEnd_502736] using wordTrace_append hprefix tailTrace_502736
  have hstable : (prefixWord ++ tailWord_502736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502736).length < 2 ^ (prefixWord ++ tailWord_502736).sum := by decide
  have hdescent : baseEnd_502736 < baseStart_502736 := by decide
  rcases family_descends (prefixWord ++ tailWord_502736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502754 : List Nat := [3, 3, 3, 1, 1, 1, 1, 4, 2, 2, 2]
def baseStart_502754 : Nat := 118140960795 + 502754 * 2 ^ 59
def prefixEnd_502754 : Nat := 4983230072969 + 3 ^ 40 * 502754 * 2
def baseEnd_502754 : Nat := 258154452970631206362883

theorem tailTrace_502754 : CollatzResearch.WordTrace tailWord_502754 prefixEnd_502754 258154452970631206362883 := by
  unfold tailWord_502754
  simp only [CollatzResearch.WordTrace]
  refine ⟨4584236205153899098090829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12224629880410397594908877 4584236205153899098090829)
  ·
    refine ⟨1719088576932712161784061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4584236205153899098090829 1719088576932712161784061)
    ·
      refine ⟨644658216349767060669023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1719088576932712161784061 644658216349767060669023)
      ·
        refine ⟨966987324524650591003535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 644658216349767060669023 966987324524650591003535)
        ·
          refine ⟨1450480986786975886505303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 966987324524650591003535 1450480986786975886505303)
          ·
            refine ⟨2175721480180463829757955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1450480986786975886505303 2175721480180463829757955)
            ·
              refine ⟨3263582220270695744636933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2175721480180463829757955 3263582220270695744636933)
              ·
                refine ⟨611921666300755452119425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3263582220270695744636933 611921666300755452119425)
                ·
                  refine ⟨458941249725566589089569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 611921666300755452119425 458941249725566589089569)
                  ·
                    refine ⟨344205937294174941817177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 458941249725566589089569 344205937294174941817177)
                    ·
                      refine ⟨258154452970631206362883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 344205937294174941817177 258154452970631206362883)
                      ·
                        rfl

theorem cell23_502754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 4, 2, 2, 2].length) (baseStart_502754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_502754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_502754 prefixEnd_502754 := by exact prefixLift 502754
  have htrace : WordTrace (prefixWord ++ tailWord_502754) baseStart_502754 baseEnd_502754 := by
    simpa [prefixWord, tailWord_502754, baseEnd_502754] using wordTrace_append hprefix tailTrace_502754
  have hstable : (prefixWord ++ tailWord_502754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502754).length < 2 ^ (prefixWord ++ tailWord_502754).sum := by decide
  have hdescent : baseEnd_502754 < baseStart_502754 := by decide
  rcases family_descends (prefixWord ++ tailWord_502754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502756 : List Nat := [2, 3, 1, 1, 1, 1, 2, 3, 4, 5]
def baseStart_502756 : Nat := 118140960795 + 502756 * 2 ^ 59
def prefixEnd_502756 : Nat := 4983230072969 + 3 ^ 40 * 502756 * 2
def baseEnd_502756 : Nat := 86051826643980066179291

theorem tailTrace_502756 : CollatzResearch.WordTrace tailWord_502756 prefixEnd_502756 86051826643980066179291 := by
  unfold tailWord_502756
  simp only [CollatzResearch.WordTrace]
  refine ⟨9168508883304175366968061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12224678511072233822624081 9168508883304175366968061)
  ·
    refine ⟨3438190831239065762613023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9168508883304175366968061 3438190831239065762613023)
    ·
      refine ⟨5157286246858598643919535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3438190831239065762613023 5157286246858598643919535)
      ·
        refine ⟨7735929370287897965879303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5157286246858598643919535 7735929370287897965879303)
        ·
          refine ⟨11603894055431846948818955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7735929370287897965879303 11603894055431846948818955)
          ·
            refine ⟨17405841083147770423228433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11603894055431846948818955 17405841083147770423228433)
            ·
              refine ⟨13054380812360827817421325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17405841083147770423228433 13054380812360827817421325)
              ·
                refine ⟨4895392804635310431532997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13054380812360827817421325 4895392804635310431532997)
                ·
                  refine ⟨917886150869120705912437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4895392804635310431532997 917886150869120705912437)
                  ·
                    refine ⟨86051826643980066179291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 917886150869120705912437 86051826643980066179291)
                    ·
                      rfl

theorem cell23_502756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 3, 4, 5].length) (baseStart_502756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_502756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_502756 prefixEnd_502756 := by exact prefixLift 502756
  have htrace : WordTrace (prefixWord ++ tailWord_502756) baseStart_502756 baseEnd_502756 := by
    simpa [prefixWord, tailWord_502756, baseEnd_502756] using wordTrace_append hprefix tailTrace_502756
  have hstable : (prefixWord ++ tailWord_502756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502756).length < 2 ^ (prefixWord ++ tailWord_502756).sum := by decide
  have hdescent : baseEnd_502756 < baseStart_502756 := by decide
  rcases family_descends (prefixWord ++ tailWord_502756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502760 : List Nat := [2, 1, 4, 1, 1, 1, 6, 2, 5]
def baseStart_502760 : Nat := 118140960795 + 502760 * 2 ^ 59
def prefixEnd_502760 : Nat := 4983230072969 + 3 ^ 40 * 502760 * 2
def baseEnd_502760 : Nat := 28684170428284242543095

theorem tailTrace_502760 : CollatzResearch.WordTrace tailWord_502760 prefixEnd_502760 28684170428284242543095 := by
  unfold tailWord_502760
  simp only [CollatzResearch.WordTrace]
  refine ⟨9168581829296929708540867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12224775772395906278054489 9168581829296929708540867)
  ·
    refine ⟨13752872743945394562811301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9168581829296929708540867 13752872743945394562811301)
    ·
      refine ⟨2578663639489761480527119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13752872743945394562811301 2578663639489761480527119)
      ·
        refine ⟨3867995459234642220790679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2578663639489761480527119 3867995459234642220790679)
        ·
          refine ⟨5801993188851963331186019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3867995459234642220790679 5801993188851963331186019)
          ·
            refine ⟨8702989783277944996779029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5801993188851963331186019 8702989783277944996779029)
            ·
              refine ⟨407952646091153671724017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 8702989783277944996779029 407952646091153671724017)
              ·
                refine ⟨305964484568365253793013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 407952646091153671724017 305964484568365253793013)
                ·
                  refine ⟨28684170428284242543095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 305964484568365253793013 28684170428284242543095)
                  ·
                    rfl

theorem cell23_502760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 6, 2, 5].length) (baseStart_502760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_502760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_502760 prefixEnd_502760 := by exact prefixLift 502760
  have htrace : WordTrace (prefixWord ++ tailWord_502760) baseStart_502760 baseEnd_502760 := by
    simpa [prefixWord, tailWord_502760, baseEnd_502760] using wordTrace_append hprefix tailTrace_502760
  have hstable : (prefixWord ++ tailWord_502760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502760).length < 2 ^ (prefixWord ++ tailWord_502760).sum := by decide
  have hdescent : baseEnd_502760 < baseStart_502760 := by decide
  rcases family_descends (prefixWord ++ tailWord_502760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502776 : List Nat := [2, 1, 2, 1, 1, 3, 1, 4, 1, 3, 4]
def baseStart_502776 : Nat := 118140960795 + 502776 * 2 ^ 59
def prefixEnd_502776 : Nat := 4983230072969 + 3 ^ 40 * 502776 * 2
def baseEnd_502776 : Nat := 258165749545030120287781

theorem tailTrace_502776 : CollatzResearch.WordTrace tailWord_502776 prefixEnd_502776 258165749545030120287781 := by
  unfold tailWord_502776
  simp only [CollatzResearch.WordTrace]
  refine ⟨9168873613267947074832091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12225164817690596099776121 9168873613267947074832091)
  ·
    refine ⟨13753310419901920612248137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9168873613267947074832091 13753310419901920612248137)
    ·
      refine ⟨10314982814926440459186103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13753310419901920612248137 10314982814926440459186103)
      ·
        refine ⟨15472474222389660688779155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10314982814926440459186103 15472474222389660688779155)
        ·
          refine ⟨23208711333584491033168733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15472474222389660688779155 23208711333584491033168733)
          ·
            refine ⟨8703266750094184137438275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23208711333584491033168733 8703266750094184137438275)
            ·
              refine ⟨13054900125141276206157413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8703266750094184137438275 13054900125141276206157413)
              ·
                refine ⟨2447793773463989288654515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13054900125141276206157413 2447793773463989288654515)
                ·
                  refine ⟨3671690660195983932981773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2447793773463989288654515 3671690660195983932981773)
                  ·
                    refine ⟨1376883997573493974868165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3671690660195983932981773 1376883997573493974868165)
                    ·
                      refine ⟨258165749545030120287781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1376883997573493974868165 258165749545030120287781)
                      ·
                        rfl

theorem cell23_502776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 4, 1, 3, 4].length) (baseStart_502776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_502776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_502776 prefixEnd_502776 := by exact prefixLift 502776
  have htrace : WordTrace (prefixWord ++ tailWord_502776) baseStart_502776 baseEnd_502776 := by
    simpa [prefixWord, tailWord_502776, baseEnd_502776] using wordTrace_append hprefix tailTrace_502776
  have hstable : (prefixWord ++ tailWord_502776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502776).length < 2 ^ (prefixWord ++ tailWord_502776).sum := by decide
  have hdescent : baseEnd_502776 < baseStart_502776 := by decide
  rcases family_descends (prefixWord ++ tailWord_502776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502820 : List Nat := [2, 3, 1, 4, 1, 1, 1, 3, 3, 4]
def baseStart_502820 : Nat := 118140960795 + 502820 * 2 ^ 59
def prefixEnd_502820 : Nat := 4983230072969 + 3 ^ 40 * 502820 * 2
def baseEnd_502820 : Nat := 86062780897942649379193

theorem tailTrace_502820 : CollatzResearch.WordTrace tailWord_502820 prefixEnd_502820 86062780897942649379193 := by
  unfold tailWord_502820
  simp only [CollatzResearch.WordTrace]
  refine ⟨9169676019188244832132957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12226234692250993109510609 9169676019188244832132957)
  ·
    refine ⟨3438628507195591812049859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9169676019188244832132957 3438628507195591812049859)
    ·
      refine ⟨5157942760793387718074789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3438628507195591812049859 5157942760793387718074789)
      ·
        refine ⟨967114267648760197139023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5157942760793387718074789 967114267648760197139023)
        ·
          refine ⟨1450671401473140295708535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 967114267648760197139023 1450671401473140295708535)
          ·
            refine ⟨2176007102209710443562803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1450671401473140295708535 2176007102209710443562803)
            ·
              refine ⟨3264010653314565665344205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2176007102209710443562803 3264010653314565665344205)
              ·
                refine ⟨1224003994992962124504077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3264010653314565665344205 1224003994992962124504077)
                ·
                  refine ⟨459001498122360796689029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1224003994992962124504077 459001498122360796689029)
                  ·
                    refine ⟨86062780897942649379193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 459001498122360796689029 86062780897942649379193)
                    ·
                      rfl

theorem cell23_502820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 3, 3, 4].length) (baseStart_502820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_502820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_502820 prefixEnd_502820 := by exact prefixLift 502820
  have htrace : WordTrace (prefixWord ++ tailWord_502820) baseStart_502820 baseEnd_502820 := by
    simpa [prefixWord, tailWord_502820, baseEnd_502820] using wordTrace_append hprefix tailTrace_502820
  have hstable : (prefixWord ++ tailWord_502820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502820).length < 2 ^ (prefixWord ++ tailWord_502820).sum := by decide
  have hdescent : baseEnd_502820 < baseStart_502820 := by decide
  rcases family_descends (prefixWord ++ tailWord_502820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502883 : List Nat := [1, 1, 1, 5, 1, 1, 1, 4, 3, 1, 4]
def baseStart_502883 : Nat := 118140960795 + 502883 * 2 ^ 59
def prefixEnd_502883 : Nat := 4983230072969 + 3 ^ 40 * 502883 * 2
def baseEnd_502883 : Nat := 258220691975061201649789

theorem tailTrace_502883 : CollatzResearch.WordTrace tailWord_502883 prefixEnd_502883 258220691975061201649789 := by
  unfold tailWord_502883
  simp only [CollatzResearch.WordTrace]
  refine ⟨18341649837148251423809303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12227766558098834282539535 18341649837148251423809303)
  ·
    refine ⟨27512474755722377135713955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18341649837148251423809303 27512474755722377135713955)
    ·
      refine ⟨41268712133583565703570933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27512474755722377135713955 41268712133583565703570933)
      ·
        refine ⟨3868941762523459284709775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41268712133583565703570933 3868941762523459284709775)
        ·
          refine ⟨5803412643785188927064663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3868941762523459284709775 5803412643785188927064663)
          ·
            refine ⟨8705118965677783390596995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5803412643785188927064663 8705118965677783390596995)
            ·
              refine ⟨13057678448516675085895493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8705118965677783390596995 13057678448516675085895493)
              ·
                refine ⟨2448314709096876578605405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13057678448516675085895493 2448314709096876578605405)
                ·
                  refine ⟨918118015911328716977027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2448314709096876578605405 918118015911328716977027)
                  ·
                    refine ⟨1377177023866993075465541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 918118015911328716977027 1377177023866993075465541)
                    ·
                      refine ⟨258220691975061201649789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1377177023866993075465541 258220691975061201649789)
                      ·
                        rfl

theorem cell23_502883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 4, 3, 1, 4].length) (baseStart_502883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_502883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_502883 prefixEnd_502883 := by exact prefixLift 502883
  have htrace : WordTrace (prefixWord ++ tailWord_502883) baseStart_502883 baseEnd_502883 := by
    simpa [prefixWord, tailWord_502883, baseEnd_502883] using wordTrace_append hprefix tailTrace_502883
  have hstable : (prefixWord ++ tailWord_502883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502883).length < 2 ^ (prefixWord ++ tailWord_502883).sum := by decide
  have hdescent : baseEnd_502883 < baseStart_502883 := by decide
  rcases family_descends (prefixWord ++ tailWord_502883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502940 : List Nat := [2, 2, 3, 2, 1, 4, 1, 8]
def baseStart_502940 : Nat := 118140960795 + 502940 * 2 ^ 59
def prefixEnd_502940 : Nat := 4983230072969 + 3 ^ 40 * 502940 * 2
def baseEnd_502940 : Nat := 9564813347124721431001

theorem tailTrace_502940 : CollatzResearch.WordTrace tailWord_502940 prefixEnd_502940 9564813347124721431001 := by
  unfold tailWord_502940
  simp only [CollatzResearch.WordTrace]
  refine ⟨9171864398970875079317137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12229152531961166772422849 9171864398970875079317137)
  ·
    refine ⟨6878898299228156309487853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9171864398970875079317137 6878898299228156309487853)
    ·
      refine ⟨2579586862210558616057945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6878898299228156309487853 2579586862210558616057945)
      ·
        refine ⟨1934690146657918962043459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2579586862210558616057945 1934690146657918962043459)
        ·
          refine ⟨2902035219986878443065189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1934690146657918962043459 2902035219986878443065189)
          ·
            refine ⟨544131603747539708074723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2902035219986878443065189 544131603747539708074723)
            ·
              refine ⟨816197405621309562112085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 544131603747539708074723 816197405621309562112085)
              ·
                refine ⟨9564813347124721431001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 816197405621309562112085 9564813347124721431001)
                ·
                  rfl

theorem cell23_502940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 1, 8].length) (baseStart_502940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_502940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_502940 prefixEnd_502940 := by exact prefixLift 502940
  have htrace : WordTrace (prefixWord ++ tailWord_502940) baseStart_502940 baseEnd_502940 := by
    simpa [prefixWord, tailWord_502940, baseEnd_502940] using wordTrace_append hprefix tailTrace_502940
  have hstable : (prefixWord ++ tailWord_502940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502940).length < 2 ^ (prefixWord ++ tailWord_502940).sum := by decide
  have hdescent : baseEnd_502940 < baseStart_502940 := by decide
  rcases family_descends (prefixWord ++ tailWord_502940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502957 : List Nat := [1, 5, 2, 1, 3, 1, 3, 7]
def baseStart_502957 : Nat := 118140960795 + 502957 * 2 ^ 59
def prefixEnd_502957 : Nat := 4983230072969 + 3 ^ 40 * 502957 * 2
def baseEnd_502957 : Nat := 9565136649759033782387

theorem tailTrace_502957 : CollatzResearch.WordTrace tailWord_502957 prefixEnd_502957 9565136649759033782387 := by
  unfold tailWord_502957
  simp only [CollatzResearch.WordTrace]
  refine ⟨18344348838880162062003125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12229565892586774708002083 18344348838880162062003125)
  ·
    refine ⟨1719782703645015193312793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18344348838880162062003125 1719782703645015193312793)
    ·
      refine ⟨1289837027733761394984595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1719782703645015193312793 1289837027733761394984595)
      ·
        refine ⟨1934755541600642092476893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1289837027733761394984595 1934755541600642092476893)
        ·
          refine ⟨725533328100240784678835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1934755541600642092476893 725533328100240784678835)
          ·
            refine ⟨1088299992150361177018253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 725533328100240784678835 1088299992150361177018253)
            ·
              refine ⟨408112497056385441381845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1088299992150361177018253 408112497056385441381845)
              ·
                refine ⟨9565136649759033782387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 408112497056385441381845 9565136649759033782387)
                ·
                  rfl

theorem cell23_502957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 3, 7].length) (baseStart_502957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_502957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_502957 prefixEnd_502957 := by exact prefixLift 502957
  have htrace : WordTrace (prefixWord ++ tailWord_502957) baseStart_502957 baseEnd_502957 := by
    simpa [prefixWord, tailWord_502957, baseEnd_502957] using wordTrace_append hprefix tailTrace_502957
  have hstable : (prefixWord ++ tailWord_502957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502957).length < 2 ^ (prefixWord ++ tailWord_502957).sum := by decide
  have hdescent : baseEnd_502957 < baseStart_502957 := by decide
  rcases family_descends (prefixWord ++ tailWord_502957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502978 : List Nat := [3, 5, 1, 1, 2, 2, 1, 2, 2, 4]
def baseStart_502978 : Nat := 118140960795 + 502978 * 2 ^ 59
def prefixEnd_502978 : Nat := 4983230072969 + 3 ^ 40 * 502978 * 2
def baseEnd_502978 : Nat := 86089824212412776653951

theorem tailTrace_502978 : CollatzResearch.WordTrace tailWord_502978 prefixEnd_502978 86089824212412776653951 := by
  unfold tailWord_502978
  simp only [CollatzResearch.WordTrace]
  refine ⟨4586278692951020662129397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12230076514536055099011725 4586278692951020662129397)
  ·
    refine ⟨429963627464158187074631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4586278692951020662129397 429963627464158187074631)
    ·
      refine ⟨644945441196237280611947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 429963627464158187074631 644945441196237280611947)
      ·
        refine ⟨967418161794355920917921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 644945441196237280611947 967418161794355920917921)
        ·
          refine ⟨725563621345766940688441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 967418161794355920917921 725563621345766940688441)
          ·
            refine ⟨544172716009325205516331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 725563621345766940688441 544172716009325205516331)
            ·
              refine ⟨816259074013987808274497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 544172716009325205516331 816259074013987808274497)
              ·
                refine ⟨612194305510490856205873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 816259074013987808274497 612194305510490856205873)
                ·
                  refine ⟨459145729132868142154405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 612194305510490856205873 459145729132868142154405)
                  ·
                    refine ⟨86089824212412776653951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 459145729132868142154405 86089824212412776653951)
                    ·
                      rfl

theorem cell23_502978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_502978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_502978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_502978 prefixEnd_502978 := by exact prefixLift 502978
  have htrace : WordTrace (prefixWord ++ tailWord_502978) baseStart_502978 baseEnd_502978 := by
    simpa [prefixWord, tailWord_502978, baseEnd_502978] using wordTrace_append hprefix tailTrace_502978
  have hstable : (prefixWord ++ tailWord_502978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502978).length < 2 ^ (prefixWord ++ tailWord_502978).sum := by decide
  have hdescent : baseEnd_502978 < baseStart_502978 := by decide
  rcases family_descends (prefixWord ++ tailWord_502978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_502993 : List Nat := [1, 2, 2, 1, 2, 2, 1, 2, 4, 1, 5]
def baseStart_502993 : Nat := 118140960795 + 502993 * 2 ^ 59
def prefixEnd_502993 : Nat := 4983230072969 + 3 ^ 40 * 502993 * 2
def baseEnd_502993 : Nat := 258277174847055771274283

theorem tailTrace_502993 : CollatzResearch.WordTrace tailWord_502993 prefixEnd_502993 258277174847055771274283 := by
  unfold tailWord_502993
  simp only [CollatzResearch.WordTrace]
  refine ⟨18345661866749740210313633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12230441244499826806875755 18345661866749740210313633)
  ·
    refine ⟨13759246400062305157735225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18345661866749740210313633 13759246400062305157735225)
    ·
      refine ⟨10319434800046728868301419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13759246400062305157735225 10319434800046728868301419)
      ·
        refine ⟨15479152200070093302452129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10319434800046728868301419 15479152200070093302452129)
        ·
          refine ⟨11609364150052569976839097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15479152200070093302452129 11609364150052569976839097)
          ·
            refine ⟨8707023112539427482629323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11609364150052569976839097 8707023112539427482629323)
            ·
              refine ⟨13060534668809141223943985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8707023112539427482629323 13060534668809141223943985)
              ·
                refine ⟨9795401001606855917957989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13060534668809141223943985 9795401001606855917957989)
                ·
                  refine ⟨1836637687801285484617123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9795401001606855917957989 1836637687801285484617123)
                  ·
                    refine ⟨2754956531701928226925685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1836637687801285484617123 2754956531701928226925685)
                    ·
                      refine ⟨258277174847055771274283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2754956531701928226925685 258277174847055771274283)
                      ·
                        rfl

theorem cell23_502993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 4, 1, 5].length) (baseStart_502993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_502993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_502993 prefixEnd_502993 := by exact prefixLift 502993
  have htrace : WordTrace (prefixWord ++ tailWord_502993) baseStart_502993 baseEnd_502993 := by
    simpa [prefixWord, tailWord_502993, baseEnd_502993] using wordTrace_append hprefix tailTrace_502993
  have hstable : (prefixWord ++ tailWord_502993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_502993).length < 2 ^ (prefixWord ++ tailWord_502993).sum := by decide
  have hdescent : baseEnd_502993 < baseStart_502993 := by decide
  rcases family_descends (prefixWord ++ tailWord_502993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503003 : List Nat := [1, 1, 1, 1, 1, 1, 1, 4, 6, 2, 4]
def baseStart_503003 : Nat := 118140960795 + 503003 * 2 ^ 59
def prefixEnd_503003 : Nat := 4983230072969 + 3 ^ 40 * 503003 * 2
def baseEnd_503003 : Nat := 258282309653600732149237

theorem tailTrace_503003 : CollatzResearch.WordTrace tailWord_503003 prefixEnd_503003 258282309653600732149237 := by
  unfold tailWord_503003
  simp only [CollatzResearch.WordTrace]
  refine ⟨18346026596713511918177663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12230684397809007945451775 18346026596713511918177663)
  ·
    refine ⟨27519039895070267877266495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18346026596713511918177663 27519039895070267877266495)
    ·
      refine ⟨41278559842605401815899743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27519039895070267877266495 41278559842605401815899743)
      ·
        refine ⟨61917839763908102723849615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41278559842605401815899743 61917839763908102723849615)
        ·
          refine ⟨92876759645862154085774423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61917839763908102723849615 92876759645862154085774423)
          ·
            refine ⟨139315139468793231128661635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92876759645862154085774423 139315139468793231128661635)
            ·
              refine ⟨208972709203189846692992453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139315139468793231128661635 208972709203189846692992453)
              ·
                refine ⟨39182382975598096254936085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 208972709203189846692992453 39182382975598096254936085)
                ·
                  refine ⟨1836674201981160761950129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 39182382975598096254936085 1836674201981160761950129)
                  ·
                    refine ⟨1377505651485870571462597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1836674201981160761950129 1377505651485870571462597)
                    ·
                      refine ⟨258282309653600732149237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1377505651485870571462597 258282309653600732149237)
                      ·
                        rfl

theorem cell23_503003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 6, 2, 4].length) (baseStart_503003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_503003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_503003 prefixEnd_503003 := by exact prefixLift 503003
  have htrace : WordTrace (prefixWord ++ tailWord_503003) baseStart_503003 baseEnd_503003 := by
    simpa [prefixWord, tailWord_503003, baseEnd_503003] using wordTrace_append hprefix tailTrace_503003
  have hstable : (prefixWord ++ tailWord_503003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503003).length < 2 ^ (prefixWord ++ tailWord_503003).sum := by decide
  have hdescent : baseEnd_503003 < baseStart_503003 := by decide
  rcases family_descends (prefixWord ++ tailWord_503003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503007 : List Nat := [1, 1, 2, 3, 2, 1, 5, 1, 1, 4, 2]
def baseStart_503007 : Nat := 118140960795 + 503007 * 2 ^ 59
def prefixEnd_503007 : Nat := 4983230072969 + 3 ^ 40 * 503007 * 2
def baseEnd_503007 : Nat := 258284363576218716499219

theorem tailTrace_503007 : CollatzResearch.WordTrace tailWord_503007 prefixEnd_503007 258284363576218716499219 := by
  unfold tailWord_503007
  simp only [CollatzResearch.WordTrace]
  refine ⟨18346172488699020601323275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12230781659132680400882183 18346172488699020601323275)
  ·
    refine ⟨27519258733048530901984913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18346172488699020601323275 27519258733048530901984913)
    ·
      refine ⟨20639444049786398176488685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27519258733048530901984913 20639444049786398176488685)
      ·
        refine ⟨7739791518669899316183257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20639444049786398176488685 7739791518669899316183257)
        ·
          refine ⟨5804843639002424487137443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7739791518669899316183257 5804843639002424487137443)
          ·
            refine ⟨8707265458503636730706165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5804843639002424487137443 8707265458503636730706165)
            ·
              refine ⟨816306136734715943503703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8707265458503636730706165 816306136734715943503703)
              ·
                refine ⟨1224459205102073915255555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 816306136734715943503703 1224459205102073915255555)
                ·
                  refine ⟨1836688807653110872883333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1224459205102073915255555 1836688807653110872883333)
                  ·
                    refine ⟨344379151434958288665625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1836688807653110872883333 344379151434958288665625)
                    ·
                      refine ⟨258284363576218716499219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 344379151434958288665625 258284363576218716499219)
                      ·
                        rfl

theorem cell23_503007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 5, 1, 1, 4, 2].length) (baseStart_503007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_503007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_503007 prefixEnd_503007 := by exact prefixLift 503007
  have htrace : WordTrace (prefixWord ++ tailWord_503007) baseStart_503007 baseEnd_503007 := by
    simpa [prefixWord, tailWord_503007, baseEnd_503007] using wordTrace_append hprefix tailTrace_503007
  have hstable : (prefixWord ++ tailWord_503007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503007).length < 2 ^ (prefixWord ++ tailWord_503007).sum := by decide
  have hdescent : baseEnd_503007 < baseStart_503007 := by decide
  rcases family_descends (prefixWord ++ tailWord_503007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503077 : List Nat := [1, 3, 1, 2, 4, 2, 2, 1, 2, 5]
def baseStart_503077 : Nat := 118140960795 + 503077 * 2 ^ 59
def prefixEnd_503077 : Nat := 4983230072969 + 3 ^ 40 * 503077 * 2
def baseEnd_503077 : Nat := 86106769074011147541299

theorem tailTrace_503077 : CollatzResearch.WordTrace tailWord_503077 prefixEnd_503077 86106769074011147541299 := by
  unfold tailWord_503077
  simp only [CollatzResearch.WordTrace]
  refine ⟨18348725598445422556371485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12232483732296948370914323 18348725598445422556371485)
  ·
    refine ⟨6880772099417033458639307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18348725598445422556371485 6880772099417033458639307)
    ·
      refine ⟨10321158149125550187958961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6880772099417033458639307 10321158149125550187958961)
      ·
        refine ⟨7740868611844162640969221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10321158149125550187958961 7740868611844162640969221)
        ·
          refine ⟨1451412864720780495181729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7740868611844162640969221 1451412864720780495181729)
          ·
            refine ⟨1088559648540585371386297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1451412864720780495181729 1088559648540585371386297)
            ·
              refine ⟨816419736405439028539723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1088559648540585371386297 816419736405439028539723)
              ·
                refine ⟨1224629604608158542809585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 816419736405439028539723 1224629604608158542809585)
                ·
                  refine ⟨918472203456118907107189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1224629604608158542809585 918472203456118907107189)
                  ·
                    refine ⟨86106769074011147541299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 918472203456118907107189 86106769074011147541299)
                    ·
                      rfl

theorem cell23_503077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 2, 1, 2, 5].length) (baseStart_503077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_503077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_503077 prefixEnd_503077 := by exact prefixLift 503077
  have htrace : WordTrace (prefixWord ++ tailWord_503077) baseStart_503077 baseEnd_503077 := by
    simpa [prefixWord, tailWord_503077, baseEnd_503077] using wordTrace_append hprefix tailTrace_503077
  have hstable : (prefixWord ++ tailWord_503077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503077).length < 2 ^ (prefixWord ++ tailWord_503077).sum := by decide
  have hdescent : baseEnd_503077 < baseStart_503077 := by decide
  rcases family_descends (prefixWord ++ tailWord_503077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503120 : List Nat := [2, 1, 1, 1, 1, 5, 1, 5, 6]
def baseStart_503120 : Nat := 118140960795 + 503120 * 2 ^ 59
def prefixEnd_503120 : Nat := 4983230072969 + 3 ^ 40 * 503120 * 2
def baseEnd_503120 : Nat := 28704709654464086042911

theorem tailTrace_503120 : CollatzResearch.WordTrace tailWord_503120 prefixEnd_503120 28704709654464086042911 := by
  unfold tailWord_503120
  simp only [CollatzResearch.WordTrace]
  refine ⟨9175146968644820450093407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12233529291526427266791209 9175146968644820450093407)
  ·
    refine ⟨13762720452967230675140111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9175146968644820450093407 13762720452967230675140111)
    ·
      refine ⟨20644080679450846012710167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13762720452967230675140111 20644080679450846012710167)
      ·
        refine ⟨30966121019176269019065251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20644080679450846012710167 30966121019176269019065251)
        ·
          refine ⟨46449181528764403528597877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30966121019176269019065251 46449181528764403528597877)
          ·
            refine ⟨4354610768321662830806051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 46449181528764403528597877 4354610768321662830806051)
            ·
              refine ⟨6531916152482494246209077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4354610768321662830806051 6531916152482494246209077)
              ·
                refine ⟨612367139295233835582101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6531916152482494246209077 612367139295233835582101)
                ·
                  refine ⟨28704709654464086042911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 612367139295233835582101 28704709654464086042911)
                  ·
                    rfl

theorem cell23_503120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 5, 6].length) (baseStart_503120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_503120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_503120 prefixEnd_503120 := by exact prefixLift 503120
  have htrace : WordTrace (prefixWord ++ tailWord_503120) baseStart_503120 baseEnd_503120 := by
    simpa [prefixWord, tailWord_503120, baseEnd_503120] using wordTrace_append hprefix tailTrace_503120
  have hstable : (prefixWord ++ tailWord_503120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503120).length < 2 ^ (prefixWord ++ tailWord_503120).sum := by decide
  have hdescent : baseEnd_503120 < baseStart_503120 := by decide
  rcases family_descends (prefixWord ++ tailWord_503120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503164 : List Nat := [2, 2, 2, 1, 1, 1, 6, 1, 3, 1, 3]
def baseStart_503164 : Nat := 118140960795 + 503164 * 2 ^ 59
def prefixEnd_503164 : Nat := 4983230072969 + 3 ^ 40 * 503164 * 2
def baseEnd_503164 : Nat := 258364980038974602235997

theorem tailTrace_503164 : CollatzResearch.WordTrace tailWord_503164 prefixEnd_503164 258364980038974602235997 := by
  unfold tailWord_503164
  simp only [CollatzResearch.WordTrace]
  refine ⟨9175949374565118207394273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12234599166086824276525697 9175949374565118207394273)
  ·
    refine ⟨6881962030923838655545705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9175949374565118207394273 6881962030923838655545705)
    ·
      refine ⟨5161471523192878991659279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6881962030923838655545705 5161471523192878991659279)
      ·
        refine ⟨7742207284789318487488919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5161471523192878991659279 7742207284789318487488919)
        ·
          refine ⟨11613310927183977731233379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7742207284789318487488919 11613310927183977731233379)
          ·
            refine ⟨17419966390775966596850069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11613310927183977731233379 17419966390775966596850069)
            ·
              refine ⟨816560924567623434227347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 17419966390775966596850069 816560924567623434227347)
              ·
                refine ⟨1224841386851435151341021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 816560924567623434227347 1224841386851435151341021)
                ·
                  refine ⟨459315520069288181752883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1224841386851435151341021 459315520069288181752883)
                  ·
                    refine ⟨688973280103932272629325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 459315520069288181752883 688973280103932272629325)
                    ·
                      refine ⟨258364980038974602235997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 688973280103932272629325 258364980038974602235997)
                      ·
                        rfl

theorem cell23_503164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 6, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 6, 1, 3, 1, 3].length) (baseStart_503164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_503164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_503164 prefixEnd_503164 := by exact prefixLift 503164
  have htrace : WordTrace (prefixWord ++ tailWord_503164) baseStart_503164 baseEnd_503164 := by
    simpa [prefixWord, tailWord_503164, baseEnd_503164] using wordTrace_append hprefix tailTrace_503164
  have hstable : (prefixWord ++ tailWord_503164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503164).length < 2 ^ (prefixWord ++ tailWord_503164).sum := by decide
  have hdescent : baseEnd_503164 < baseStart_503164 := by decide
  rcases family_descends (prefixWord ++ tailWord_503164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503208 : List Nat := [2, 1, 6, 1, 2, 1, 1, 2, 2, 3, 2]
def baseStart_503208 : Nat := 118140960795 + 503208 * 2 ^ 59
def prefixEnd_503208 : Nat := 4983230072969 + 3 ^ 40 * 503208 * 2
def baseEnd_503208 : Nat := 258387573187772430085795

theorem tailTrace_503208 : CollatzResearch.WordTrace tailWord_503208 prefixEnd_503208 258387573187772430085795 := by
  unfold tailWord_503208
  simp only [CollatzResearch.WordTrace]
  refine ⟨9176751780485415964695139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12235669040647221286260185 9176751780485415964695139)
  ·
    refine ⟨13765127670728123947042709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9176751780485415964695139 13765127670728123947042709)
    ·
      refine ⟨645240359565380810017627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 13765127670728123947042709 645240359565380810017627)
      ·
        refine ⟨967860539348071215026441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 645240359565380810017627 967860539348071215026441)
        ·
          refine ⟨725895404511053411269831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 967860539348071215026441 725895404511053411269831)
          ·
            refine ⟨1088843106766580116904747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 725895404511053411269831 1088843106766580116904747)
            ·
              refine ⟨1633264660149870175357121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1088843106766580116904747 1633264660149870175357121)
              ·
                refine ⟨1224948495112402631517841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1633264660149870175357121 1224948495112402631517841)
                ·
                  refine ⟨918711371334301973638381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1224948495112402631517841 918711371334301973638381)
                  ·
                    refine ⟨344516764250363240114393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 918711371334301973638381 344516764250363240114393)
                    ·
                      refine ⟨258387573187772430085795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 344516764250363240114393 258387573187772430085795)
                      ·
                        rfl

theorem cell23_503208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 2, 2, 3, 2].length) (baseStart_503208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_503208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_503208 prefixEnd_503208 := by exact prefixLift 503208
  have htrace : WordTrace (prefixWord ++ tailWord_503208) baseStart_503208 baseEnd_503208 := by
    simpa [prefixWord, tailWord_503208, baseEnd_503208] using wordTrace_append hprefix tailTrace_503208
  have hstable : (prefixWord ++ tailWord_503208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503208).length < 2 ^ (prefixWord ++ tailWord_503208).sum := by decide
  have hdescent : baseEnd_503208 < baseStart_503208 := by decide
  rcases family_descends (prefixWord ++ tailWord_503208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503271 : List Nat := [1, 1, 5, 2, 1, 2, 1, 4, 2, 1, 3]
def baseStart_503271 : Nat := 118140960795 + 503271 * 2 ^ 59
def prefixEnd_503271 : Nat := 4983230072969 + 3 ^ 40 * 503271 * 2
def baseEnd_503271 : Nat := 258419922469005683598005

theorem tailTrace_503271 : CollatzResearch.WordTrace tailWord_503271 prefixEnd_503271 258419922469005683598005 := by
  unfold tailWord_503271
  simp only [CollatzResearch.WordTrace]
  refine ⟨18355801359742593688933667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12237200906495062459289111 18355801359742593688933667)
  ·
    refine ⟨27533702039613890533400501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18355801359742593688933667 27533702039613890533400501)
    ·
      refine ⟨2581284566213802237506297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27533702039613890533400501 2581284566213802237506297)
      ·
        refine ⟨1935963424660351678129723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2581284566213802237506297 1935963424660351678129723)
        ·
          refine ⟨2903945136990527517194585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1935963424660351678129723 2903945136990527517194585)
          ·
            refine ⟨2177958852742895637895939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2903945136990527517194585 2177958852742895637895939)
            ·
              refine ⟨3266938279114343456843909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2177958852742895637895939 3266938279114343456843909)
              ·
                refine ⟨612550927333939398158233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3266938279114343456843909 612550927333939398158233)
                ·
                  refine ⟨459413195500454548618675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 612550927333939398158233 459413195500454548618675)
                  ·
                    refine ⟨689119793250681822928013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 459413195500454548618675 689119793250681822928013)
                    ·
                      refine ⟨258419922469005683598005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 689119793250681822928013 258419922469005683598005)
                      ·
                        rfl

theorem cell23_503271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 4, 2, 1, 3].length) (baseStart_503271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_503271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_503271 prefixEnd_503271 := by exact prefixLift 503271
  have htrace : WordTrace (prefixWord ++ tailWord_503271) baseStart_503271 baseEnd_503271 := by
    simpa [prefixWord, tailWord_503271, baseEnd_503271] using wordTrace_append hprefix tailTrace_503271
  have hstable : (prefixWord ++ tailWord_503271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503271).length < 2 ^ (prefixWord ++ tailWord_503271).sum := by decide
  have hdescent : baseEnd_503271 < baseStart_503271 := by decide
  rcases family_descends (prefixWord ++ tailWord_503271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503298 : List Nat := [3, 4, 1, 2, 1, 1, 2, 1, 3, 3, 2]
def baseStart_503298 : Nat := 118140960795 + 503298 * 2 ^ 59
def prefixEnd_503298 : Nat := 4983230072969 + 3 ^ 40 * 503298 * 2
def baseEnd_503298 : Nat := 258433786446677077960381

theorem tailTrace_503298 : CollatzResearch.WordTrace tailWord_503298 prefixEnd_503298 258433786446677077960381 := by
  unfold tailWord_503298
  simp only [CollatzResearch.WordTrace]
  refine ⟨4589196532661194325041637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12237857420429851533444365 4589196532661194325041637)
  ·
    refine ⟨860474349873973935945307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4589196532661194325041637 860474349873973935945307)
    ·
      refine ⟨1290711524810960903917961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 860474349873973935945307 1290711524810960903917961)
      ·
        refine ⟨968033643608220677938471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1290711524810960903917961 968033643608220677938471)
        ·
          refine ⟨1452050465412331016907707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 968033643608220677938471 1452050465412331016907707)
          ·
            refine ⟨2178075698118496525361561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1452050465412331016907707 2178075698118496525361561)
            ·
              refine ⟨1633556773588872394021171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2178075698118496525361561 1633556773588872394021171)
              ·
                refine ⟨2450335160383308591031757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1633556773588872394021171 2450335160383308591031757)
                ·
                  refine ⟨918875685143740721636909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2450335160383308591031757 918875685143740721636909)
                  ·
                    refine ⟨344578381928902770613841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 918875685143740721636909 344578381928902770613841)
                    ·
                      refine ⟨258433786446677077960381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 344578381928902770613841 258433786446677077960381)
                      ·
                        rfl

theorem cell23_503298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 1, 3, 3, 2].length) (baseStart_503298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_503298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_503298 prefixEnd_503298 := by exact prefixLift 503298
  have htrace : WordTrace (prefixWord ++ tailWord_503298) baseStart_503298 baseEnd_503298 := by
    simpa [prefixWord, tailWord_503298, baseEnd_503298] using wordTrace_append hprefix tailTrace_503298
  have hstable : (prefixWord ++ tailWord_503298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503298).length < 2 ^ (prefixWord ++ tailWord_503298).sum := by decide
  have hdescent : baseEnd_503298 < baseStart_503298 := by decide
  rcases family_descends (prefixWord ++ tailWord_503298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503309 : List Nat := [1, 7, 1, 1, 3, 1, 2, 1, 1, 2, 3]
def baseStart_503309 : Nat := 118140960795 + 503309 * 2 ^ 59
def prefixEnd_503309 : Nat := 4983230072969 + 3 ^ 40 * 503309 * 2
def baseEnd_503309 : Nat := 258439434733876534922831

theorem tailTrace_503309 : CollatzResearch.WordTrace tailWord_503309 prefixEnd_503309 258439434733876534922831 := by
  unfold tailWord_503309
  simp only [CollatzResearch.WordTrace]
  refine ⟨18357187333604926178816981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12238124889069950785877987 18357187333604926178816981)
  ·
    refine ⟨430246578131365457316023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 18357187333604926178816981 430246578131365457316023)
    ·
      refine ⟨645369867197048185974035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 430246578131365457316023 645369867197048185974035)
      ·
        refine ⟨968054800795572278961053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 645369867197048185974035 968054800795572278961053)
        ·
          refine ⟨363020550298339604610395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 968054800795572278961053 363020550298339604610395)
          ·
            refine ⟨544530825447509406915593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 363020550298339604610395 544530825447509406915593)
            ·
              refine ⟨408398119085632055186695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 544530825447509406915593 408398119085632055186695)
              ·
                refine ⟨612597178628448082780043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 408398119085632055186695 612597178628448082780043)
                ·
                  refine ⟨918895767942672124170065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 612597178628448082780043 918895767942672124170065)
                  ·
                    refine ⟨689171825957004093127549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 918895767942672124170065 689171825957004093127549)
                    ·
                      refine ⟨258439434733876534922831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 689171825957004093127549 258439434733876534922831)
                      ·
                        rfl

theorem cell23_503309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 2, 1, 1, 2, 3].length) (baseStart_503309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_503309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_503309 prefixEnd_503309 := by exact prefixLift 503309
  have htrace : WordTrace (prefixWord ++ tailWord_503309) baseStart_503309 baseEnd_503309 := by
    simpa [prefixWord, tailWord_503309, baseEnd_503309] using wordTrace_append hprefix tailTrace_503309
  have hstable : (prefixWord ++ tailWord_503309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503309).length < 2 ^ (prefixWord ++ tailWord_503309).sum := by decide
  have hdescent : baseEnd_503309 < baseStart_503309 := by decide
  rcases family_descends (prefixWord ++ tailWord_503309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503328 : List Nat := [2, 1, 1, 6, 1, 2, 1, 1, 4, 2, 2]
def baseStart_503328 : Nat := 118140960795 + 503328 * 2 ^ 59
def prefixEnd_503328 : Nat := 4983230072969 + 3 ^ 40 * 503328 * 2
def baseEnd_503328 : Nat := 258449190866311960585243

theorem tailTrace_503328 : CollatzResearch.WordTrace tailWord_503328 prefixEnd_503328 258449190866311960585243 := by
  unfold tailWord_503328
  simp only [CollatzResearch.WordTrace]
  refine ⟨9178940160268046211879319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12238586880357394949172425 9178940160268046211879319)
  ·
    refine ⟨13768410240402069317818979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9178940160268046211879319 13768410240402069317818979)
    ·
      refine ⟨20652615360603103976728469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13768410240402069317818979 20652615360603103976728469)
      ·
        refine ⟨968091345028270498909147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 20652615360603103976728469 968091345028270498909147)
        ·
          refine ⟨1452137017542405748363721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 968091345028270498909147 1452137017542405748363721)
          ·
            refine ⟨1089102763156804311272791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1452137017542405748363721 1089102763156804311272791)
            ·
              refine ⟨1633654144735206466909187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1089102763156804311272791 1633654144735206466909187)
              ·
                refine ⟨2450481217102809700363781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1633654144735206466909187 2450481217102809700363781)
                ·
                  refine ⟨459465228206776818818209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2450481217102809700363781 459465228206776818818209)
                  ·
                    refine ⟨344598921155082614113657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 459465228206776818818209 344598921155082614113657)
                    ·
                      refine ⟨258449190866311960585243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 344598921155082614113657 258449190866311960585243)
                      ·
                        rfl

theorem cell23_503328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 1, 4, 2, 2].length) (baseStart_503328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_503328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_503328 prefixEnd_503328 := by exact prefixLift 503328
  have htrace : WordTrace (prefixWord ++ tailWord_503328) baseStart_503328 baseEnd_503328 := by
    simpa [prefixWord, tailWord_503328, baseEnd_503328] using wordTrace_append hprefix tailTrace_503328
  have hstable : (prefixWord ++ tailWord_503328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503328).length < 2 ^ (prefixWord ++ tailWord_503328).sum := by decide
  have hdescent : baseEnd_503328 < baseStart_503328 := by decide
  rcases family_descends (prefixWord ++ tailWord_503328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503347 : List Nat := [1, 1, 1, 2, 4, 3, 1, 2, 1, 7]
def baseStart_503347 : Nat := 118140960795 + 503347 * 2 ^ 59
def prefixEnd_503347 : Nat := 4983230072969 + 3 ^ 40 * 503347 * 2
def baseEnd_503347 : Nat := 86152982332915795415885

theorem tailTrace_503347 : CollatzResearch.WordTrace tailWord_503347 prefixEnd_503347 86152982332915795415885 := by
  unfold tailWord_503347
  simp only [CollatzResearch.WordTrace]
  refine ⟨18358573307467258668700295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12239048871644839112466863 18358573307467258668700295)
  ·
    refine ⟨27537859961200888003050443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18358573307467258668700295 27537859961200888003050443)
    ·
      refine ⟨41306789941801332004575665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27537859961200888003050443 41306789941801332004575665)
      ·
        refine ⟨30980092456350999003431749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41306789941801332004575665 30980092456350999003431749)
        ·
          refine ⟨5808767335565812313143453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30980092456350999003431749 5808767335565812313143453)
          ·
            refine ⟨2178287750837179617428795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5808767335565812313143453 2178287750837179617428795)
            ·
              refine ⟨3267431626255769426143193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2178287750837179617428795 3267431626255769426143193)
              ·
                refine ⟨2450573719691827069607395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3267431626255769426143193 2450573719691827069607395)
                ·
                  refine ⟨3675860579537740604411093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2450573719691827069607395 3675860579537740604411093)
                  ·
                    refine ⟨86152982332915795415885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3675860579537740604411093 86152982332915795415885)
                    ·
                      rfl

theorem cell23_503347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 2, 1, 7].length) (baseStart_503347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_503347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_503347 prefixEnd_503347 := by exact prefixLift 503347
  have htrace : WordTrace (prefixWord ++ tailWord_503347) baseStart_503347 baseEnd_503347 := by
    simpa [prefixWord, tailWord_503347, baseEnd_503347] using wordTrace_append hprefix tailTrace_503347
  have hstable : (prefixWord ++ tailWord_503347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503347).length < 2 ^ (prefixWord ++ tailWord_503347).sum := by decide
  have hdescent : baseEnd_503347 < baseStart_503347 := by decide
  rcases family_descends (prefixWord ++ tailWord_503347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503404 : List Nat := [2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 3]
def baseStart_503404 : Nat := 118140960795 + 503404 * 2 ^ 59
def prefixEnd_503404 : Nat := 4983230072969 + 3 ^ 40 * 503404 * 2
def baseEnd_503404 : Nat := 258488215396053663234893

theorem tailTrace_503404 : CollatzResearch.WordTrace tailWord_503404 prefixEnd_503404 258488215396053663234893 := by
  unfold tailWord_503404
  simp only [CollatzResearch.WordTrace]
  refine ⟨9180326134130378701762633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12240434845507171602350177 9180326134130378701762633)
  ·
    refine ⟨6885244600597784026321975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9180326134130378701762633 6885244600597784026321975)
    ·
      refine ⟨10327866900896676039482963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6885244600597784026321975 10327866900896676039482963)
      ·
        refine ⟨15491800351345014059224445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10327866900896676039482963 15491800351345014059224445)
        ·
          refine ⟨5809425131754380272209167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15491800351345014059224445 5809425131754380272209167)
          ·
            refine ⟨8714137697631570408313751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5809425131754380272209167 8714137697631570408313751)
            ·
              refine ⟨13071206546447355612470627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8714137697631570408313751 13071206546447355612470627)
              ·
                refine ⟨19606809819671033418705941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13071206546447355612470627 19606809819671033418705941)
                ·
                  refine ⟨919069210297079691501841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 19606809819671033418705941 919069210297079691501841)
                  ·
                    refine ⟨689301907722809768626381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 919069210297079691501841 689301907722809768626381)
                    ·
                      refine ⟨258488215396053663234893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 689301907722809768626381 258488215396053663234893)
                      ·
                        rfl

theorem cell23_503404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 3].length) (baseStart_503404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_503404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_503404 prefixEnd_503404 := by exact prefixLift 503404
  have htrace : WordTrace (prefixWord ++ tailWord_503404) baseStart_503404 baseEnd_503404 := by
    simpa [prefixWord, tailWord_503404, baseEnd_503404] using wordTrace_append hprefix tailTrace_503404
  have hstable : (prefixWord ++ tailWord_503404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503404).length < 2 ^ (prefixWord ++ tailWord_503404).sum := by decide
  have hdescent : baseEnd_503404 < baseStart_503404 := by decide
  rcases family_descends (prefixWord ++ tailWord_503404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503421 : List Nat := [1, 4, 1, 1, 4, 1, 1, 3, 2, 2, 3]
def baseStart_503421 : Nat := 118140960795 + 503421 * 2 ^ 59
def prefixEnd_503421 : Nat := 4983230072969 + 3 ^ 40 * 503421 * 2
def baseEnd_503421 : Nat := 258496944567180096722315

theorem tailTrace_503421 : CollatzResearch.WordTrace tailWord_503421 prefixEnd_503421 258496944567180096722315 := by
  unfold tailWord_503421
  simp only [CollatzResearch.WordTrace]
  refine ⟨18361272309199169306894117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12240848206132779537929411 18361272309199169306894117)
  ·
    refine ⟨3442738557974844245042647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18361272309199169306894117 3442738557974844245042647)
    ·
      refine ⟨5164107836962266367563971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3442738557974844245042647 5164107836962266367563971)
      ·
        refine ⟨7746161755443399551345957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5164107836962266367563971 7746161755443399551345957)
        ·
          refine ⟨1452405329145637415877367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7746161755443399551345957 1452405329145637415877367)
          ·
            refine ⟨2178607993718456123816051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1452405329145637415877367 2178607993718456123816051)
            ·
              refine ⟨3267911990577684185724077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2178607993718456123816051 3267911990577684185724077)
              ·
                refine ⟨1225466996466631569646529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3267911990577684185724077 1225466996466631569646529)
                ·
                  refine ⟨919100247349973677234897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1225466996466631569646529 919100247349973677234897)
                  ·
                    refine ⟨689325185512480257926173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 919100247349973677234897 689325185512480257926173)
                    ·
                      refine ⟨258496944567180096722315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 689325185512480257926173 258496944567180096722315)
                      ·
                        rfl

theorem cell23_503421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 3, 2, 2, 3].length) (baseStart_503421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_503421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_503421 prefixEnd_503421 := by exact prefixLift 503421
  have htrace : WordTrace (prefixWord ++ tailWord_503421) baseStart_503421 baseEnd_503421 := by
    simpa [prefixWord, tailWord_503421, baseEnd_503421] using wordTrace_append hprefix tailTrace_503421
  have hstable : (prefixWord ++ tailWord_503421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503421).length < 2 ^ (prefixWord ++ tailWord_503421).sum := by decide
  have hdescent : baseEnd_503421 < baseStart_503421 := by decide
  rcases family_descends (prefixWord ++ tailWord_503421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503427 : List Nat := [1, 1, 1, 3, 3, 1, 1, 2, 1, 1, 8]
def baseStart_503427 : Nat := 118140960795 + 503427 * 2 ^ 59
def prefixEnd_503427 : Nat := 4983230072969 + 3 ^ 40 * 503427 * 2
def baseEnd_503427 : Nat := 258500025451107073247287

theorem tailTrace_503427 : CollatzResearch.WordTrace tailWord_503427 prefixEnd_503427 258500025451107073247287 := by
  unfold tailWord_503427
  simp only [CollatzResearch.WordTrace]
  refine ⟨18361491147177432331612535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12240994098118288221075023 18361491147177432331612535)
  ·
    refine ⟨27542236720766148497418803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18361491147177432331612535 27542236720766148497418803)
    ·
      refine ⟨41313355081149222746128205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27542236720766148497418803 41313355081149222746128205)
      ·
        refine ⟨15492508155430958529798077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41313355081149222746128205 15492508155430958529798077)
        ·
          refine ⟨5809690558286609448674279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15492508155430958529798077 5809690558286609448674279)
          ·
            refine ⟨8714535837429914173011419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5809690558286609448674279 8714535837429914173011419)
            ·
              refine ⟨13071803756144871259517129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8714535837429914173011419 13071803756144871259517129)
              ·
                refine ⟨9803852817108653444637847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13071803756144871259517129 9803852817108653444637847)
                ·
                  refine ⟨14705779225662980166956771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9803852817108653444637847 14705779225662980166956771)
                  ·
                    refine ⟨22058668838494470250435157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14705779225662980166956771 22058668838494470250435157)
                    ·
                      refine ⟨258500025451107073247287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 22058668838494470250435157 258500025451107073247287)
                      ·
                        rfl

theorem cell23_503427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 2, 1, 1, 8].length) (baseStart_503427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_503427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_503427 prefixEnd_503427 := by exact prefixLift 503427
  have htrace : WordTrace (prefixWord ++ tailWord_503427) baseStart_503427 baseEnd_503427 := by
    simpa [prefixWord, tailWord_503427, baseEnd_503427] using wordTrace_append hprefix tailTrace_503427
  have hstable : (prefixWord ++ tailWord_503427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503427).length < 2 ^ (prefixWord ++ tailWord_503427).sum := by decide
  have hdescent : baseEnd_503427 < baseStart_503427 := by decide
  rcases family_descends (prefixWord ++ tailWord_503427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503461 : List Nat := [1, 3, 1, 2, 1, 2, 2, 2, 4, 3, 2]
def baseStart_503461 : Nat := 118140960795 + 503461 * 2 ^ 59
def prefixEnd_503461 : Nat := 4983230072969 + 3 ^ 40 * 503461 * 2
def baseEnd_503461 : Nat := 258517483793359940222131

theorem tailTrace_503461 : CollatzResearch.WordTrace tailWord_503461 prefixEnd_503461 258517483793359940222131 := by
  unfold tailWord_503461
  simp only [CollatzResearch.WordTrace]
  refine ⟨18362731229054256138350237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12241820819369504092233491 18362731229054256138350237)
  ·
    refine ⟨6886024210895346051881339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18362731229054256138350237 6886024210895346051881339)
    ·
      refine ⟨10329036316343019077822009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6886024210895346051881339 10329036316343019077822009)
      ·
        refine ⟨7746777237257264308366507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10329036316343019077822009 7746777237257264308366507)
        ·
          refine ⟨11620165855885896462549761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7746777237257264308366507 11620165855885896462549761)
          ·
            refine ⟨8715124391914422346912321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11620165855885896462549761 8715124391914422346912321)
            ·
              refine ⟨6536343293935816760184241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8715124391914422346912321 6536343293935816760184241)
              ·
                refine ⟨4902257470451862570138181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6536343293935816760184241 4902257470451862570138181)
                ·
                  refine ⟨919173275709724231900909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4902257470451862570138181 919173275709724231900909)
                  ·
                    refine ⟨344689978391146586962841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 919173275709724231900909 344689978391146586962841)
                    ·
                      refine ⟨258517483793359940222131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 344689978391146586962841 258517483793359940222131)
                      ·
                        rfl

theorem cell23_503461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 2, 4, 3, 2].length) (baseStart_503461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_503461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_503461 prefixEnd_503461 := by exact prefixLift 503461
  have htrace : WordTrace (prefixWord ++ tailWord_503461) baseStart_503461 baseEnd_503461 := by
    simpa [prefixWord, tailWord_503461, baseEnd_503461] using wordTrace_append hprefix tailTrace_503461
  have hstable : (prefixWord ++ tailWord_503461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503461).length < 2 ^ (prefixWord ++ tailWord_503461).sum := by decide
  have hdescent : baseEnd_503461 < baseStart_503461 := by decide
  rcases family_descends (prefixWord ++ tailWord_503461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503485 : List Nat := [1, 4, 1, 2, 1, 2, 4, 3, 1, 1, 3]
def baseStart_503485 : Nat := 118140960795 + 503485 * 2 ^ 59
def prefixEnd_503485 : Nat := 4983230072969 + 3 ^ 40 * 503485 * 2
def baseEnd_503485 : Nat := 258529807329067846322021

theorem tailTrace_503485 : CollatzResearch.WordTrace tailWord_503485 prefixEnd_503485 258529807329067846322021 := by
  unfold tailWord_503485
  simp only [CollatzResearch.WordTrace]
  refine ⟨18363606580967308237223909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12242404387311538824815939 18363606580967308237223909)
  ·
    refine ⟨3443176233931370294479483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18363606580967308237223909 3443176233931370294479483)
    ·
      refine ⟨5164764350897055441719225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3443176233931370294479483 5164764350897055441719225)
      ·
        refine ⟨3873573263172791581289419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5164764350897055441719225 3873573263172791581289419)
        ·
          refine ⟨5810359894759187371934129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3873573263172791581289419 5810359894759187371934129)
          ·
            refine ⟨4357769921069390528950597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5810359894759187371934129 4357769921069390528950597)
            ·
              refine ⟨817081860200510724178237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4357769921069390528950597 817081860200510724178237)
              ·
                refine ⟨306405697575191521566839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 817081860200510724178237 306405697575191521566839)
                ·
                  refine ⟨459608546362787282350259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 306405697575191521566839 459608546362787282350259)
                  ·
                    refine ⟨689412819544180923525389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 459608546362787282350259 689412819544180923525389)
                    ·
                      refine ⟨258529807329067846322021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 689412819544180923525389 258529807329067846322021)
                      ·
                        rfl

theorem cell23_503485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 4, 3, 1, 1, 3].length) (baseStart_503485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_503485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_503485 prefixEnd_503485 := by exact prefixLift 503485
  have htrace : WordTrace (prefixWord ++ tailWord_503485) baseStart_503485 baseEnd_503485 := by
    simpa [prefixWord, tailWord_503485, baseEnd_503485] using wordTrace_append hprefix tailTrace_503485
  have hstable : (prefixWord ++ tailWord_503485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503485).length < 2 ^ (prefixWord ++ tailWord_503485).sum := by decide
  have hdescent : baseEnd_503485 < baseStart_503485 := by decide
  rcases family_descends (prefixWord ++ tailWord_503485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503521 : List Nat := [1, 2, 3, 1, 5, 1, 1, 1, 1, 1, 6]
def baseStart_503521 : Nat := 118140960795 + 503521 * 2 ^ 59
def prefixEnd_503521 : Nat := 4983230072969 + 3 ^ 40 * 503521 * 2
def baseEnd_503521 : Nat := 258548292632629705471855

theorem tailTrace_503521 : CollatzResearch.WordTrace tailWord_503521 prefixEnd_503521 258548292632629705471855 := by
  unfold tailWord_503521
  simp only [CollatzResearch.WordTrace]
  refine ⟨18364919608836886385534417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12243279739224590923689611 18364919608836886385534417)
  ·
    refine ⟨13773689706627664789150813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18364919608836886385534417 13773689706627664789150813)
    ·
      refine ⟨5165133639985374295931555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13773689706627664789150813 5165133639985374295931555)
      ·
        refine ⟨7747700459978061443897333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5165133639985374295931555 7747700459978061443897333)
        ·
          refine ⟨726346918122943260365375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7747700459978061443897333 726346918122943260365375)
          ·
            refine ⟨1089520377184414890548063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 726346918122943260365375 1089520377184414890548063)
            ·
              refine ⟨1634280565776622335822095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1089520377184414890548063 1634280565776622335822095)
              ·
                refine ⟨2451420848664933503733143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1634280565776622335822095 2451420848664933503733143)
                ·
                  refine ⟨3677131272997400255599715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2451420848664933503733143 3677131272997400255599715)
                  ·
                    refine ⟨5515696909496100383399573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3677131272997400255599715 5515696909496100383399573)
                    ·
                      refine ⟨258548292632629705471855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5515696909496100383399573 258548292632629705471855)
                      ·
                        rfl

theorem cell23_503521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 1, 1, 1, 6].length) (baseStart_503521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_503521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_503521 prefixEnd_503521 := by exact prefixLift 503521
  have htrace : WordTrace (prefixWord ++ tailWord_503521) baseStart_503521 baseEnd_503521 := by
    simpa [prefixWord, tailWord_503521, baseEnd_503521] using wordTrace_append hprefix tailTrace_503521
  have hstable : (prefixWord ++ tailWord_503521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503521).length < 2 ^ (prefixWord ++ tailWord_503521).sum := by decide
  have hdescent : baseEnd_503521 < baseStart_503521 := by decide
  rcases family_descends (prefixWord ++ tailWord_503521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503528 : List Nat := [2, 1, 4, 1, 3, 1, 1, 4, 1, 2, 3]
def baseStart_503528 : Nat := 118140960795 + 503528 * 2 ^ 59
def prefixEnd_503528 : Nat := 4983230072969 + 3 ^ 40 * 503528 * 2
def baseEnd_503528 : Nat := 258551886997211178084323

theorem tailTrace_503528 : CollatzResearch.WordTrace tailWord_503528 prefixEnd_503528 258551886997211178084323 := by
  unfold tailWord_503528
  simp only [CollatzResearch.WordTrace]
  refine ⟨9182587459905763290519619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12243449946541017720692825 9182587459905763290519619)
  ·
    refine ⟨13773881189858644935779429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9182587459905763290519619 13773881189858644935779429)
    ·
      refine ⟨2582602723098495925458643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13773881189858644935779429 2582602723098495925458643)
      ·
        refine ⟨3873904084647743888187965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2582602723098495925458643 3873904084647743888187965)
        ·
          refine ⟨1452714031742903958070487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3873904084647743888187965 1452714031742903958070487)
          ·
            refine ⟨2179071047614355937105731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1452714031742903958070487 2179071047614355937105731)
            ·
              refine ⟨3268606571421533905658597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2179071047614355937105731 3268606571421533905658597)
              ·
                refine ⟨612863732141537607310987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3268606571421533905658597 612863732141537607310987)
                ·
                  refine ⟨919295598212306410966481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 612863732141537607310987 919295598212306410966481)
                  ·
                    refine ⟨689471698659229808224861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 919295598212306410966481 689471698659229808224861)
                    ·
                      refine ⟨258551886997211178084323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 689471698659229808224861 258551886997211178084323)
                      ·
                        rfl

theorem cell23_503528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 4, 1, 2, 3].length) (baseStart_503528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_503528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_503528 prefixEnd_503528 := by exact prefixLift 503528
  have htrace : WordTrace (prefixWord ++ tailWord_503528) baseStart_503528 baseEnd_503528 := by
    simpa [prefixWord, tailWord_503528, baseEnd_503528] using wordTrace_append hprefix tailTrace_503528
  have hstable : (prefixWord ++ tailWord_503528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503528).length < 2 ^ (prefixWord ++ tailWord_503528).sum := by decide
  have hdescent : baseEnd_503528 < baseStart_503528 := by decide
  rcases family_descends (prefixWord ++ tailWord_503528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503559 : List Nat := [1, 1, 4, 4, 3, 1, 1, 1, 3, 2, 2]
def baseStart_503559 : Nat := 118140960795 + 503559 * 2 ^ 59
def prefixEnd_503559 : Nat := 4983230072969 + 3 ^ 40 * 503559 * 2
def baseEnd_503559 : Nat := 258567804897500556796681

theorem tailTrace_503559 : CollatzResearch.WordTrace tailWord_503559 prefixEnd_503559 258567804897500556796681 := by
  unfold tailWord_503559
  simp only [CollatzResearch.WordTrace]
  refine ⟨18366305582699218875417731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12244203721799479250278487 18366305582699218875417731)
  ·
    refine ⟨27549458374048828313126597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18366305582699218875417731 27549458374048828313126597)
    ·
      refine ⟨5165523445134155308711237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27549458374048828313126597 5165523445134155308711237)
      ·
        refine ⟨968535645962654120383357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5165523445134155308711237 968535645962654120383357)
        ·
          refine ⟨363200867235995295143759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 968535645962654120383357 363200867235995295143759)
          ·
            refine ⟨544801300853992942715639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 363200867235995295143759 544801300853992942715639)
            ·
              refine ⟨817201951280989414073459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 544801300853992942715639 817201951280989414073459)
              ·
                refine ⟨1225802926921484121110189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 817201951280989414073459 1225802926921484121110189)
                ·
                  refine ⟨459676097595556545416321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1225802926921484121110189 459676097595556545416321)
                  ·
                    refine ⟨344757073196667409062241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 459676097595556545416321 344757073196667409062241)
                    ·
                      refine ⟨258567804897500556796681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 344757073196667409062241 258567804897500556796681)
                      ·
                        rfl

theorem cell23_503559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 1, 1, 3, 2, 2].length) (baseStart_503559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_503559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_503559 prefixEnd_503559 := by exact prefixLift 503559
  have htrace : WordTrace (prefixWord ++ tailWord_503559) baseStart_503559 baseEnd_503559 := by
    simpa [prefixWord, tailWord_503559, baseEnd_503559] using wordTrace_append hprefix tailTrace_503559
  have hstable : (prefixWord ++ tailWord_503559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503559).length < 2 ^ (prefixWord ++ tailWord_503559).sum := by decide
  have hdescent : baseEnd_503559 < baseStart_503559 := by decide
  rcases family_descends (prefixWord ++ tailWord_503559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503575 : List Nat := [1, 1, 3, 4, 2, 2, 1, 3, 2, 1, 3]
def baseStart_503575 : Nat := 118140960795 + 503575 * 2 ^ 59
def prefixEnd_503575 : Nat := 4983230072969 + 3 ^ 40 * 503575 * 2
def baseEnd_503575 : Nat := 258576020587972494196607

theorem tailTrace_503575 : CollatzResearch.WordTrace tailWord_503575 prefixEnd_503575 258576020587972494196607 := by
  unfold tailWord_503575
  simp only [CollatzResearch.WordTrace]
  refine ⟨18366889150641253608000179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12244592767094169072000119 18366889150641253608000179)
  ·
    refine ⟨27550333725961880412000269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18366889150641253608000179 27550333725961880412000269)
    ·
      refine ⟨10331375147235705154500101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27550333725961880412000269 10331375147235705154500101)
      ·
        refine ⟨1937132840106694716468769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10331375147235705154500101 1937132840106694716468769)
        ·
          refine ⟨1452849630080021037351577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1937132840106694716468769 1452849630080021037351577)
          ·
            refine ⟨1089637222560015778013683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1452849630080021037351577 1089637222560015778013683)
            ·
              refine ⟨1634455833840023667020525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1089637222560015778013683 1634455833840023667020525)
              ·
                refine ⟨612920937690008875132697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1634455833840023667020525 612920937690008875132697)
                ·
                  refine ⟨459690703267506656349523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 612920937690008875132697 459690703267506656349523)
                  ·
                    refine ⟨689536054901259984524285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 459690703267506656349523 689536054901259984524285)
                    ·
                      refine ⟨258576020587972494196607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 689536054901259984524285 258576020587972494196607)
                      ·
                        rfl

theorem cell23_503575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 3, 2, 1, 3].length) (baseStart_503575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_503575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_503575 prefixEnd_503575 := by exact prefixLift 503575
  have htrace : WordTrace (prefixWord ++ tailWord_503575) baseStart_503575 baseEnd_503575 := by
    simpa [prefixWord, tailWord_503575, baseEnd_503575] using wordTrace_append hprefix tailTrace_503575
  have hstable : (prefixWord ++ tailWord_503575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503575).length < 2 ^ (prefixWord ++ tailWord_503575).sum := by decide
  have hdescent : baseEnd_503575 < baseStart_503575 := by decide
  rcases family_descends (prefixWord ++ tailWord_503575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503585 : List Nat := [1, 2, 3, 2, 1, 3, 3, 2, 1, 3, 2]
def baseStart_503585 : Nat := 118140960795 + 503585 * 2 ^ 59
def prefixEnd_503585 : Nat := 4983230072969 + 3 ^ 40 * 503585 * 2
def baseEnd_503585 : Nat := 258581155394517455071561

theorem tailTrace_503585 : CollatzResearch.WordTrace tailWord_503585 prefixEnd_503585 258581155394517455071561 := by
  unfold tailWord_503585
  simp only [CollatzResearch.WordTrace]
  refine ⟨18367253880605025315864209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12244835920403350210576139 18367253880605025315864209)
  ·
    refine ⟨13775440410453768986898157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18367253880605025315864209 13775440410453768986898157)
    ·
      refine ⟨5165790153920163370086809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13775440410453768986898157 5165790153920163370086809)
      ·
        refine ⟨3874342615440122527565107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5165790153920163370086809 3874342615440122527565107)
        ·
          refine ⟨5811513923160183791347661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3874342615440122527565107 5811513923160183791347661)
          ·
            refine ⟨2179317721185068921755373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5811513923160183791347661 2179317721185068921755373)
            ·
              refine ⟨817244145444400845658265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2179317721185068921755373 817244145444400845658265)
              ·
                refine ⟨612933109083300634243699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 817244145444400845658265 612933109083300634243699)
                ·
                  refine ⟨919399663624950951365549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 612933109083300634243699 919399663624950951365549)
                  ·
                    refine ⟨344774873859356606762081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 919399663624950951365549 344774873859356606762081)
                    ·
                      refine ⟨258581155394517455071561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 344774873859356606762081 258581155394517455071561)
                      ·
                        rfl

theorem cell23_503585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 3, 2, 1, 3, 2].length) (baseStart_503585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_503585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_503585 prefixEnd_503585 := by exact prefixLift 503585
  have htrace : WordTrace (prefixWord ++ tailWord_503585) baseStart_503585 baseEnd_503585 := by
    simpa [prefixWord, tailWord_503585, baseEnd_503585] using wordTrace_append hprefix tailTrace_503585
  have hstable : (prefixWord ++ tailWord_503585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503585).length < 2 ^ (prefixWord ++ tailWord_503585).sum := by decide
  have hdescent : baseEnd_503585 < baseStart_503585 := by decide
  rcases family_descends (prefixWord ++ tailWord_503585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503601 : List Nat := [1, 2, 2, 3, 2, 2, 2, 1, 2, 1, 5]
def baseStart_503601 : Nat := 118140960795 + 503601 * 2 ^ 59
def prefixEnd_503601 : Nat := 4983230072969 + 3 ^ 40 * 503601 * 2
def baseEnd_503601 : Nat := 258589371084989392471487

theorem tailTrace_503601 : CollatzResearch.WordTrace tailWord_503601 prefixEnd_503601 258589371084989392471487 := by
  unfold tailWord_503601
  simp only [CollatzResearch.WordTrace]
  refine ⟨18367837448547060048446657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12245224965698040032297771 18367837448547060048446657)
  ·
    refine ⟨13775878086410295036334993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18367837448547060048446657 13775878086410295036334993)
    ·
      refine ⟨10331908564807721277251245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13775878086410295036334993 10331908564807721277251245)
      ·
        refine ⟨3874465711802895478969217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10331908564807721277251245 3874465711802895478969217)
        ·
          refine ⟨2905849283852171609226913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3874465711802895478969217 2905849283852171609226913)
          ·
            refine ⟨2179386962889128706920185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2905849283852171609226913 2179386962889128706920185)
            ·
              refine ⟨1634540222166846530190139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2179386962889128706920185 1634540222166846530190139)
              ·
                refine ⟨2451810333250269795285209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1634540222166846530190139 2451810333250269795285209)
                ·
                  refine ⟨1838857749937702346463907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2451810333250269795285209 1838857749937702346463907)
                  ·
                    refine ⟨2758286624906553519695861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1838857749937702346463907 2758286624906553519695861)
                    ·
                      refine ⟨258589371084989392471487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2758286624906553519695861 258589371084989392471487)
                      ·
                        rfl

theorem cell23_503601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 2, 1, 2, 1, 5].length) (baseStart_503601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_503601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_503601 prefixEnd_503601 := by exact prefixLift 503601
  have htrace : WordTrace (prefixWord ++ tailWord_503601) baseStart_503601 baseEnd_503601 := by
    simpa [prefixWord, tailWord_503601, baseEnd_503601] using wordTrace_append hprefix tailTrace_503601
  have hstable : (prefixWord ++ tailWord_503601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503601).length < 2 ^ (prefixWord ++ tailWord_503601).sum := by decide
  have hdescent : baseEnd_503601 < baseStart_503601 := by decide
  rcases family_descends (prefixWord ++ tailWord_503601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503602 : List Nat := [3, 2, 1, 1, 3, 3, 3, 1, 1, 3, 2]
def baseStart_503602 : Nat := 118140960795 + 503602 * 2 ^ 59
def prefixEnd_503602 : Nat := 4983230072969 + 3 ^ 40 * 503602 * 2
def baseEnd_503602 : Nat := 258589884565643888558983

theorem tailTrace_503602 : CollatzResearch.WordTrace tailWord_503602 prefixEnd_503602 258589884565643888558983 := by
  unfold tailWord_503602
  simp only [CollatzResearch.WordTrace]
  refine ⟨4591968480385859304808265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12245249281028958146155373 4591968480385859304808265)
  ·
    refine ⟨3443976360289394478606199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4591968480385859304808265 3443976360289394478606199)
    ·
      refine ⟨5165964540434091717909299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3443976360289394478606199 5165964540434091717909299)
      ·
        refine ⟨7748946810651137576863949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5165964540434091717909299 7748946810651137576863949)
        ·
          refine ⟨2905855053994176591323981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7748946810651137576863949 2905855053994176591323981)
          ·
            refine ⟨1089695645247816221746493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2905855053994176591323981 1089695645247816221746493)
            ·
              refine ⟨408635866967931083154935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1089695645247816221746493 408635866967931083154935)
              ·
                refine ⟨612953800451896624732403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 408635866967931083154935 612953800451896624732403)
                ·
                  refine ⟨919430700677844937098605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 612953800451896624732403 919430700677844937098605)
                  ·
                    refine ⟨344786512754191851411977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 919430700677844937098605 344786512754191851411977)
                    ·
                      refine ⟨258589884565643888558983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 344786512754191851411977 258589884565643888558983)
                      ·
                        rfl

theorem cell23_503602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 3, 1, 1, 3, 2].length) (baseStart_503602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_503602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_503602 prefixEnd_503602 := by exact prefixLift 503602
  have htrace : WordTrace (prefixWord ++ tailWord_503602) baseStart_503602 baseEnd_503602 := by
    simpa [prefixWord, tailWord_503602, baseEnd_503602] using wordTrace_append hprefix tailTrace_503602
  have hstable : (prefixWord ++ tailWord_503602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503602).length < 2 ^ (prefixWord ++ tailWord_503602).sum := by decide
  have hdescent : baseEnd_503602 < baseStart_503602 := by decide
  rcases family_descends (prefixWord ++ tailWord_503602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503628 : List Nat := [2, 2, 1, 3, 4, 1, 1, 1, 2, 2, 4]
def baseStart_503628 : Nat := 118140960795 + 503628 * 2 ^ 59
def prefixEnd_503628 : Nat := 4983230072969 + 3 ^ 40 * 503628 * 2
def baseEnd_503628 : Nat := 258603235062660786833863

theorem tailTrace_503628 : CollatzResearch.WordTrace tailWord_503628 prefixEnd_503628 258603235062660786833863 := by
  unfold tailWord_503628
  simp only [CollatzResearch.WordTrace]
  refine ⟨9184411109724621829839769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12245881479632829106453025 9184411109724621829839769)
  ·
    refine ⟨6888308332293466372379827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9184411109724621829839769 6888308332293466372379827)
    ·
      refine ⟨10332462498440199558569741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6888308332293466372379827 10332462498440199558569741)
      ·
        refine ⟨3874673436915074834463653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10332462498440199558569741 3874673436915074834463653)
        ·
          refine ⟨726501269421576531461935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3874673436915074834463653 726501269421576531461935)
          ·
            refine ⟨1089751904132364797192903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 726501269421576531461935 1089751904132364797192903)
            ·
              refine ⟨1634627856198547195789355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1089751904132364797192903 1634627856198547195789355)
              ·
                refine ⟨2451941784297820793684033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1634627856198547195789355 2451941784297820793684033)
                ·
                  refine ⟨1838956338223365595263025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2451941784297820793684033 1838956338223365595263025)
                  ·
                    refine ⟨1379217253667524196447269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1838956338223365595263025 1379217253667524196447269)
                    ·
                      refine ⟨258603235062660786833863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1379217253667524196447269 258603235062660786833863)
                      ·
                        rfl

theorem cell23_503628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 1, 2, 2, 4].length) (baseStart_503628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_503628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_503628 prefixEnd_503628 := by exact prefixLift 503628
  have htrace : WordTrace (prefixWord ++ tailWord_503628) baseStart_503628 baseEnd_503628 := by
    simpa [prefixWord, tailWord_503628, baseEnd_503628] using wordTrace_append hprefix tailTrace_503628
  have hstable : (prefixWord ++ tailWord_503628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503628).length < 2 ^ (prefixWord ++ tailWord_503628).sum := by decide
  have hdescent : baseEnd_503628 < baseStart_503628 := by decide
  rcases family_descends (prefixWord ++ tailWord_503628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503661 : List Nat := [1, 5, 1, 1, 1, 1, 2, 1, 3, 2, 5]
def baseStart_503661 : Nat := 118140960795 + 503661 * 2 ^ 59
def prefixEnd_503661 : Nat := 4983230072969 + 3 ^ 40 * 503661 * 2
def baseEnd_503661 : Nat := 258620179924259157721211

theorem tailTrace_503661 : CollatzResearch.WordTrace tailWord_503661 prefixEnd_503661 258620179924259157721211 := by
  unfold tailWord_503661
  simp only [CollatzResearch.WordTrace]
  refine ⟨18370025828329690295630837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12246683885553126863753891 18370025828329690295630837)
  ·
    refine ⟨1722189921405908465215391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18370025828329690295630837 1722189921405908465215391)
    ·
      refine ⟨2583284882108862697823087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1722189921405908465215391 2583284882108862697823087)
      ·
        refine ⟨3874927323163294046734631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2583284882108862697823087 3874927323163294046734631)
        ·
          refine ⟨5812390984744941070101947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3874927323163294046734631 5812390984744941070101947)
          ·
            refine ⟨8718586477117411605152921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5812390984744941070101947 8718586477117411605152921)
            ·
              refine ⟨6538939857838058703864691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8718586477117411605152921 6538939857838058703864691)
              ·
                refine ⟨9808409786757088055797037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6538939857838058703864691 9808409786757088055797037)
                ·
                  refine ⟨3678153670033908020923889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9808409786757088055797037 3678153670033908020923889)
                  ·
                    refine ⟨2758615252525431015692917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3678153670033908020923889 2758615252525431015692917)
                    ·
                      refine ⟨258620179924259157721211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2758615252525431015692917 258620179924259157721211)
                      ·
                        rfl

theorem cell23_503661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 1, 3, 2, 5].length) (baseStart_503661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_503661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_503661 prefixEnd_503661 := by exact prefixLift 503661
  have htrace : WordTrace (prefixWord ++ tailWord_503661) baseStart_503661 baseEnd_503661 := by
    simpa [prefixWord, tailWord_503661, baseEnd_503661] using wordTrace_append hprefix tailTrace_503661
  have hstable : (prefixWord ++ tailWord_503661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503661).length < 2 ^ (prefixWord ++ tailWord_503661).sum := by decide
  have hdescent : baseEnd_503661 < baseStart_503661 := by decide
  rcases family_descends (prefixWord ++ tailWord_503661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503701 : List Nat := [1, 3, 2, 1, 1, 3, 1, 1, 2, 4, 4]
def baseStart_503701 : Nat := 118140960795 + 503701 * 2 ^ 59
def prefixEnd_503701 : Nat := 4983230072969 + 3 ^ 40 * 503701 * 2
def baseEnd_503701 : Nat := 258640719150439001221027

theorem tailTrace_503701 : CollatzResearch.WordTrace tailWord_503701 prefixEnd_503701 258640719150439001221027 := by
  unfold tailWord_503701
  simp only [CollatzResearch.WordTrace]
  refine ⟨18371484748184777127086957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12247656498789851418057971 18371484748184777127086957)
  ·
    refine ⟨6889306780569291422657609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18371484748184777127086957 6889306780569291422657609)
    ·
      refine ⟨5166980085426968566993207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6889306780569291422657609 5166980085426968566993207)
      ·
        refine ⟨7750470128140452850489811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5166980085426968566993207 7750470128140452850489811)
        ·
          refine ⟨11625705192210679275734717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7750470128140452850489811 11625705192210679275734717)
          ·
            refine ⟨4359639447079004728400519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11625705192210679275734717 4359639447079004728400519)
            ·
              refine ⟨6539459170618507092600779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4359639447079004728400519 6539459170618507092600779)
              ·
                refine ⟨9809188755927760638901169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6539459170618507092600779 9809188755927760638901169)
                ·
                  refine ⟨7356891566945820479175877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9809188755927760638901169 7356891566945820479175877)
                  ·
                    refine ⟨1379417168802341339845477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7356891566945820479175877 1379417168802341339845477)
                    ·
                      refine ⟨258640719150439001221027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1379417168802341339845477 258640719150439001221027)
                      ·
                        rfl

theorem cell23_503701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 1, 2, 4, 4].length) (baseStart_503701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_503701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_503701 prefixEnd_503701 := by exact prefixLift 503701
  have htrace : WordTrace (prefixWord ++ tailWord_503701) baseStart_503701 baseEnd_503701 := by
    simpa [prefixWord, tailWord_503701, baseEnd_503701] using wordTrace_append hprefix tailTrace_503701
  have hstable : (prefixWord ++ tailWord_503701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503701).length < 2 ^ (prefixWord ++ tailWord_503701).sum := by decide
  have hdescent : baseEnd_503701 < baseStart_503701 := by decide
  rcases family_descends (prefixWord ++ tailWord_503701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503758 : List Nat := [4, 1, 1, 1, 2, 2, 3, 1, 3, 5]
def baseStart_503758 : Nat := 118140960795 + 503758 * 2 ^ 59
def prefixEnd_503758 : Nat := 4983230072969 + 3 ^ 40 * 503758 * 2
def baseEnd_503758 : Nat := 86223329182581759402755

theorem tailTrace_503758 : CollatzResearch.WordTrace tailWord_503758 prefixEnd_503758 86223329182581759402755 := by
  unfold tailWord_503758
  simp only [CollatzResearch.WordTrace]
  refine ⟨2296695463622284482738991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12249042472652183907941285 2296695463622284482738991)
  ·
    refine ⟨3445043195433426724108487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2296695463622284482738991 3445043195433426724108487)
    ·
      refine ⟨5167564793150140086162731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3445043195433426724108487 5167564793150140086162731)
      ·
        refine ⟨7751347189725210129244097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5167564793150140086162731 7751347189725210129244097)
        ·
          refine ⟨5813510392293907596933073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7751347189725210129244097 5813510392293907596933073)
          ·
            refine ⟨4360132794220430697699805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5813510392293907596933073 4360132794220430697699805)
            ·
              refine ⟨1635049797832661511637427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4360132794220430697699805 1635049797832661511637427)
              ·
                refine ⟨2452574696748992267456141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1635049797832661511637427 2452574696748992267456141)
                ·
                  refine ⟨919715511280872100296053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2452574696748992267456141 919715511280872100296053)
                  ·
                    refine ⟨86223329182581759402755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 919715511280872100296053 86223329182581759402755)
                    ·
                      rfl

theorem cell23_503758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 1, 3, 5].length) (baseStart_503758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_503758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_503758 prefixEnd_503758 := by exact prefixLift 503758
  have htrace : WordTrace (prefixWord ++ tailWord_503758) baseStart_503758 baseEnd_503758 := by
    simpa [prefixWord, tailWord_503758, baseEnd_503758] using wordTrace_append hprefix tailTrace_503758
  have hstable : (prefixWord ++ tailWord_503758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503758).length < 2 ^ (prefixWord ++ tailWord_503758).sum := by decide
  have hdescent : baseEnd_503758 < baseStart_503758 := by decide
  rcases family_descends (prefixWord ++ tailWord_503758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503788 : List Nat := [2, 2, 1, 1, 2, 1, 1, 5, 4, 4]
def baseStart_503788 : Nat := 118140960795 + 503788 * 2 ^ 59
def prefixEnd_503788 : Nat := 4983230072969 + 3 ^ 40 * 503788 * 2
def baseEnd_503788 : Nat := 86228463989126720277709

theorem tailTrace_503788 : CollatzResearch.WordTrace tailWord_503788 prefixEnd_503788 86228463989126720277709 := by
  unfold tailWord_503788
  simp only [CollatzResearch.WordTrace]
  refine ⟨9187328949434795492752009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12249771932579727323669345 9187328949434795492752009)
  ·
    refine ⟨6890496712076096619564007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9187328949434795492752009 6890496712076096619564007)
    ·
      refine ⟨10335745068114144929346011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6890496712076096619564007 10335745068114144929346011)
      ·
        refine ⟨15503617602171217394019017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10335745068114144929346011 15503617602171217394019017)
        ·
          refine ⟨11627713201628413045514263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15503617602171217394019017 11627713201628413045514263)
          ·
            refine ⟨17441569802442619568271395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11627713201628413045514263 17441569802442619568271395)
            ·
              refine ⟨26162354703663929352407093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17441569802442619568271395 26162354703663929352407093)
              ·
                refine ⟨2452720753468493376788165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26162354703663929352407093 2452720753468493376788165)
                ·
                  refine ⟨459885141275342508147781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2452720753468493376788165 459885141275342508147781)
                  ·
                    refine ⟨86228463989126720277709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 459885141275342508147781 86228463989126720277709)
                    ·
                      rfl

theorem cell23_503788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 4].length) (baseStart_503788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_503788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_503788 prefixEnd_503788 := by exact prefixLift 503788
  have htrace : WordTrace (prefixWord ++ tailWord_503788) baseStart_503788 baseEnd_503788 := by
    simpa [prefixWord, tailWord_503788, baseEnd_503788] using wordTrace_append hprefix tailTrace_503788
  have hstable : (prefixWord ++ tailWord_503788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503788).length < 2 ^ (prefixWord ++ tailWord_503788).sum := by decide
  have hdescent : baseEnd_503788 < baseStart_503788 := by decide
  rcases family_descends (prefixWord ++ tailWord_503788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503795 : List Nat := [1, 1, 1, 2, 2, 2, 1, 2, 7, 2, 2]
def baseStart_503795 : Nat := 118140960795 + 503795 * 2 ^ 59
def prefixEnd_503795 : Nat := 4983230072969 + 3 ^ 40 * 503795 * 2
def baseEnd_503795 : Nat := 258688986331961633445595

theorem tailTrace_503795 : CollatzResearch.WordTrace tailWord_503795 prefixEnd_503795 258688986331961633445595 := by
  unfold tailWord_503795
  simp only [CollatzResearch.WordTrace]
  refine ⟨18374913209844231181008839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12249942139896154120672559 18374913209844231181008839)
  ·
    refine ⟨27562369814766346771513259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18374913209844231181008839 27562369814766346771513259)
    ·
      refine ⟨41343554722149520157269889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27562369814766346771513259 41343554722149520157269889)
      ·
        refine ⟨31007666041612140117952417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41343554722149520157269889 31007666041612140117952417)
        ·
          refine ⟨23255749531209105088464313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31007666041612140117952417 23255749531209105088464313)
          ·
            refine ⟨17441812148406828816348235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23255749531209105088464313 17441812148406828816348235)
            ·
              refine ⟨26162718222610243224522353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17441812148406828816348235 26162718222610243224522353)
              ·
                refine ⟨19622038666957682418391765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26162718222610243224522353 19622038666957682418391765)
                ·
                  refine ⟨459891531256820681681057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19622038666957682418391765 459891531256820681681057)
                  ·
                    refine ⟨344918648442615511260793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 459891531256820681681057 344918648442615511260793)
                    ·
                      refine ⟨258688986331961633445595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 344918648442615511260793 258688986331961633445595)
                      ·
                        rfl

theorem cell23_503795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 7, 2, 2].length) (baseStart_503795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_503795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_503795 prefixEnd_503795 := by exact prefixLift 503795
  have htrace : WordTrace (prefixWord ++ tailWord_503795) baseStart_503795 baseEnd_503795 := by
    simpa [prefixWord, tailWord_503795, baseEnd_503795] using wordTrace_append hprefix tailTrace_503795
  have hstable : (prefixWord ++ tailWord_503795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503795).length < 2 ^ (prefixWord ++ tailWord_503795).sum := by decide
  have hdescent : baseEnd_503795 < baseStart_503795 := by decide
  rcases family_descends (prefixWord ++ tailWord_503795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503805 : List Nat := [1, 4, 1, 1, 1, 2, 4, 3, 2, 4]
def baseStart_503805 : Nat := 118140960795 + 503805 * 2 ^ 59
def prefixEnd_503805 : Nat := 4983230072969 + 3 ^ 40 * 503805 * 2
def baseEnd_503805 : Nat := 86231373712835531440183

theorem tailTrace_503805 : CollatzResearch.WordTrace tailWord_503805 prefixEnd_503805 86231373712835531440183 := by
  unfold tailWord_503805
  simp only [CollatzResearch.WordTrace]
  refine ⟨18375277939808002888872869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12250185293205335259248579 18375277939808002888872869)
  ·
    refine ⟨3445364613714000541663663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18375277939808002888872869 3445364613714000541663663)
    ·
      refine ⟨5168046920571000812495495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3445364613714000541663663 5168046920571000812495495)
      ·
        refine ⟨7752070380856501218743243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5168046920571000812495495 7752070380856501218743243)
        ·
          refine ⟨11628105571284751828114865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7752070380856501218743243 11628105571284751828114865)
          ·
            refine ⟨8721079178463563871086149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11628105571284751828114865 8721079178463563871086149)
            ·
              refine ⟨1635202345961918225828653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8721079178463563871086149 1635202345961918225828653)
              ·
                refine ⟨613200879735719334685745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1635202345961918225828653 613200879735719334685745)
                ·
                  refine ⟨459900659801789501014309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 613200879735719334685745 459900659801789501014309)
                  ·
                    refine ⟨86231373712835531440183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 459900659801789501014309 86231373712835531440183)
                    ·
                      rfl

theorem cell23_503805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 3, 2, 4].length) (baseStart_503805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_503805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_503805 prefixEnd_503805 := by exact prefixLift 503805
  have htrace : WordTrace (prefixWord ++ tailWord_503805) baseStart_503805 baseEnd_503805 := by
    simpa [prefixWord, tailWord_503805, baseEnd_503805] using wordTrace_append hprefix tailTrace_503805
  have hstable : (prefixWord ++ tailWord_503805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503805).length < 2 ^ (prefixWord ++ tailWord_503805).sum := by decide
  have hdescent : baseEnd_503805 < baseStart_503805 := by decide
  rcases family_descends (prefixWord ++ tailWord_503805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503811 : List Nat := [1, 1, 1, 3, 2, 1, 1, 2, 2, 2, 7]
def baseStart_503811 : Nat := 118140960795 + 503811 * 2 ^ 59
def prefixEnd_503811 : Nat := 4983230072969 + 3 ^ 40 * 503811 * 2
def baseEnd_503811 : Nat := 258697202022433570845521

theorem tailTrace_503811 : CollatzResearch.WordTrace tailWord_503811 prefixEnd_503811 258697202022433570845521 := by
  unfold tailWord_503811
  simp only [CollatzResearch.WordTrace]
  refine ⟨18375496777786265913591287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12250331185190843942394191 18375496777786265913591287)
  ·
    refine ⟨27563245166679398870386931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18375496777786265913591287 27563245166679398870386931)
    ·
      refine ⟨41344867750019098305580397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27563245166679398870386931 41344867750019098305580397)
      ·
        refine ⟨15504325406257161864592649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41344867750019098305580397 15504325406257161864592649)
        ·
          refine ⟨11628244054692871398444487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15504325406257161864592649 11628244054692871398444487)
          ·
            refine ⟨17442366082039307097666731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11628244054692871398444487 17442366082039307097666731)
            ·
              refine ⟨26163549123058960646500097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17442366082039307097666731 26163549123058960646500097)
              ·
                refine ⟨19622661842294220484875073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26163549123058960646500097 19622661842294220484875073)
                ·
                  refine ⟨14716996381720665363656305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19622661842294220484875073 14716996381720665363656305)
                  ·
                    refine ⟨11037747286290499022742229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14716996381720665363656305 11037747286290499022742229)
                    ·
                      refine ⟨258697202022433570845521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 11037747286290499022742229 258697202022433570845521)
                      ·
                        rfl

theorem cell23_503811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 2, 2, 7].length) (baseStart_503811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_503811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_503811 prefixEnd_503811 := by exact prefixLift 503811
  have htrace : WordTrace (prefixWord ++ tailWord_503811) baseStart_503811 baseEnd_503811 := by
    simpa [prefixWord, tailWord_503811, baseEnd_503811] using wordTrace_append hprefix tailTrace_503811
  have hstable : (prefixWord ++ tailWord_503811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503811).length < 2 ^ (prefixWord ++ tailWord_503811).sum := by decide
  have hdescent : baseEnd_503811 < baseStart_503811 := by decide
  rcases family_descends (prefixWord ++ tailWord_503811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503815 : List Nat := [1, 1, 4, 3, 1, 2, 2, 1, 3, 2, 3]
def baseStart_503815 : Nat := 118140960795 + 503815 * 2 ^ 59
def prefixEnd_503815 : Nat := 4983230072969 + 3 ^ 40 * 503815 * 2
def baseEnd_503815 : Nat := 258699255945051555195503

theorem tailTrace_503815 : CollatzResearch.WordTrace tailWord_503815 prefixEnd_503815 258699255945051555195503 := by
  unfold tailWord_503815
  simp only [CollatzResearch.WordTrace]
  refine ⟨18375642669771774596736899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12250428446514516397824599 18375642669771774596736899)
  ·
    refine ⟨27563464004657661895105349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18375642669771774596736899 27563464004657661895105349)
    ·
      refine ⟨5168149500873311605332253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27563464004657661895105349 5168149500873311605332253)
      ·
        refine ⟨1938056062827491851999595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5168149500873311605332253 1938056062827491851999595)
        ·
          refine ⟨2907084094241237777999393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1938056062827491851999595 2907084094241237777999393)
          ·
            refine ⟨2180313070680928333499545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2907084094241237777999393 2180313070680928333499545)
            ·
              refine ⟨1635234803010696250124659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2180313070680928333499545 1635234803010696250124659)
              ·
                refine ⟨2452852204516044375186989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1635234803010696250124659 2452852204516044375186989)
                ·
                  refine ⟨919819576693516640695121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2452852204516044375186989 919819576693516640695121)
                  ·
                    refine ⟨689864682520137480521341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 919819576693516640695121 689864682520137480521341)
                    ·
                      refine ⟨258699255945051555195503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 689864682520137480521341 258699255945051555195503)
                      ·
                        rfl

theorem cell23_503815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 1, 3, 2, 3].length) (baseStart_503815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_503815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_503815 prefixEnd_503815 := by exact prefixLift 503815
  have htrace : WordTrace (prefixWord ++ tailWord_503815) baseStart_503815 baseEnd_503815 := by
    simpa [prefixWord, tailWord_503815, baseEnd_503815] using wordTrace_append hprefix tailTrace_503815
  have hstable : (prefixWord ++ tailWord_503815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503815).length < 2 ^ (prefixWord ++ tailWord_503815).sum := by decide
  have hdescent : baseEnd_503815 < baseStart_503815 := by decide
  rcases family_descends (prefixWord ++ tailWord_503815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503829 : List Nat := [1, 3, 2, 1, 5, 2, 2, 1, 1, 1, 4]
def baseStart_503829 : Nat := 118140960795 + 503829 * 2 ^ 59
def prefixEnd_503829 : Nat := 4983230072969 + 3 ^ 40 * 503829 * 2
def baseEnd_503829 : Nat := 258706444674214500420439

theorem tailTrace_503829 : CollatzResearch.WordTrace tailWord_503829 prefixEnd_503829 258706444674214500420439 := by
  unfold tailWord_503829
  simp only [CollatzResearch.WordTrace]
  refine ⟨18376153291721054987746541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12250768861147369991831027 18376153291721054987746541)
  ·
    refine ⟨6891057484395395620404953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18376153291721054987746541 6891057484395395620404953)
    ·
      refine ⟨5168293113296546715303715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6891057484395395620404953 5168293113296546715303715)
      ·
        refine ⟨7752439669944820072955573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5168293113296546715303715 7752439669944820072955573)
        ·
          refine ⟨726791219057326881839585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7752439669944820072955573 726791219057326881839585)
          ·
            refine ⟨545093414292995161379689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 726791219057326881839585 545093414292995161379689)
            ·
              refine ⟨408820060719746371034767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 545093414292995161379689 408820060719746371034767)
              ·
                refine ⟨613230091079619556552151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 408820060719746371034767 613230091079619556552151)
                ·
                  refine ⟨919845136619429334828227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 613230091079619556552151 919845136619429334828227)
                  ·
                    refine ⟨1379767704929144002242341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 919845136619429334828227 1379767704929144002242341)
                    ·
                      refine ⟨258706444674214500420439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1379767704929144002242341 258706444674214500420439)
                      ·
                        rfl

theorem cell23_503829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 2, 1, 1, 1, 4].length) (baseStart_503829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_503829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_503829 prefixEnd_503829 := by exact prefixLift 503829
  have htrace : WordTrace (prefixWord ++ tailWord_503829) baseStart_503829 baseEnd_503829 := by
    simpa [prefixWord, tailWord_503829, baseEnd_503829] using wordTrace_append hprefix tailTrace_503829
  have hstable : (prefixWord ++ tailWord_503829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503829).length < 2 ^ (prefixWord ++ tailWord_503829).sum := by decide
  have hdescent : baseEnd_503829 < baseStart_503829 := by decide
  rcases family_descends (prefixWord ++ tailWord_503829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503855 : List Nat := [1, 1, 2, 1, 2, 1, 1, 6, 3, 3, 2]
def baseStart_503855 : Nat := 118140960795 + 503855 * 2 ^ 59
def prefixEnd_503855 : Nat := 4983230072969 + 3 ^ 40 * 503855 * 2
def baseEnd_503855 : Nat := 258719795171231398695319

theorem tailTrace_503855 : CollatzResearch.WordTrace tailWord_503855 prefixEnd_503855 258719795171231398695319 := by
  unfold tailWord_503855
  simp only [CollatzResearch.WordTrace]
  refine ⟨18377101589626861428193019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12251401059751240952128679 18377101589626861428193019)
  ·
    refine ⟨27565652384440292142289529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18377101589626861428193019 27565652384440292142289529)
    ·
      refine ⟨20674239288330219106717147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27565652384440292142289529 20674239288330219106717147)
      ·
        refine ⟨31011358932495328660075721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20674239288330219106717147 31011358932495328660075721)
        ·
          refine ⟨23258519199371496495056791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31011358932495328660075721 23258519199371496495056791)
          ·
            refine ⟨34887778799057244742585187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23258519199371496495056791 34887778799057244742585187)
            ·
              refine ⟨52331668198585867113877781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34887778799057244742585187 52331668198585867113877781)
              ·
                refine ⟨2453046946808712520963021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 52331668198585867113877781 2453046946808712520963021)
                ·
                  refine ⟨919892605053267195361133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2453046946808712520963021 919892605053267195361133)
                  ·
                    refine ⟨344959726894975198260425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 919892605053267195361133 344959726894975198260425)
                    ·
                      refine ⟨258719795171231398695319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 344959726894975198260425 258719795171231398695319)
                      ·
                        rfl

theorem cell23_503855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 6, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 6, 3, 3, 2].length) (baseStart_503855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_503855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_503855 prefixEnd_503855 := by exact prefixLift 503855
  have htrace : WordTrace (prefixWord ++ tailWord_503855) baseStart_503855 baseEnd_503855 := by
    simpa [prefixWord, tailWord_503855, baseEnd_503855] using wordTrace_append hprefix tailTrace_503855
  have hstable : (prefixWord ++ tailWord_503855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503855).length < 2 ^ (prefixWord ++ tailWord_503855).sum := by decide
  have hdescent : baseEnd_503855 < baseStart_503855 := by decide
  rcases family_descends (prefixWord ++ tailWord_503855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503872 : List Nat := [2, 1, 1, 2, 2, 4, 1, 4, 1, 3, 2]
def baseStart_503872 : Nat := 118140960795 + 503872 * 2 ^ 59
def prefixEnd_503872 : Nat := 4983230072969 + 3 ^ 40 * 503872 * 2
def baseEnd_503872 : Nat := 258728524342357832182741

theorem tailTrace_503872 : CollatzResearch.WordTrace tailWord_503872 prefixEnd_503872 258728524342357832182741 := by
  unfold tailWord_503872
  simp only [CollatzResearch.WordTrace]
  refine ⟨9188860815282636665780935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12251814420376848887707913 9188860815282636665780935)
  ·
    refine ⟨13783291222923954998671403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9188860815282636665780935 13783291222923954998671403)
    ·
      refine ⟨20674936834385932498007105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13783291222923954998671403 20674936834385932498007105)
      ·
        refine ⟨15506202625789449373505329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20674936834385932498007105 15506202625789449373505329)
        ·
          refine ⟨11629651969342087030128997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15506202625789449373505329 11629651969342087030128997)
          ·
            refine ⟨2180559744251641318149187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11629651969342087030128997 2180559744251641318149187)
            ·
              refine ⟨3270839616377461977223781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2180559744251641318149187 3270839616377461977223781)
              ·
                refine ⟨613282428070774120729459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3270839616377461977223781 613282428070774120729459)
                ·
                  refine ⟨919923642106161181094189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 613282428070774120729459 919923642106161181094189)
                  ·
                    refine ⟨344971365789810442910321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 919923642106161181094189 344971365789810442910321)
                    ·
                      refine ⟨258728524342357832182741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 344971365789810442910321 258728524342357832182741)
                      ·
                        rfl

theorem cell23_503872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 4, 1, 3, 2].length) (baseStart_503872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_503872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_503872 prefixEnd_503872 := by exact prefixLift 503872
  have htrace : WordTrace (prefixWord ++ tailWord_503872) baseStart_503872 baseEnd_503872 := by
    simpa [prefixWord, tailWord_503872, baseEnd_503872] using wordTrace_append hprefix tailTrace_503872
  have hstable : (prefixWord ++ tailWord_503872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503872).length < 2 ^ (prefixWord ++ tailWord_503872).sum := by decide
  have hdescent : baseEnd_503872 < baseStart_503872 := by decide
  rcases family_descends (prefixWord ++ tailWord_503872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503888 : List Nat := [2, 1, 1, 1, 1, 3, 1, 1, 3, 6, 3]
def baseStart_503888 : Nat := 118140960795 + 503888 * 2 ^ 59
def prefixEnd_503888 : Nat := 4983230072969 + 3 ^ 40 * 503888 * 2
def baseEnd_503888 : Nat := 258736740032829769582667

theorem tailTrace_503888 : CollatzResearch.WordTrace tailWord_503888 prefixEnd_503888 258736740032829769582667 := by
  unfold tailWord_503888
  simp only [CollatzResearch.WordTrace]
  refine ⟨9189152599253654032072159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12252203465671538709429545 9189152599253654032072159)
  ·
    refine ⟨13783728898880481048108239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9189152599253654032072159 13783728898880481048108239)
    ·
      refine ⟨20675593348320721572162359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13783728898880481048108239 20675593348320721572162359)
      ·
        refine ⟨31013390022481082358243539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20675593348320721572162359 31013390022481082358243539)
        ·
          refine ⟨46520085033721623537365309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31013390022481082358243539 46520085033721623537365309)
          ·
            refine ⟨17445031887645608826511991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46520085033721623537365309 17445031887645608826511991)
            ·
              refine ⟨26167547831468413239767987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17445031887645608826511991 26167547831468413239767987)
              ·
                refine ⟨39251321747202619859651981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26167547831468413239767987 39251321747202619859651981)
                ·
                  refine ⟨14719245655200982447369493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39251321747202619859651981 14719245655200982447369493)
                  ·
                    refine ⟨689964640087546052220445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14719245655200982447369493 689964640087546052220445)
                    ·
                      refine ⟨258736740032829769582667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 689964640087546052220445 258736740032829769582667)
                      ·
                        rfl

theorem cell23_503888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 3, 6, 3].length) (baseStart_503888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_503888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_503888 prefixEnd_503888 := by exact prefixLift 503888
  have htrace : WordTrace (prefixWord ++ tailWord_503888) baseStart_503888 baseEnd_503888 := by
    simpa [prefixWord, tailWord_503888, baseEnd_503888] using wordTrace_append hprefix tailTrace_503888
  have hstable : (prefixWord ++ tailWord_503888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503888).length < 2 ^ (prefixWord ++ tailWord_503888).sum := by decide
  have hdescent : baseEnd_503888 < baseStart_503888 := by decide
  rcases family_descends (prefixWord ++ tailWord_503888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503919 : List Nat := [1, 1, 2, 1, 3, 5, 1, 3, 2, 2, 2]
def baseStart_503919 : Nat := 118140960795 + 503919 * 2 ^ 59
def prefixEnd_503919 : Nat := 4983230072969 + 3 ^ 40 * 503919 * 2
def baseEnd_503919 : Nat := 258752657933119148295025

theorem tailTrace_503919 : CollatzResearch.WordTrace tailWord_503919 prefixEnd_503919 258752657933119148295025 := by
  unfold tailWord_503919
  simp only [CollatzResearch.WordTrace]
  refine ⟨18379435861395000358522811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12252957240930000239015207 18379435861395000358522811)
  ·
    refine ⟨27569153792092500537784217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18379435861395000358522811 27569153792092500537784217)
    ·
      refine ⟨20676865344069375403338163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27569153792092500537784217 20676865344069375403338163)
      ·
        refine ⟨31015298016104063105007245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20676865344069375403338163 31015298016104063105007245)
        ·
          refine ⟨11630736756039023664377717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31015298016104063105007245 11630736756039023664377717)
          ·
            refine ⟨1090381570878658468535411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11630736756039023664377717 1090381570878658468535411)
            ·
              refine ⟨1635572356317987702803117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1090381570878658468535411 1635572356317987702803117)
              ·
                refine ⟨613339633619245388551169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1635572356317987702803117 613339633619245388551169)
                ·
                  refine ⟨460004725214434041413377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 613339633619245388551169 460004725214434041413377)
                  ·
                    refine ⟨345003543910825531060033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 460004725214434041413377 345003543910825531060033)
                    ·
                      refine ⟨258752657933119148295025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 345003543910825531060033 258752657933119148295025)
                      ·
                        rfl

theorem cell23_503919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 3, 2, 2, 2].length) (baseStart_503919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_503919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_503919 prefixEnd_503919 := by exact prefixLift 503919
  have htrace : WordTrace (prefixWord ++ tailWord_503919) baseStart_503919 baseEnd_503919 := by
    simpa [prefixWord, tailWord_503919, baseEnd_503919] using wordTrace_append hprefix tailTrace_503919
  have hstable : (prefixWord ++ tailWord_503919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503919).length < 2 ^ (prefixWord ++ tailWord_503919).sum := by decide
  have hdescent : baseEnd_503919 < baseStart_503919 := by decide
  rcases family_descends (prefixWord ++ tailWord_503919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503965 : List Nat := [1, 4, 2, 1, 1, 3, 2, 1, 1, 2, 5]
def baseStart_503965 : Nat := 118140960795 + 503965 * 2 ^ 59
def prefixEnd_503965 : Nat := 4983230072969 + 3 ^ 40 * 503965 * 2
def baseEnd_503965 : Nat := 258776278043225968319813

theorem tailTrace_503965 : CollatzResearch.WordTrace tailWord_503965 prefixEnd_503965 258776278043225968319813 := by
  unfold tailWord_503965
  simp only [CollatzResearch.WordTrace]
  refine ⟨18381113619228350214697349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12254075746152233476464899 18381113619228350214697349)
  ·
    refine ⟨3446458803605315665255753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18381113619228350214697349 3446458803605315665255753)
    ·
      refine ⟨2584844102703986748941815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3446458803605315665255753 2584844102703986748941815)
      ·
        refine ⟨3877266154055980123412723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2584844102703986748941815 3877266154055980123412723)
        ·
          refine ⟨5815899231083970185119085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3877266154055980123412723 5815899231083970185119085)
          ·
            refine ⟨2180962211656488819419657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5815899231083970185119085 2180962211656488819419657)
            ·
              refine ⟨1635721658742366614564743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2180962211656488819419657 1635721658742366614564743)
              ·
                refine ⟨2453582488113549921847115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1635721658742366614564743 2453582488113549921847115)
                ·
                  refine ⟨3680373732170324882770673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2453582488113549921847115 3680373732170324882770673)
                  ·
                    refine ⟨2760280299127743662078005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3680373732170324882770673 2760280299127743662078005)
                    ·
                      refine ⟨258776278043225968319813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2760280299127743662078005 258776278043225968319813)
                      ·
                        rfl

theorem cell23_503965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 1, 1, 2, 5].length) (baseStart_503965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_503965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_503965 prefixEnd_503965 := by exact prefixLift 503965
  have htrace : WordTrace (prefixWord ++ tailWord_503965) baseStart_503965 baseEnd_503965 := by
    simpa [prefixWord, tailWord_503965, baseEnd_503965] using wordTrace_append hprefix tailTrace_503965
  have hstable : (prefixWord ++ tailWord_503965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503965).length < 2 ^ (prefixWord ++ tailWord_503965).sum := by decide
  have hdescent : baseEnd_503965 < baseStart_503965 := by decide
  rcases family_descends (prefixWord ++ tailWord_503965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_503995 : List Nat := [1, 1, 1, 1, 1, 2, 7, 1, 1, 4, 3]
def baseStart_503995 : Nat := 118140960795 + 503995 * 2 ^ 59
def prefixEnd_503995 : Nat := 4983230072969 + 3 ^ 40 * 503995 * 2
def baseEnd_503995 : Nat := 258791682462860850944675

theorem tailTrace_503995 : CollatzResearch.WordTrace tailWord_503995 prefixEnd_503995 258791682462860850944675 := by
  unfold tailWord_503995
  simp only [CollatzResearch.WordTrace]
  refine ⟨18382207809119665338289439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12254805206079776892192959 18382207809119665338289439)
  ·
    refine ⟨27573311713679498007434159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18382207809119665338289439 27573311713679498007434159)
    ·
      refine ⟨41359967570519247011151239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27573311713679498007434159 41359967570519247011151239)
      ·
        refine ⟨62039951355778870516726859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41359967570519247011151239 62039951355778870516726859)
        ·
          refine ⟨93059927033668305775090289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62039951355778870516726859 93059927033668305775090289)
          ·
            refine ⟨69794945275251229331317717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93059927033668305775090289 69794945275251229331317717)
            ·
              refine ⟨1635819029888700687452759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 69794945275251229331317717 1635819029888700687452759)
              ·
                refine ⟨2453728544833051031179139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1635819029888700687452759 2453728544833051031179139)
                ·
                  refine ⟨3680592817249576546768709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2453728544833051031179139 3680592817249576546768709)
                  ·
                    refine ⟨690111153234295602519133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3680592817249576546768709 690111153234295602519133)
                    ·
                      refine ⟨258791682462860850944675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 690111153234295602519133 258791682462860850944675)
                      ·
                        rfl

theorem cell23_503995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 1, 1, 4, 3].length) (baseStart_503995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_503995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_503995 prefixEnd_503995 := by exact prefixLift 503995
  have htrace : WordTrace (prefixWord ++ tailWord_503995) baseStart_503995 baseEnd_503995 := by
    simpa [prefixWord, tailWord_503995, baseEnd_503995] using wordTrace_append hprefix tailTrace_503995
  have hstable : (prefixWord ++ tailWord_503995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_503995).length < 2 ^ (prefixWord ++ tailWord_503995).sum := by decide
  have hdescent : baseEnd_503995 < baseStart_503995 := by decide
  rcases family_descends (prefixWord ++ tailWord_503995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504032 : List Nat := [2, 1, 1, 3, 1, 3, 5, 1, 6]
def baseStart_504032 : Nat := 118140960795 + 504032 * 2 ^ 59
def prefixEnd_504032 : Nat := 4983230072969 + 3 ^ 40 * 504032 * 2
def baseEnd_504032 : Nat := 28756742360786356242445

theorem tailTrace_504032 : CollatzResearch.WordTrace tailWord_504032 prefixEnd_504032 28756742360786356242445 := by
  unfold tailWord_504032
  simp only [CollatzResearch.WordTrace]
  refine ⟨9191778654992810328693175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12255704873323747104924233 9191778654992810328693175)
  ·
    refine ⟨13787667982489215493039763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9191778654992810328693175 13787667982489215493039763)
    ·
      refine ⟨20681501973733823239559645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13787667982489215493039763 20681501973733823239559645)
      ·
        refine ⟨7755563240150183714834867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20681501973733823239559645 7755563240150183714834867)
        ·
          refine ⟨11633344860225275572252301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7755563240150183714834867 11633344860225275572252301)
          ·
            refine ⟨4362504322584478339594613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11633344860225275572252301 4362504322584478339594613)
            ·
              refine ⟨408984780242294844336995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4362504322584478339594613 408984780242294844336995)
              ·
                refine ⟨613477170363442266505493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 408984780242294844336995 613477170363442266505493)
                ·
                  refine ⟨28756742360786356242445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 613477170363442266505493 28756742360786356242445)
                  ·
                    rfl

theorem cell23_504032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 5, 1, 6].length) (baseStart_504032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_504032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_504032 prefixEnd_504032 := by exact prefixLift 504032
  have htrace : WordTrace (prefixWord ++ tailWord_504032) baseStart_504032 baseEnd_504032 := by
    simpa [prefixWord, tailWord_504032, baseEnd_504032] using wordTrace_append hprefix tailTrace_504032
  have hstable : (prefixWord ++ tailWord_504032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504032).length < 2 ^ (prefixWord ++ tailWord_504032).sum := by decide
  have hdescent : baseEnd_504032 < baseStart_504032 := by decide
  rcases family_descends (prefixWord ++ tailWord_504032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504099 : List Nat := [1, 1, 1, 4, 2, 2, 2, 1, 5, 2, 2]
def baseStart_504099 : Nat := 118140960795 + 504099 * 2 ^ 59
def prefixEnd_504099 : Nat := 4983230072969 + 3 ^ 40 * 504099 * 2
def baseEnd_504099 : Nat := 258845084450928444044197

theorem tailTrace_504099 : CollatzResearch.WordTrace tailWord_504099 prefixEnd_504099 258845084450928444044197 := by
  unfold tailWord_504099
  simp only [CollatzResearch.WordTrace]
  refine ⟨18386001000742891100075351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12257334000495260733383567 18386001000742891100075351)
  ·
    refine ⟨27579001501114336650113027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18386001000742891100075351 27579001501114336650113027)
    ·
      refine ⟨41368502251671504975169541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27579001501114336650113027 41368502251671504975169541)
      ·
        refine ⟨7756594172188407182844289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41368502251671504975169541 7756594172188407182844289)
        ·
          refine ⟨5817445629141305387133217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7756594172188407182844289 5817445629141305387133217)
          ·
            refine ⟨4363084221855979040349913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5817445629141305387133217 4363084221855979040349913)
            ·
              refine ⟨3272313166391984280262435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4363084221855979040349913 3272313166391984280262435)
              ·
                refine ⟨4908469749587976420393653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3272313166391984280262435 4908469749587976420393653)
                ·
                  refine ⟨460169039023872789411905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4908469749587976420393653 460169039023872789411905)
                  ·
                    refine ⟨345126779267904592058929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 460169039023872789411905 345126779267904592058929)
                    ·
                      refine ⟨258845084450928444044197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 345126779267904592058929 258845084450928444044197)
                      ·
                        rfl

theorem cell23_504099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 1, 5, 2, 2].length) (baseStart_504099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_504099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_504099 prefixEnd_504099 := by exact prefixLift 504099
  have htrace : WordTrace (prefixWord ++ tailWord_504099) baseStart_504099 baseEnd_504099 := by
    simpa [prefixWord, tailWord_504099, baseEnd_504099] using wordTrace_append hprefix tailTrace_504099
  have hstable : (prefixWord ++ tailWord_504099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504099).length < 2 ^ (prefixWord ++ tailWord_504099).sum := by decide
  have hdescent : baseEnd_504099 < baseStart_504099 := by decide
  rcases family_descends (prefixWord ++ tailWord_504099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504126 : List Nat := [4, 2, 1, 2, 1, 3, 2, 2, 2, 4]
def baseStart_504126 : Nat := 118140960795 + 504126 * 2 ^ 59
def prefixEnd_504126 : Nat := 4983230072969 + 3 ^ 40 * 504126 * 2
def baseEnd_504126 : Nat := 86286316142866612802191

theorem tailTrace_504126 : CollatzResearch.WordTrace tailWord_504126 prefixEnd_504126 86286316142866612802191 := by
  unfold tailWord_504126
  simp only [CollatzResearch.WordTrace]
  refine ⟨2298373221455634338913529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12257990514430049807538821 2298373221455634338913529)
  ·
    refine ⟨1723779916091725754185147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2298373221455634338913529 1723779916091725754185147)
    ·
      refine ⟨2585669874137588631277721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1723779916091725754185147 2585669874137588631277721)
      ·
        refine ⟨1939252405603191473458291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2585669874137588631277721 1939252405603191473458291)
        ·
          refine ⟨2908878608404787210187437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1939252405603191473458291 2908878608404787210187437)
          ·
            refine ⟨1090829478151795203820289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2908878608404787210187437 1090829478151795203820289)
            ·
              refine ⟨818122108613846402865217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1090829478151795203820289 818122108613846402865217)
              ·
                refine ⟨613591581460384802148913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 818122108613846402865217 613591581460384802148913)
                ·
                  refine ⟨460193686095288601611685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 613591581460384802148913 460193686095288601611685)
                  ·
                    refine ⟨86286316142866612802191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 460193686095288601611685 86286316142866612802191)
                    ·
                      rfl

theorem cell23_504126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 2, 2, 2, 4].length) (baseStart_504126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_504126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_504126 prefixEnd_504126 := by exact prefixLift 504126
  have htrace : WordTrace (prefixWord ++ tailWord_504126) baseStart_504126 baseEnd_504126 := by
    simpa [prefixWord, tailWord_504126, baseEnd_504126] using wordTrace_append hprefix tailTrace_504126
  have hstable : (prefixWord ++ tailWord_504126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504126).length < 2 ^ (prefixWord ++ tailWord_504126).sum := by decide
  have hdescent : baseEnd_504126 < baseStart_504126 := by decide
  rcases family_descends (prefixWord ++ tailWord_504126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504135 : List Nat := [1, 1, 4, 1, 2, 2, 1, 1, 1, 9]
def baseStart_504135 : Nat := 118140960795 + 504135 * 2 ^ 59
def prefixEnd_504135 : Nat := 4983230072969 + 3 ^ 40 * 504135 * 2
def baseEnd_504135 : Nat := 86287856584830101064677

theorem tailTrace_504135 : CollatzResearch.WordTrace tailWord_504135 prefixEnd_504135 86287856584830101064677 := by
  unfold tailWord_504135
  simp only [CollatzResearch.WordTrace]
  refine ⟨18387314028612469248385859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12258209352408312832257239 18387314028612469248385859)
  ·
    refine ⟨27580971042918703872578789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18387314028612469248385859 27580971042918703872578789)
    ·
      refine ⟨5171432070547256976108523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27580971042918703872578789 5171432070547256976108523)
      ·
        refine ⟨7757148105820885464162785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5171432070547256976108523 7757148105820885464162785)
        ·
          refine ⟨5817861079365664098122089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7757148105820885464162785 5817861079365664098122089)
          ·
            refine ⟨4363395809524248073591567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5817861079365664098122089 4363395809524248073591567)
            ·
              refine ⟨6545093714286372110387351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4363395809524248073591567 6545093714286372110387351)
              ·
                refine ⟨9817640571429558165581027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6545093714286372110387351 9817640571429558165581027)
                ·
                  refine ⟨14726460857144337248371541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9817640571429558165581027 14726460857144337248371541)
                  ·
                    refine ⟨86287856584830101064677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 14726460857144337248371541 86287856584830101064677)
                    ·
                      rfl

theorem cell23_504135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 1, 1, 9].length) (baseStart_504135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_504135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_504135 prefixEnd_504135 := by exact prefixLift 504135
  have htrace : WordTrace (prefixWord ++ tailWord_504135) baseStart_504135 baseEnd_504135 := by
    simpa [prefixWord, tailWord_504135, baseEnd_504135] using wordTrace_append hprefix tailTrace_504135
  have hstable : (prefixWord ++ tailWord_504135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504135).length < 2 ^ (prefixWord ++ tailWord_504135).sum := by decide
  have hdescent : baseEnd_504135 < baseStart_504135 := by decide
  rcases family_descends (prefixWord ++ tailWord_504135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504155 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 2, 9, 4]
def baseStart_504155 : Nat := 118140960795 + 504155 * 2 ^ 59
def prefixEnd_504155 : Nat := 4983230072969 + 3 ^ 40 * 504155 * 2
def baseEnd_504155 : Nat := 258873839367580224943939

theorem tailTrace_504155 : CollatzResearch.WordTrace tailWord_504155 prefixEnd_504155 258873839367580224943939 := by
  unfold tailWord_504155
  simp only [CollatzResearch.WordTrace]
  refine ⟨18388043488540012664113919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12258695659026675109409279 18388043488540012664113919)
  ·
    refine ⟨27582065232810018996170879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18388043488540012664113919 27582065232810018996170879)
    ·
      refine ⟨41373097849215028494256319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27582065232810018996170879 41373097849215028494256319)
      ·
        refine ⟨62059646773822542741384479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41373097849215028494256319 62059646773822542741384479)
        ·
          refine ⟨93089470160733814112076719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62059646773822542741384479 93089470160733814112076719)
          ·
            refine ⟨139634205241100721168115079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93089470160733814112076719 139634205241100721168115079)
            ·
              refine ⟨209451307861651081752172619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139634205241100721168115079 209451307861651081752172619)
              ·
                refine ⟨314176961792476622628258929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 209451307861651081752172619 314176961792476622628258929)
                ·
                  refine ⟨235632721344357466971194197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 314176961792476622628258929 235632721344357466971194197)
                  ·
                    refine ⟨1380660476627094533034341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 235632721344357466971194197 1380660476627094533034341)
                    ·
                      refine ⟨258873839367580224943939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1380660476627094533034341 258873839367580224943939)
                      ·
                        rfl

theorem cell23_504155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 9, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 9, 4].length) (baseStart_504155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_504155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_504155 prefixEnd_504155 := by exact prefixLift 504155
  have htrace : WordTrace (prefixWord ++ tailWord_504155) baseStart_504155 baseEnd_504155 := by
    simpa [prefixWord, tailWord_504155, baseEnd_504155] using wordTrace_append hprefix tailTrace_504155
  have hstable : (prefixWord ++ tailWord_504155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504155).length < 2 ^ (prefixWord ++ tailWord_504155).sum := by decide
  have hdescent : baseEnd_504155 < baseStart_504155 := by decide
  rcases family_descends (prefixWord ++ tailWord_504155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504156 : List Nat := [2, 2, 4, 3, 1, 1, 3, 7]
def baseStart_504156 : Nat := 118140960795 + 504156 * 2 ^ 59
def prefixEnd_504156 : Nat := 4983230072969 + 3 ^ 40 * 504156 * 2
def baseEnd_504156 : Nat := 9587938994379063741905

theorem tailTrace_504156 : CollatzResearch.WordTrace tailWord_504156 prefixEnd_504156 9587938994379063741905 := by
  unfold tailWord_504156
  simp only [CollatzResearch.WordTrace]
  refine ⟨9194039980768194917450161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12258719974357593223266881 9194039980768194917450161)
  ·
    refine ⟨6895529985576146188087621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9194039980768194917450161 6895529985576146188087621)
    ·
      refine ⟨1292911872295527410266429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6895529985576146188087621 1292911872295527410266429)
      ·
        refine ⟨484841952110822778849911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1292911872295527410266429 484841952110822778849911)
        ·
          refine ⟨727262928166234168274867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 484841952110822778849911 727262928166234168274867)
          ·
            refine ⟨1090894392249351252412301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 727262928166234168274867 1090894392249351252412301)
            ·
              refine ⟨409085397093506719654613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1090894392249351252412301 409085397093506719654613)
              ·
                refine ⟨9587938994379063741905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 409085397093506719654613 9587938994379063741905)
                ·
                  rfl

theorem cell23_504156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 3, 7].length) (baseStart_504156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_504156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_504156 prefixEnd_504156 := by exact prefixLift 504156
  have htrace : WordTrace (prefixWord ++ tailWord_504156) baseStart_504156 baseEnd_504156 := by
    simpa [prefixWord, tailWord_504156, baseEnd_504156] using wordTrace_append hprefix tailTrace_504156
  have hstable : (prefixWord ++ tailWord_504156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504156).length < 2 ^ (prefixWord ++ tailWord_504156).sum := by decide
  have hdescent : baseEnd_504156 < baseStart_504156 := by decide
  rcases family_descends (prefixWord ++ tailWord_504156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504159 : List Nat := [1, 1, 2, 3, 1, 2, 4, 1, 3, 3, 2]
def baseStart_504159 : Nat := 118140960795 + 504159 * 2 ^ 59
def prefixEnd_504159 : Nat := 4983230072969 + 3 ^ 40 * 504159 * 2
def baseEnd_504159 : Nat := 258875893290198209293921

theorem tailTrace_504159 : CollatzResearch.WordTrace tailWord_504159 prefixEnd_504159 258875893290198209293921 := by
  unfold tailWord_504159
  simp only [CollatzResearch.WordTrace]
  refine ⟨18388189380525521347259531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12258792920350347564839687 18388189380525521347259531)
  ·
    refine ⟨27582284070788282020889297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18388189380525521347259531 27582284070788282020889297)
    ·
      refine ⟨20686713053091211515666973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27582284070788282020889297 20686713053091211515666973)
      ·
        refine ⟨7757517394909204318375115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20686713053091211515666973 7757517394909204318375115)
        ·
          refine ⟨11636276092363806477562673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7757517394909204318375115 11636276092363806477562673)
          ·
            refine ⟨8727207069272854858172005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11636276092363806477562673 8727207069272854858172005)
            ·
              refine ⟨1636351325488660285907251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8727207069272854858172005 1636351325488660285907251)
              ·
                refine ⟨2454526988232990428860877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1636351325488660285907251 2454526988232990428860877)
                ·
                  refine ⟨920447620587371410822829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2454526988232990428860877 920447620587371410822829)
                  ·
                    refine ⟨345167857720264279058561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 920447620587371410822829 345167857720264279058561)
                    ·
                      refine ⟨258875893290198209293921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 345167857720264279058561 258875893290198209293921)
                      ·
                        rfl

theorem cell23_504159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 1, 3, 3, 2].length) (baseStart_504159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_504159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_504159 prefixEnd_504159 := by exact prefixLift 504159
  have htrace : WordTrace (prefixWord ++ tailWord_504159) baseStart_504159 baseEnd_504159 := by
    simpa [prefixWord, tailWord_504159, baseEnd_504159] using wordTrace_append hprefix tailTrace_504159
  have hstable : (prefixWord ++ tailWord_504159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504159).length < 2 ^ (prefixWord ++ tailWord_504159).sum := by decide
  have hdescent : baseEnd_504159 < baseStart_504159 := by decide
  rcases family_descends (prefixWord ++ tailWord_504159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504176 : List Nat := [2, 1, 1, 1, 4, 4, 1, 3, 1, 3, 2]
def baseStart_504176 : Nat := 118140960795 + 504176 * 2 ^ 59
def prefixEnd_504176 : Nat := 4983230072969 + 3 ^ 40 * 504176 * 2
def baseEnd_504176 : Nat := 258884622461324642781343

theorem tailTrace_504176 : CollatzResearch.WordTrace tailWord_504176 prefixEnd_504176 258884622461324642781343 := by
  unfold tailWord_504176
  simp only [CollatzResearch.WordTrace]
  refine ⟨9194404710731966625314191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12259206280975955500418921 9194404710731966625314191)
  ·
    refine ⟨13791607066097949937971287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9194404710731966625314191 13791607066097949937971287)
    ·
      refine ⟨20687410599146924906956931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13791607066097949937971287 20687410599146924906956931)
      ·
        refine ⟨31031115898720387360435397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20687410599146924906956931 31031115898720387360435397)
        ·
          refine ⟨5818334231010072630081637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31031115898720387360435397 5818334231010072630081637)
          ·
            refine ⟨1090937668314388618140307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5818334231010072630081637 1090937668314388618140307)
            ·
              refine ⟨1636406502471582927210461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1090937668314388618140307 1636406502471582927210461)
              ·
                refine ⟨613652438426843597703923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1636406502471582927210461 613652438426843597703923)
                ·
                  refine ⟨920478657640265396555885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 613652438426843597703923 920478657640265396555885)
                  ·
                    refine ⟨345179496615099523708457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 920478657640265396555885 345179496615099523708457)
                    ·
                      refine ⟨258884622461324642781343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 345179496615099523708457 258884622461324642781343)
                      ·
                        rfl

theorem cell23_504176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 3, 1, 3, 2].length) (baseStart_504176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_504176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_504176 prefixEnd_504176 := by exact prefixLift 504176
  have htrace : WordTrace (prefixWord ++ tailWord_504176) baseStart_504176 baseEnd_504176 := by
    simpa [prefixWord, tailWord_504176, baseEnd_504176] using wordTrace_append hprefix tailTrace_504176
  have hstable : (prefixWord ++ tailWord_504176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504176).length < 2 ^ (prefixWord ++ tailWord_504176).sum := by decide
  have hdescent : baseEnd_504176 < baseStart_504176 := by decide
  rcases family_descends (prefixWord ++ tailWord_504176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504276 : List Nat := [2, 4, 1, 2, 2, 2, 2, 1, 2, 5]
def baseStart_504276 : Nat := 118140960795 + 504276 * 2 ^ 59
def prefixEnd_504276 : Nat := 4983230072969 + 3 ^ 40 * 504276 * 2
def baseEnd_504276 : Nat := 86311990175591417176961

theorem tailTrace_504276 : CollatzResearch.WordTrace tailWord_504276 prefixEnd_504276 86311990175591417176961 := by
  unfold tailWord_504276
  simp only [CollatzResearch.WordTrace]
  refine ⟨9196228360550825164634341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12261637814067766886179121 9196228360550825164634341)
  ·
    refine ⟨1724292817603279718368939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9196228360550825164634341 1724292817603279718368939)
    ·
      refine ⟨2586439226404919577553409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1724292817603279718368939 2586439226404919577553409)
      ·
        refine ⟨1939829419803689683165057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2586439226404919577553409 1939829419803689683165057)
        ·
          refine ⟨1454872064852767262373793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1939829419803689683165057 1454872064852767262373793)
          ·
            refine ⟨1091154048639575446780345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1454872064852767262373793 1091154048639575446780345)
            ·
              refine ⟨818365536479681585085259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1091154048639575446780345 818365536479681585085259)
              ·
                refine ⟨1227548304719522377627889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 818365536479681585085259 1227548304719522377627889)
                ·
                  refine ⟨920661228539641783220917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1227548304719522377627889 920661228539641783220917)
                  ·
                    refine ⟨86311990175591417176961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 920661228539641783220917 86311990175591417176961)
                    ·
                      rfl

theorem cell23_504276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 2, 1, 2, 5].length) (baseStart_504276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_504276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_504276 prefixEnd_504276 := by exact prefixLift 504276
  have htrace : WordTrace (prefixWord ++ tailWord_504276) baseStart_504276 baseEnd_504276 := by
    simpa [prefixWord, tailWord_504276, baseEnd_504276] using wordTrace_append hprefix tailTrace_504276
  have hstable : (prefixWord ++ tailWord_504276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504276).length < 2 ^ (prefixWord ++ tailWord_504276).sum := by decide
  have hdescent : baseEnd_504276 < baseStart_504276 := by decide
  rcases family_descends (prefixWord ++ tailWord_504276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504279 : List Nat := [1, 1, 3, 2, 1, 1, 1, 1, 6, 4, 2]
def baseStart_504279 : Nat := 118140960795 + 504279 * 2 ^ 59
def prefixEnd_504279 : Nat := 4983230072969 + 3 ^ 40 * 504279 * 2
def baseEnd_504279 : Nat := 258937510968737739793369

theorem tailTrace_504279 : CollatzResearch.WordTrace tailWord_504279 prefixEnd_504279 258937510968737739793369 := by
  unfold tailWord_504279
  simp only [CollatzResearch.WordTrace]
  refine ⟨18392566140090781841627891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12261710760060521227751927 18392566140090781841627891)
  ·
    refine ⟨27588849210136172762441837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18392566140090781841627891 27588849210136172762441837)
    ·
      refine ⟨10345818453801064785915689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27588849210136172762441837 10345818453801064785915689)
      ·
        refine ⟨7759363840350798589436767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10345818453801064785915689 7759363840350798589436767)
        ·
          refine ⟨11639045760526197884155151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7759363840350798589436767 11639045760526197884155151)
          ·
            refine ⟨17458568640789296826232727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11639045760526197884155151 17458568640789296826232727)
            ·
              refine ⟨26187852961183945239349091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17458568640789296826232727 26187852961183945239349091)
              ·
                refine ⟨39281779441775917859023637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26187852961183945239349091 39281779441775917859023637)
                ·
                  refine ⟨1841333411333246149641733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 39281779441775917859023637 1841333411333246149641733)
                  ·
                    refine ⟨345250014624983653057825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1841333411333246149641733 345250014624983653057825)
                    ·
                      refine ⟨258937510968737739793369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 345250014624983653057825 258937510968737739793369)
                      ·
                        rfl

theorem cell23_504279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 6, 4, 2].length) (baseStart_504279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_504279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_504279 prefixEnd_504279 := by exact prefixLift 504279
  have htrace : WordTrace (prefixWord ++ tailWord_504279) baseStart_504279 baseEnd_504279 := by
    simpa [prefixWord, tailWord_504279, baseEnd_504279] using wordTrace_append hprefix tailTrace_504279
  have hstable : (prefixWord ++ tailWord_504279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504279).length < 2 ^ (prefixWord ++ tailWord_504279).sum := by decide
  have hdescent : baseEnd_504279 < baseStart_504279 := by decide
  rcases family_descends (prefixWord ++ tailWord_504279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504299 : List Nat := [1, 1, 1, 1, 2, 3, 3, 4, 2, 2, 3]
def baseStart_504299 : Nat := 118140960795 + 504299 * 2 ^ 59
def prefixEnd_504299 : Nat := 4983230072969 + 3 ^ 40 * 504299 * 2
def baseEnd_504299 : Nat := 258947780581827661543277

theorem tailTrace_504299 : CollatzResearch.WordTrace tailWord_504299 prefixEnd_504299 258947780581827661543277 := by
  unfold tailWord_504299
  simp only [CollatzResearch.WordTrace]
  refine ⟨18393295600018325257355951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12262197066678883504903967 18393295600018325257355951)
  ·
    refine ⟨27589943400027487886033927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18393295600018325257355951 27589943400027487886033927)
    ·
      refine ⟨41384915100041231829050891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27589943400027487886033927 41384915100041231829050891)
      ·
        refine ⟨62077372650061847743576337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41384915100041231829050891 62077372650061847743576337)
        ·
          refine ⟨46558029487546385807682253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62077372650061847743576337 46558029487546385807682253)
          ·
            refine ⟨17459261057829894677880845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46558029487546385807682253 17459261057829894677880845)
            ·
              refine ⟨6547222896686210504205317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17459261057829894677880845 6547222896686210504205317)
              ·
                refine ⟨1227604293128664469538497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6547222896686210504205317 1227604293128664469538497)
                ·
                  refine ⟨920703219846498352153873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1227604293128664469538497 920703219846498352153873)
                  ·
                    refine ⟨690527414884873764115405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 920703219846498352153873 690527414884873764115405)
                    ·
                      refine ⟨258947780581827661543277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 690527414884873764115405 258947780581827661543277)
                      ·
                        rfl

theorem cell23_504299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 4, 2, 2, 3].length) (baseStart_504299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_504299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_504299 prefixEnd_504299 := by exact prefixLift 504299
  have htrace : WordTrace (prefixWord ++ tailWord_504299) baseStart_504299 baseEnd_504299 := by
    simpa [prefixWord, tailWord_504299, baseEnd_504299] using wordTrace_append hprefix tailTrace_504299
  have hstable : (prefixWord ++ tailWord_504299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504299).length < 2 ^ (prefixWord ++ tailWord_504299).sum := by decide
  have hdescent : baseEnd_504299 < baseStart_504299 := by decide
  rcases family_descends (prefixWord ++ tailWord_504299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504340 : List Nat := [2, 4, 3, 1, 1, 1, 1, 5, 1, 4]
def baseStart_504340 : Nat := 118140960795 + 504340 * 2 ^ 59
def prefixEnd_504340 : Nat := 4983230072969 + 3 ^ 40 * 504340 * 2
def baseEnd_504340 : Nat := 86322944429554000376863

theorem tailTrace_504340 : CollatzResearch.WordTrace tailWord_504340 prefixEnd_504340 86322944429554000376863 := by
  unfold tailWord_504340
  simp only [CollatzResearch.WordTrace]
  refine ⟨9197395496434894629799237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12263193995246526173065649 9197395496434894629799237)
  ·
    refine ⟨1724511655581542743087357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9197395496434894629799237 1724511655581542743087357)
    ·
      refine ⟨646691870843078528657759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1724511655581542743087357 646691870843078528657759)
      ·
        refine ⟨970037806264617792986639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 646691870843078528657759 970037806264617792986639)
        ·
          refine ⟨1455056709396926689479959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 970037806264617792986639 1455056709396926689479959)
          ·
            refine ⟨2182585064095390034219939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1455056709396926689479959 2182585064095390034219939)
            ·
              refine ⟨3273877596143085051329909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2182585064095390034219939 3273877596143085051329909)
              ·
                refine ⟨306926024638414223562179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3273877596143085051329909 306926024638414223562179)
                ·
                  refine ⟨460389036957621335343269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 306926024638414223562179 460389036957621335343269)
                  ·
                    refine ⟨86322944429554000376863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 460389036957621335343269 86322944429554000376863)
                    ·
                      rfl

theorem cell23_504340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_504340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_504340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_504340 prefixEnd_504340 := by exact prefixLift 504340
  have htrace : WordTrace (prefixWord ++ tailWord_504340) baseStart_504340 baseEnd_504340 := by
    simpa [prefixWord, tailWord_504340, baseEnd_504340] using wordTrace_append hprefix tailTrace_504340
  have hstable : (prefixWord ++ tailWord_504340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504340).length < 2 ^ (prefixWord ++ tailWord_504340).sum := by decide
  have hdescent : baseEnd_504340 < baseStart_504340 := by decide
  rcases family_descends (prefixWord ++ tailWord_504340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504369 : List Nat := [1, 2, 2, 3, 1, 1, 2, 1, 5, 1, 4]
def baseStart_504369 : Nat := 118140960795 + 504369 * 2 ^ 59
def prefixEnd_504369 : Nat := 4983230072969 + 3 ^ 40 * 504369 * 2
def baseEnd_504369 : Nat := 258983724227642387667955

theorem tailTrace_504369 : CollatzResearch.WordTrace tailWord_504369 prefixEnd_504369 258983724227642387667955 := by
  unfold tailWord_504369
  simp only [CollatzResearch.WordTrace]
  refine ⟨18395848709764727212404161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12263899139843151474936107 18395848709764727212404161)
  ·
    refine ⟨13796886532323545409303121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18395848709764727212404161 13796886532323545409303121)
    ·
      refine ⟨10347664899242659056977341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13796886532323545409303121 10347664899242659056977341)
      ·
        refine ⟨3880374337215997146366503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10347664899242659056977341 3880374337215997146366503)
        ·
          refine ⟨5820561505823995719549755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3880374337215997146366503 5820561505823995719549755)
          ·
            refine ⟨8730842258735993579324633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5820561505823995719549755 8730842258735993579324633)
            ·
              refine ⟨6548131694051995184493475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8730842258735993579324633 6548131694051995184493475)
              ·
                refine ⟨9822197541077992776740213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6548131694051995184493475 9822197541077992776740213)
                ·
                  refine ⟨920831019476061822819395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9822197541077992776740213 920831019476061822819395)
                  ·
                    refine ⟨1381246529214092734229093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 920831019476061822819395 1381246529214092734229093)
                    ·
                      refine ⟨258983724227642387667955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1381246529214092734229093 258983724227642387667955)
                      ·
                        rfl

theorem cell23_504369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 1, 5, 1, 4].length) (baseStart_504369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_504369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_504369 prefixEnd_504369 := by exact prefixLift 504369
  have htrace : WordTrace (prefixWord ++ tailWord_504369) baseStart_504369 baseEnd_504369 := by
    simpa [prefixWord, tailWord_504369, baseEnd_504369] using wordTrace_append hprefix tailTrace_504369
  have hstable : (prefixWord ++ tailWord_504369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504369).length < 2 ^ (prefixWord ++ tailWord_504369).sum := by decide
  have hdescent : baseEnd_504369 < baseStart_504369 := by decide
  rcases family_descends (prefixWord ++ tailWord_504369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504390 : List Nat := [6, 1, 1, 1, 2, 1, 2, 1, 1, 5, 2]
def baseStart_504390 : Nat := 118140960795 + 504390 * 2 ^ 59
def prefixEnd_504390 : Nat := 4983230072969 + 3 ^ 40 * 504390 * 2
def baseEnd_504390 : Nat := 258994507321386805505359

theorem tailTrace_504390 : CollatzResearch.WordTrace tailWord_504390 prefixEnd_504390 258994507321386805505359 := by
  unfold tailWord_504390
  simp only [CollatzResearch.WordTrace]
  refine ⟨574894207584020243716207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 12264409761792431865945749 574894207584020243716207)
  ·
    refine ⟨862341311376030365574311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 574894207584020243716207 862341311376030365574311)
    ·
      refine ⟨1293511967064045548361467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 862341311376030365574311 1293511967064045548361467)
      ·
        refine ⟨1940267950596068322542201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1293511967064045548361467 1940267950596068322542201)
        ·
          refine ⟨1455200962947051241906651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1940267950596068322542201 1455200962947051241906651)
          ·
            refine ⟨2182801444420576862859977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1455200962947051241906651 2182801444420576862859977)
            ·
              refine ⟨1637101083315432647144983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2182801444420576862859977 1637101083315432647144983)
              ·
                refine ⟨2455651624973148970717475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1637101083315432647144983 2455651624973148970717475)
                ·
                  refine ⟨3683477437459723456076213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2455651624973148970717475 3683477437459723456076213)
                  ·
                    refine ⟨345326009761849074007145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3683477437459723456076213 345326009761849074007145)
                    ·
                      refine ⟨258994507321386805505359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 345326009761849074007145 258994507321386805505359)
                      ·
                        rfl

theorem cell23_504390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 1, 1, 5, 2].length) (baseStart_504390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_504390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_504390 prefixEnd_504390 := by exact prefixLift 504390
  have htrace : WordTrace (prefixWord ++ tailWord_504390) baseStart_504390 baseEnd_504390 := by
    simpa [prefixWord, tailWord_504390, baseEnd_504390] using wordTrace_append hprefix tailTrace_504390
  have hstable : (prefixWord ++ tailWord_504390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504390).length < 2 ^ (prefixWord ++ tailWord_504390).sum := by decide
  have hdescent : baseEnd_504390 < baseStart_504390 := by decide
  rcases family_descends (prefixWord ++ tailWord_504390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504397 : List Nat := [1, 6, 1, 1, 2, 1, 3, 3, 1, 1, 3]
def baseStart_504397 : Nat := 118140960795 + 504397 * 2 ^ 59
def prefixEnd_504397 : Nat := 4983230072969 + 3 ^ 40 * 504397 * 2
def baseEnd_504397 : Nat := 258998101685968278117827

theorem tailTrace_504397 : CollatzResearch.WordTrace tailWord_504397 prefixEnd_504397 258998101685968278117827 := by
  unfold tailWord_504397
  simp only [CollatzResearch.WordTrace]
  refine ⟨18396869953663287994423445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12264579969108858662948963 18396869953663287994423445)
  ·
    refine ⟨862353279077966624738599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 18396869953663287994423445 862353279077966624738599)
    ·
      refine ⟨1293529918616949937107899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 862353279077966624738599 1293529918616949937107899)
      ·
        refine ⟨1940294877925424905661849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1293529918616949937107899 1940294877925424905661849)
        ·
          refine ⟨1455221158444068679246387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1940294877925424905661849 1455221158444068679246387)
          ·
            refine ⟨2182831737666103018869581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1455221158444068679246387 2182831737666103018869581)
            ·
              refine ⟨818561901624788632076093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2182831737666103018869581 818561901624788632076093)
              ·
                refine ⟨306960713109295737028535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 818561901624788632076093 306960713109295737028535)
                ·
                  refine ⟨460441069663943605542803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 306960713109295737028535 460441069663943605542803)
                  ·
                    refine ⟨690661604495915408314205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 460441069663943605542803 690661604495915408314205)
                    ·
                      refine ⟨258998101685968278117827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 690661604495915408314205 258998101685968278117827)
                      ·
                        rfl

theorem cell23_504397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 3, 3, 1, 1, 3].length) (baseStart_504397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_504397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_504397 prefixEnd_504397 := by exact prefixLift 504397
  have htrace : WordTrace (prefixWord ++ tailWord_504397) baseStart_504397 baseEnd_504397 := by
    simpa [prefixWord, tailWord_504397, baseEnd_504397] using wordTrace_append hprefix tailTrace_504397
  have hstable : (prefixWord ++ tailWord_504397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504397).length < 2 ^ (prefixWord ++ tailWord_504397).sum := by decide
  have hdescent : baseEnd_504397 < baseStart_504397 := by decide
  rcases family_descends (prefixWord ++ tailWord_504397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504399 : List Nat := [1, 1, 2, 1, 1, 2, 4, 4, 1, 2, 4]
def baseStart_504399 : Nat := 118140960795 + 504399 * 2 ^ 59
def prefixEnd_504399 : Nat := 4983230072969 + 3 ^ 40 * 504399 * 2
def baseEnd_504399 : Nat := 258999128647277270292817

theorem tailTrace_504399 : CollatzResearch.WordTrace tailWord_504399 prefixEnd_504399 258999128647277270292817 := by
  unfold tailWord_504399
  simp only [CollatzResearch.WordTrace]
  refine ⟨18396942899656042335996251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12264628599770694890664167 18396942899656042335996251)
  ·
    refine ⟨27595414349484063503994377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18396942899656042335996251 27595414349484063503994377)
    ·
      refine ⟨20696560762113047627995783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27595414349484063503994377 20696560762113047627995783)
      ·
        refine ⟨31044841143169571441993675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20696560762113047627995783 31044841143169571441993675)
        ·
          refine ⟨46567261714754357162990513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31044841143169571441993675 46567261714754357162990513)
          ·
            refine ⟨34925446286065767872242885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46567261714754357162990513 34925446286065767872242885)
            ·
              refine ⟨6548521178637331476045541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34925446286065767872242885 6548521178637331476045541)
              ·
                refine ⟨1227847720994499651758539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6548521178637331476045541 1227847720994499651758539)
                ·
                  refine ⟨1841771581491749477637809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1227847720994499651758539 1841771581491749477637809)
                  ·
                    refine ⟨1381328686118812108228357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1841771581491749477637809 1381328686118812108228357)
                    ·
                      refine ⟨258999128647277270292817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1381328686118812108228357 258999128647277270292817)
                      ·
                        rfl

theorem cell23_504399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 4, 1, 2, 4].length) (baseStart_504399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_504399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_504399 prefixEnd_504399 := by exact prefixLift 504399
  have htrace : WordTrace (prefixWord ++ tailWord_504399) baseStart_504399 baseEnd_504399 := by
    simpa [prefixWord, tailWord_504399, baseEnd_504399] using wordTrace_append hprefix tailTrace_504399
  have hstable : (prefixWord ++ tailWord_504399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504399).length < 2 ^ (prefixWord ++ tailWord_504399).sum := by decide
  have hdescent : baseEnd_504399 < baseStart_504399 := by decide
  rcases family_descends (prefixWord ++ tailWord_504399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504430 : List Nat := [4, 1, 2, 2, 2, 1, 4, 1, 2, 4]
def baseStart_504430 : Nat := 118140960795 + 504430 * 2 ^ 59
def prefixEnd_504430 : Nat := 4983230072969 + 3 ^ 40 * 504430 * 2
def baseEnd_504430 : Nat := 86338348849188883001725

theorem tailTrace_504430 : CollatzResearch.WordTrace tailWord_504430 prefixEnd_504430 86338348849188883001725 := by
  unfold tailWord_504430
  simp only [CollatzResearch.WordTrace]
  refine ⟨2299759195317966828796843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12265382375029156420249829 2299759195317966828796843)
  ·
    refine ⟨3449638792976950243195265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2299759195317966828796843 3449638792976950243195265)
    ·
      refine ⟨2587229094732712682396449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3449638792976950243195265 2587229094732712682396449)
      ·
        refine ⟨1940421821049534511797337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2587229094732712682396449 1940421821049534511797337)
        ·
          refine ⟨1455316365787150883848003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1940421821049534511797337 1455316365787150883848003)
          ·
            refine ⟨2182974548680726325772005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1455316365787150883848003 2182974548680726325772005)
            ·
              refine ⟨409307727877636186082251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2182974548680726325772005 409307727877636186082251)
              ·
                refine ⟨613961591816454279123377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 409307727877636186082251 613961591816454279123377)
                ·
                  refine ⟨460471193862340709342533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 613961591816454279123377 460471193862340709342533)
                  ·
                    refine ⟨86338348849188883001725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 460471193862340709342533 86338348849188883001725)
                    ·
                      rfl

theorem cell23_504430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 4, 1, 2, 4].length) (baseStart_504430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_504430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_504430 prefixEnd_504430 := by exact prefixLift 504430
  have htrace : WordTrace (prefixWord ++ tailWord_504430) baseStart_504430 baseEnd_504430 := by
    simpa [prefixWord, tailWord_504430, baseEnd_504430] using wordTrace_append hprefix tailTrace_504430
  have hstable : (prefixWord ++ tailWord_504430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504430).length < 2 ^ (prefixWord ++ tailWord_504430).sum := by decide
  have hdescent : baseEnd_504430 < baseStart_504430 := by decide
  rcases family_descends (prefixWord ++ tailWord_504430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504437 : List Nat := [1, 3, 4, 2, 3, 1, 1, 2, 1, 1, 4]
def baseStart_504437 : Nat := 118140960795 + 504437 * 2 ^ 59
def prefixEnd_504437 : Nat := 4983230072969 + 3 ^ 40 * 504437 * 2
def baseEnd_504437 : Nat := 259018640912148121617643

theorem tailTrace_504437 : CollatzResearch.WordTrace tailWord_504437 prefixEnd_504437 259018640912148121617643 := by
  unfold tailWord_504437
  simp only [CollatzResearch.WordTrace]
  refine ⟨18398328873518374825879565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12265552582345583217253043 18398328873518374825879565)
  ·
    refine ⟨6899373327569390559704837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18398328873518374825879565 6899373327569390559704837)
    ·
      refine ⟨1293632498919260729944657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6899373327569390559704837 1293632498919260729944657)
      ·
        refine ⟨970224374189445547458493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1293632498919260729944657 970224374189445547458493)
        ·
          refine ⟨363834140321042080296935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 970224374189445547458493 363834140321042080296935)
          ·
            refine ⟨545751210481563120445403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 363834140321042080296935 545751210481563120445403)
            ·
              refine ⟨818626815722344680668105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 545751210481563120445403 818626815722344680668105)
              ·
                refine ⟨613970111791758510501079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 818626815722344680668105 613970111791758510501079)
                ·
                  refine ⟨920955167687637765751619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 613970111791758510501079 920955167687637765751619)
                  ·
                    refine ⟨1381432751531456648627429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 920955167687637765751619 1381432751531456648627429)
                    ·
                      refine ⟨259018640912148121617643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1381432751531456648627429 259018640912148121617643)
                      ·
                        rfl

theorem cell23_504437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 1, 2, 1, 1, 4].length) (baseStart_504437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_504437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_504437 prefixEnd_504437 := by exact prefixLift 504437
  have htrace : WordTrace (prefixWord ++ tailWord_504437) baseStart_504437 baseEnd_504437 := by
    simpa [prefixWord, tailWord_504437, baseEnd_504437] using wordTrace_append hprefix tailTrace_504437
  have hstable : (prefixWord ++ tailWord_504437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504437).length < 2 ^ (prefixWord ++ tailWord_504437).sum := by decide
  have hdescent : baseEnd_504437 < baseStart_504437 := by decide
  rcases family_descends (prefixWord ++ tailWord_504437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504476 : List Nat := [2, 2, 3, 2, 2, 1, 1, 1, 2, 3, 4]
def baseStart_504476 : Nat := 118140960795 + 504476 * 2 ^ 59
def prefixEnd_504476 : Nat := 4983230072969 + 3 ^ 40 * 504476 * 2
def baseEnd_504476 : Nat := 259038666657673469029963

theorem tailTrace_504476 : CollatzResearch.WordTrace tailWord_504476 prefixEnd_504476 259038666657673469029963 := by
  unfold tailWord_504476
  simp only [CollatzResearch.WordTrace]
  refine ⟨9199875660188542243274641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12266500880251389657699521 9199875660188542243274641)
  ·
    refine ⟨6899906745141406682455981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9199875660188542243274641 6899906745141406682455981)
    ·
      refine ⟨2587465029428027505920993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6899906745141406682455981 2587465029428027505920993)
      ·
        refine ⟨1940598772071020629440745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2587465029428027505920993 1940598772071020629440745)
        ·
          refine ⟨1455449079053265472080559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1940598772071020629440745 1455449079053265472080559)
          ·
            refine ⟨2183173618579898208120839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1455449079053265472080559 2183173618579898208120839)
            ·
              refine ⟨3274760427869847312181259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2183173618579898208120839 3274760427869847312181259)
              ·
                refine ⟨4912140641804770968271889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3274760427869847312181259 4912140641804770968271889)
                ·
                  refine ⟨3684105481353578226203917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4912140641804770968271889 3684105481353578226203917)
                  ·
                    refine ⟨1381539555507591834826469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3684105481353578226203917 1381539555507591834826469)
                    ·
                      refine ⟨259038666657673469029963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1381539555507591834826469 259038666657673469029963)
                      ·
                        rfl

theorem cell23_504476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_504476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_504476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_504476 prefixEnd_504476 := by exact prefixLift 504476
  have htrace : WordTrace (prefixWord ++ tailWord_504476) baseStart_504476 baseEnd_504476 := by
    simpa [prefixWord, tailWord_504476, baseEnd_504476] using wordTrace_append hprefix tailTrace_504476
  have hstable : (prefixWord ++ tailWord_504476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504476).length < 2 ^ (prefixWord ++ tailWord_504476).sum := by decide
  have hdescent : baseEnd_504476 < baseStart_504476 := by decide
  rcases family_descends (prefixWord ++ tailWord_504476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504489 : List Nat := [1, 2, 1, 1, 1, 1, 2, 5, 1, 4, 4]
def baseStart_504489 : Nat := 118140960795 + 504489 * 2 ^ 59
def prefixEnd_504489 : Nat := 4983230072969 + 3 ^ 40 * 504489 * 2
def baseEnd_504489 : Nat := 259045341906181918167403

theorem tailTrace_504489 : CollatzResearch.WordTrace tailWord_504489 prefixEnd_504489 259045341906181918167403 := by
  unfold tailWord_504489
  simp only [CollatzResearch.WordTrace]
  refine ⟨18400225469329987706772521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12266816979553325137848347 18400225469329987706772521)
  ·
    refine ⟨13800169101997490780079391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18400225469329987706772521 13800169101997490780079391)
    ·
      refine ⟨20700253652996236170119087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13800169101997490780079391 20700253652996236170119087)
      ·
        refine ⟨31050380479494354255178631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20700253652996236170119087 31050380479494354255178631)
        ·
          refine ⟨46575570719241531382767947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31050380479494354255178631 46575570719241531382767947)
          ·
            refine ⟨69863356078862297074151921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46575570719241531382767947 69863356078862297074151921)
            ·
              refine ⟨52397517059146722805613941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69863356078862297074151921 52397517059146722805613941)
              ·
                refine ⟨4912267224295005263026307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52397517059146722805613941 4912267224295005263026307)
                ·
                  refine ⟨7368400836442507894539461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4912267224295005263026307 7368400836442507894539461)
                  ·
                    refine ⟨1381575156832970230226149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7368400836442507894539461 1381575156832970230226149)
                    ·
                      refine ⟨259045341906181918167403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1381575156832970230226149 259045341906181918167403)
                      ·
                        rfl

theorem cell23_504489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 5, 1, 4, 4].length) (baseStart_504489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_504489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_504489 prefixEnd_504489 := by exact prefixLift 504489
  have htrace : WordTrace (prefixWord ++ tailWord_504489) baseStart_504489 baseEnd_504489 := by
    simpa [prefixWord, tailWord_504489, baseEnd_504489] using wordTrace_append hprefix tailTrace_504489
  have hstable : (prefixWord ++ tailWord_504489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504489).length < 2 ^ (prefixWord ++ tailWord_504489).sum := by decide
  have hdescent : baseEnd_504489 < baseStart_504489 := by decide
  rcases family_descends (prefixWord ++ tailWord_504489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504499 : List Nat := [1, 1, 1, 2, 3, 4, 1, 1, 9]
def baseStart_504499 : Nat := 118140960795 + 504499 * 2 ^ 59
def prefixEnd_504499 : Nat := 4983230072969 + 3 ^ 40 * 504499 * 2
def baseEnd_504499 : Nat := 28783386301414097671373

theorem tailTrace_504499 : CollatzResearch.WordTrace tailWord_504499 prefixEnd_504499 28783386301414097671373 := by
  unfold tailWord_504499
  simp only [CollatzResearch.WordTrace]
  refine ⟨18400590199293759414636551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12267060132862506276424367 18400590199293759414636551)
  ·
    refine ⟨27600885298940639121954827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18400590199293759414636551 27600885298940639121954827)
    ·
      refine ⟨41401327948410958682932241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27600885298940639121954827 41401327948410958682932241)
      ·
        refine ⟨31050995961308219012199181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41401327948410958682932241 31050995961308219012199181)
        ·
          refine ⟨11644123485490582129574693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31050995961308219012199181 11644123485490582129574693)
          ·
            refine ⟨2183273153529484149295255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11644123485490582129574693 2183273153529484149295255)
            ·
              refine ⟨3274909730294226223942883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2183273153529484149295255 3274909730294226223942883)
              ·
                refine ⟨4912364595441339335914325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3274909730294226223942883 4912364595441339335914325)
                ·
                  refine ⟨28783386301414097671373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 4912364595441339335914325 28783386301414097671373)
                  ·
                    rfl

theorem cell23_504499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 1, 9].length) (baseStart_504499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_504499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_504499 prefixEnd_504499 := by exact prefixLift 504499
  have htrace : WordTrace (prefixWord ++ tailWord_504499) baseStart_504499 baseEnd_504499 := by
    simpa [prefixWord, tailWord_504499, baseEnd_504499] using wordTrace_append hprefix tailTrace_504499
  have hstable : (prefixWord ++ tailWord_504499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504499).length < 2 ^ (prefixWord ++ tailWord_504499).sum := by decide
  have hdescent : baseEnd_504499 < baseStart_504499 := by decide
  rcases family_descends (prefixWord ++ tailWord_504499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504510 : List Nat := [4, 2, 1, 1, 2, 1, 2, 2, 4, 2, 2]
def baseStart_504510 : Nat := 118140960795 + 504510 * 2 ^ 59
def prefixEnd_504510 : Nat := 4983230072969 + 3 ^ 40 * 504510 * 2
def baseEnd_504510 : Nat := 259056124999926336004807

theorem tailTrace_504510 : CollatzResearch.WordTrace tailWord_504510 prefixEnd_504510 259056124999926336004807 := by
  unfold tailWord_504510
  simp only [CollatzResearch.WordTrace]
  refine ⟨2300123925281738536660873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12267327601502605528857989 2300123925281738536660873)
  ·
    refine ⟨1725092943961303902495655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2300123925281738536660873 1725092943961303902495655)
    ·
      refine ⟨2587639415941955853743483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1725092943961303902495655 2587639415941955853743483)
      ·
        refine ⟨3881459123912933780615225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2587639415941955853743483 3881459123912933780615225)
        ·
          refine ⟨2911094342934700335461419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3881459123912933780615225 2911094342934700335461419)
          ·
            refine ⟨4366641514402050503192129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2911094342934700335461419 4366641514402050503192129)
            ·
              refine ⟨3274981135801537877394097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4366641514402050503192129 3274981135801537877394097)
              ·
                refine ⟨2456235851851153408045573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3274981135801537877394097 2456235851851153408045573)
                ·
                  refine ⟨460544222222091264008545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2456235851851153408045573 460544222222091264008545)
                  ·
                    refine ⟨345408166666568448006409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 460544222222091264008545 345408166666568448006409)
                    ·
                      refine ⟨259056124999926336004807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 345408166666568448006409 259056124999926336004807)
                      ·
                        rfl

theorem cell23_504510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 2, 4, 2, 2].length) (baseStart_504510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_504510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_504510 prefixEnd_504510 := by exact prefixLift 504510
  have htrace : WordTrace (prefixWord ++ tailWord_504510) baseStart_504510 baseEnd_504510 := by
    simpa [prefixWord, tailWord_504510, baseEnd_504510] using wordTrace_append hprefix tailTrace_504510
  have hstable : (prefixWord ++ tailWord_504510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504510).length < 2 ^ (prefixWord ++ tailWord_504510).sum := by decide
  have hdescent : baseEnd_504510 < baseStart_504510 := by decide
  rcases family_descends (prefixWord ++ tailWord_504510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504583 : List Nat := [1, 1, 4, 4, 1, 1, 1, 1, 4, 1, 4]
def baseStart_504583 : Nat := 118140960795 + 504583 * 2 ^ 59
def prefixEnd_504583 : Nat := 4983230072969 + 3 ^ 40 * 504583 * 2
def baseEnd_504583 : Nat := 259093609087704550391971

theorem tailTrace_504583 : CollatzResearch.WordTrace tailWord_504583 prefixEnd_504583 259093609087704550391971 := by
  unfold tailWord_504583
  simp only [CollatzResearch.WordTrace]
  refine ⟨18403653930989441760694403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12269102620659627840462935 18403653930989441760694403)
  ·
    refine ⟨27605480896484162641041605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18403653930989441760694403 27605480896484162641041605)
    ·
      refine ⟨5176027668090780495195301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27605480896484162641041605 5176027668090780495195301)
      ·
        refine ⟨970505187767021342849119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5176027668090780495195301 970505187767021342849119)
        ·
          refine ⟨1455757781650532014273679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 970505187767021342849119 1455757781650532014273679)
          ·
            refine ⟨2183636672475798021410519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1455757781650532014273679 2183636672475798021410519)
            ·
              refine ⟨3275455008713697032115779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2183636672475798021410519 3275455008713697032115779)
              ·
                refine ⟨4913182513070545548173669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3275455008713697032115779 4913182513070545548173669)
                ·
                  refine ⟨921221721200727290282563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4913182513070545548173669 921221721200727290282563)
                  ·
                    refine ⟨1381832581801090935423845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 921221721200727290282563 1381832581801090935423845)
                    ·
                      refine ⟨259093609087704550391971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1381832581801090935423845 259093609087704550391971)
                      ·
                        rfl

theorem cell23_504583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_504583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_504583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_504583 prefixEnd_504583 := by exact prefixLift 504583
  have htrace : WordTrace (prefixWord ++ tailWord_504583) baseStart_504583 baseEnd_504583 := by
    simpa [prefixWord, tailWord_504583, baseEnd_504583] using wordTrace_append hprefix tailTrace_504583
  have hstable : (prefixWord ++ tailWord_504583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504583).length < 2 ^ (prefixWord ++ tailWord_504583).sum := by decide
  have hdescent : baseEnd_504583 < baseStart_504583 := by decide
  rcases family_descends (prefixWord ++ tailWord_504583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504593 : List Nat := [1, 2, 2, 1, 1, 3, 5, 1, 3, 4]
def baseStart_504593 : Nat := 118140960795 + 504593 * 2 ^ 59
def prefixEnd_504593 : Nat := 4983230072969 + 3 ^ 40 * 504593 * 2
def baseEnd_504593 : Nat := 86366247964749837088975

theorem tailTrace_504593 : CollatzResearch.WordTrace tailWord_504593 prefixEnd_504593 86366247964749837088975 := by
  unfold tailWord_504593
  simp only [CollatzResearch.WordTrace]
  refine ⟨18404018660953213468558433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12269345773968808979038955 18404018660953213468558433)
  ·
    refine ⟨13803013995714910101418825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18404018660953213468558433 13803013995714910101418825)
    ·
      refine ⟨10352260496786182576064119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13803013995714910101418825 10352260496786182576064119)
      ·
        refine ⟨15528390745179273864096179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10352260496786182576064119 15528390745179273864096179)
        ·
          refine ⟨23292586117768910796144269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15528390745179273864096179 23292586117768910796144269)
          ·
            refine ⟨8734719794163341548554101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23292586117768910796144269 8734719794163341548554101)
            ·
              refine ⟨818879980702813270176947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8734719794163341548554101 818879980702813270176947)
              ·
                refine ⟨1228319971054219905265421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 818879980702813270176947 1228319971054219905265421)
                ·
                  refine ⟨460619989145332464474533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1228319971054219905265421 460619989145332464474533)
                  ·
                    refine ⟨86366247964749837088975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 460619989145332464474533 86366247964749837088975)
                    ·
                      rfl

theorem cell23_504593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 5, 1, 3, 4].length) (baseStart_504593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_504593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_504593 prefixEnd_504593 := by exact prefixLift 504593
  have htrace : WordTrace (prefixWord ++ tailWord_504593) baseStart_504593 baseEnd_504593 := by
    simpa [prefixWord, tailWord_504593, baseEnd_504593] using wordTrace_append hprefix tailTrace_504593
  have hstable : (prefixWord ++ tailWord_504593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504593).length < 2 ^ (prefixWord ++ tailWord_504593).sum := by decide
  have hdescent : baseEnd_504593 < baseStart_504593 := by decide
  rcases family_descends (prefixWord ++ tailWord_504593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504673 : List Nat := [1, 2, 3, 1, 1, 1, 2, 1, 1, 8, 2]
def baseStart_504673 : Nat := 118140960795 + 504673 * 2 ^ 59
def prefixEnd_504673 : Nat := 4983230072969 + 3 ^ 40 * 504673 * 2
def baseEnd_504673 : Nat := 259139822346609198266557

theorem tailTrace_504673 : CollatzResearch.WordTrace tailWord_504673 prefixEnd_504673 259139822346609198266557 := by
  unfold tailWord_504673
  simp only [CollatzResearch.WordTrace]
  refine ⟨18406936500663387131470673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12271291000442258087647115 18406936500663387131470673)
  ·
    refine ⟨13805202375497540348603005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18406936500663387131470673 13805202375497540348603005)
    ·
      refine ⟨5176950890811577630726127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13805202375497540348603005 5176950890811577630726127)
      ·
        refine ⟨7765426336217366446089191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5176950890811577630726127 7765426336217366446089191)
        ·
          refine ⟨11648139504326049669133787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7765426336217366446089191 11648139504326049669133787)
          ·
            refine ⟨17472209256489074503700681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11648139504326049669133787 17472209256489074503700681)
            ·
              refine ⟨13104156942366805877775511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17472209256489074503700681 13104156942366805877775511)
              ·
                refine ⟨19656235413550208816663267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13104156942366805877775511 19656235413550208816663267)
                ·
                  refine ⟨29484353120325313224994901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19656235413550208816663267 29484353120325313224994901)
                  ·
                    refine ⟨345519763128812264355409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 29484353120325313224994901 345519763128812264355409)
                    ·
                      refine ⟨259139822346609198266557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 345519763128812264355409 259139822346609198266557)
                      ·
                        rfl

theorem cell23_504673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 8, 2].length) (baseStart_504673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_504673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_504673 prefixEnd_504673 := by exact prefixLift 504673
  have htrace : WordTrace (prefixWord ++ tailWord_504673) baseStart_504673 baseEnd_504673 := by
    simpa [prefixWord, tailWord_504673, baseEnd_504673] using wordTrace_append hprefix tailTrace_504673
  have hstable : (prefixWord ++ tailWord_504673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504673).length < 2 ^ (prefixWord ++ tailWord_504673).sum := by decide
  have hdescent : baseEnd_504673 < baseStart_504673 := by decide
  rcases family_descends (prefixWord ++ tailWord_504673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504707 : List Nat := [1, 1, 1, 3, 4, 1, 4, 1, 3, 2, 2]
def baseStart_504707 : Nat := 118140960795 + 504707 * 2 ^ 59
def prefixEnd_504707 : Nat := 4983230072969 + 3 ^ 40 * 504707 * 2
def baseEnd_504707 : Nat := 259157280688862065241401

theorem tailTrace_504707 : CollatzResearch.WordTrace tailWord_504707 prefixEnd_504707 259157280688862065241401 := by
  unfold tailWord_504707
  simp only [CollatzResearch.WordTrace]
  refine ⟨18408176582540210938208375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12272117721693473958805583 18408176582540210938208375)
  ·
    refine ⟨27612264873810316407312563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18408176582540210938208375 27612264873810316407312563)
    ·
      refine ⟨41418397310715474610968845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27612264873810316407312563 41418397310715474610968845)
      ·
        refine ⟨15531898991518302979113317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41418397310715474610968845 15531898991518302979113317)
        ·
          refine ⟨2912231060909681808583747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15531898991518302979113317 2912231060909681808583747)
          ·
            refine ⟨4368346591364522712875621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2912231060909681808583747 4368346591364522712875621)
            ·
              refine ⟨819064985880848008664179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4368346591364522712875621 819064985880848008664179)
              ·
                refine ⟨1228597478821272012996269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 819064985880848008664179 1228597478821272012996269)
                ·
                  refine ⟨460724054557977004873601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1228597478821272012996269 460724054557977004873601)
                  ·
                    refine ⟨345543040918482753655201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 460724054557977004873601 345543040918482753655201)
                    ·
                      refine ⟨259157280688862065241401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 345543040918482753655201 259157280688862065241401)
                      ·
                        rfl

theorem cell23_504707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 4, 1, 3, 2, 2].length) (baseStart_504707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_504707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_504707 prefixEnd_504707 := by exact prefixLift 504707
  have htrace : WordTrace (prefixWord ++ tailWord_504707) baseStart_504707 baseEnd_504707 := by
    simpa [prefixWord, tailWord_504707, baseEnd_504707] using wordTrace_append hprefix tailTrace_504707
  have hstable : (prefixWord ++ tailWord_504707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504707).length < 2 ^ (prefixWord ++ tailWord_504707).sum := by decide
  have hdescent : baseEnd_504707 < baseStart_504707 := by decide
  rcases family_descends (prefixWord ++ tailWord_504707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504723 : List Nat := [1, 1, 1, 2, 1, 2, 1, 7, 1, 3, 3]
def baseStart_504723 : Nat := 118140960795 + 504723 * 2 ^ 59
def prefixEnd_504723 : Nat := 4983230072969 + 3 ^ 40 * 504723 * 2
def baseEnd_504723 : Nat := 259165496379334002641327

theorem tailTrace_504723 : CollatzResearch.WordTrace tailWord_504723 prefixEnd_504723 259165496379334002641327 := by
  unfold tailWord_504723
  simp only [CollatzResearch.WordTrace]
  refine ⟨18408760150482245670790823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12272506766988163780527215 18408760150482245670790823)
  ·
    refine ⟨27613140225723368506186235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18408760150482245670790823 27613140225723368506186235)
    ·
      refine ⟨41419710338585052759279353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27613140225723368506186235 41419710338585052759279353)
      ·
        refine ⟨31064782753938789569459515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41419710338585052759279353 31064782753938789569459515)
        ·
          refine ⟨46597174130908184354189273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31064782753938789569459515 46597174130908184354189273)
          ·
            refine ⟨34947880598181138265641955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46597174130908184354189273 34947880598181138265641955)
            ·
              refine ⟨52421820897271707398462933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34947880598181138265641955 52421820897271707398462933)
              ·
                refine ⟨1228636427279805642151475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 52421820897271707398462933 1228636427279805642151475)
                ·
                  refine ⟨1842954640919708463227213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1228636427279805642151475 1842954640919708463227213)
                  ·
                    refine ⟨691107990344890673710205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1842954640919708463227213 691107990344890673710205)
                    ·
                      refine ⟨259165496379334002641327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 691107990344890673710205 259165496379334002641327)
                      ·
                        rfl

theorem cell23_504723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 7, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 7, 1, 3, 3].length) (baseStart_504723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_504723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_504723 prefixEnd_504723 := by exact prefixLift 504723
  have htrace : WordTrace (prefixWord ++ tailWord_504723) baseStart_504723 baseEnd_504723 := by
    simpa [prefixWord, tailWord_504723, baseEnd_504723] using wordTrace_append hprefix tailTrace_504723
  have hstable : (prefixWord ++ tailWord_504723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504723).length < 2 ^ (prefixWord ++ tailWord_504723).sum := by decide
  have hdescent : baseEnd_504723 < baseStart_504723 := by decide
  rcases family_descends (prefixWord ++ tailWord_504723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504740 : List Nat := [2, 3, 1, 2, 1, 2, 1, 1, 6, 1, 3]
def baseStart_504740 : Nat := 118140960795 + 504740 * 2 ^ 59
def prefixEnd_504740 : Nat := 4983230072969 + 3 ^ 40 * 504740 * 2
def baseEnd_504740 : Nat := 259174225550460436128749

theorem tailTrace_504740 : CollatzResearch.WordTrace tailWord_504740 prefixEnd_504740 259174225550460436128749 := by
  unfold tailWord_504740
  simp only [CollatzResearch.WordTrace]
  refine ⟨9204690095710328787079837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12272920127613771716106449 9204690095710328787079837)
  ·
    refine ⟨3451758785891373295154939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9204690095710328787079837 3451758785891373295154939)
    ·
      refine ⟨5177638178837059942732409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3451758785891373295154939 5177638178837059942732409)
      ·
        refine ⟨3883228634127794957049307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5177638178837059942732409 3883228634127794957049307)
        ·
          refine ⟨5824842951191692435573961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3883228634127794957049307 5824842951191692435573961)
          ·
            refine ⟨4368632213393769326680471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5824842951191692435573961 4368632213393769326680471)
            ·
              refine ⟨6552948320090653990020707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4368632213393769326680471 6552948320090653990020707)
              ·
                refine ⟨9829422480135980985031061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6552948320090653990020707 9829422480135980985031061)
                ·
                  refine ⟨460754178756374108673331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9829422480135980985031061 460754178756374108673331)
                  ·
                    refine ⟨691131268134561163009997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 460754178756374108673331 691131268134561163009997)
                    ·
                      refine ⟨259174225550460436128749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 691131268134561163009997 259174225550460436128749)
                      ·
                        rfl

theorem cell23_504740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 1, 6, 1, 3].length) (baseStart_504740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_504740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_504740 prefixEnd_504740 := by exact prefixLift 504740
  have htrace : WordTrace (prefixWord ++ tailWord_504740) baseStart_504740 baseEnd_504740 := by
    simpa [prefixWord, tailWord_504740, baseEnd_504740] using wordTrace_append hprefix tailTrace_504740
  have hstable : (prefixWord ++ tailWord_504740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504740).length < 2 ^ (prefixWord ++ tailWord_504740).sum := by decide
  have hdescent : baseEnd_504740 < baseStart_504740 := by decide
  rcases family_descends (prefixWord ++ tailWord_504740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504757 : List Nat := [1, 3, 3, 2, 1, 1, 2, 4, 2, 1, 3]
def baseStart_504757 : Nat := 118140960795 + 504757 * 2 ^ 59
def prefixEnd_504757 : Nat := 4983230072969 + 3 ^ 40 * 504757 * 2
def baseEnd_504757 : Nat := 259182954721586869616171

theorem tailTrace_504757 : CollatzResearch.WordTrace tailWord_504757 prefixEnd_504757 259182954721586869616171 := by
  unfold tailWord_504757
  simp only [CollatzResearch.WordTrace]
  refine ⟨18410000232359069477528525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12273333488239379651685683 18410000232359069477528525)
  ·
    refine ⟨6903750087134651054073197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18410000232359069477528525 6903750087134651054073197)
    ·
      refine ⟨2588906282675494145277449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6903750087134651054073197 2588906282675494145277449)
      ·
        refine ⟨1941679712006620608958087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2588906282675494145277449 1941679712006620608958087)
        ·
          refine ⟨2912519568009930913437131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1941679712006620608958087 2912519568009930913437131)
          ·
            refine ⟨4368779352014896370155697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2912519568009930913437131 4368779352014896370155697)
            ·
              refine ⟨3276584514011172277616773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4368779352014896370155697 3276584514011172277616773)
              ·
                refine ⟨614359596377094802053145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3276584514011172277616773 614359596377094802053145)
                ·
                  refine ⟨460769697282821101539859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 614359596377094802053145 460769697282821101539859)
                  ·
                    refine ⟨691154545924231652309789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 460769697282821101539859 691154545924231652309789)
                    ·
                      refine ⟨259182954721586869616171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 691154545924231652309789 259182954721586869616171)
                      ·
                        rfl

theorem cell23_504757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 4, 2, 1, 3].length) (baseStart_504757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_504757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_504757 prefixEnd_504757 := by exact prefixLift 504757
  have htrace : WordTrace (prefixWord ++ tailWord_504757) baseStart_504757 baseEnd_504757 := by
    simpa [prefixWord, tailWord_504757, baseEnd_504757] using wordTrace_append hprefix tailTrace_504757
  have hstable : (prefixWord ++ tailWord_504757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504757).length < 2 ^ (prefixWord ++ tailWord_504757).sum := by decide
  have hdescent : baseEnd_504757 < baseStart_504757 := by decide
  rcases family_descends (prefixWord ++ tailWord_504757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504783 : List Nat := [1, 1, 2, 1, 1, 6, 1, 2, 2, 1, 5]
def baseStart_504783 : Nat := 118140960795 + 504783 * 2 ^ 59
def prefixEnd_504783 : Nat := 4983230072969 + 3 ^ 40 * 504783 * 2
def baseEnd_504783 : Nat := 259196305218603767891051

theorem tailTrace_504783 : CollatzResearch.WordTrace tailWord_504783 prefixEnd_504783 259196305218603767891051 := by
  unfold tailWord_504783
  simp only [CollatzResearch.WordTrace]
  refine ⟨18410948530264875917975003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12273965686843250611983335 18410948530264875917975003)
  ·
    refine ⟨27616422795397313876962505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18410948530264875917975003 27616422795397313876962505)
    ·
      refine ⟨20712317096547985407721879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27616422795397313876962505 20712317096547985407721879)
      ·
        refine ⟨31068475644821978111582819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20712317096547985407721879 31068475644821978111582819)
        ·
          refine ⟨46602713467232967167374229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31068475644821978111582819 46602713467232967167374229)
          ·
            refine ⟨2184502193776545335970667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 46602713467232967167374229 2184502193776545335970667)
            ·
              refine ⟨3276753290664818003956001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2184502193776545335970667 3276753290664818003956001)
              ·
                refine ⟨2457564967998613502967001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3276753290664818003956001 2457564967998613502967001)
                ·
                  refine ⟨1843173725998960127225251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2457564967998613502967001 1843173725998960127225251)
                  ·
                    refine ⟨2764760588998440190837877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1843173725998960127225251 2764760588998440190837877)
                    ·
                      refine ⟨259196305218603767891051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2764760588998440190837877 259196305218603767891051)
                      ·
                        rfl

theorem cell23_504783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 2, 2, 1, 5].length) (baseStart_504783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_504783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_504783 prefixEnd_504783 := by exact prefixLift 504783
  have htrace : WordTrace (prefixWord ++ tailWord_504783) baseStart_504783 baseEnd_504783 := by
    simpa [prefixWord, tailWord_504783, baseEnd_504783] using wordTrace_append hprefix tailTrace_504783
  have hstable : (prefixWord ++ tailWord_504783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504783).length < 2 ^ (prefixWord ++ tailWord_504783).sum := by decide
  have hdescent : baseEnd_504783 < baseStart_504783 := by decide
  rcases family_descends (prefixWord ++ tailWord_504783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504797 : List Nat := [1, 4, 3, 1, 2, 1, 1, 1, 3, 4, 2]
def baseStart_504797 : Nat := 118140960795 + 504797 * 2 ^ 59
def prefixEnd_504797 : Nat := 4983230072969 + 3 ^ 40 * 504797 * 2
def baseEnd_504797 : Nat := 259203493947766713115987

theorem tailTrace_504797 : CollatzResearch.WordTrace tailWord_504797 prefixEnd_504797 259203493947766713115987 := by
  unfold tailWord_504797
  simp only [CollatzResearch.WordTrace]
  refine ⟨18411459152214156308984645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12274306101476104205989763 18411459152214156308984645)
  ·
    refine ⟨3452148591040154307934621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18411459152214156308984645 3452148591040154307934621)
    ·
      refine ⟨1294555721640057865475483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3452148591040154307934621 1294555721640057865475483)
      ·
        refine ⟨1941833582460086798213225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1294555721640057865475483 1941833582460086798213225)
        ·
          refine ⟨1456375186845065098659919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1941833582460086798213225 1456375186845065098659919)
          ·
            refine ⟨2184562780267597647989879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1456375186845065098659919 2184562780267597647989879)
            ·
              refine ⟨3276844170401396471984819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2184562780267597647989879 3276844170401396471984819)
              ·
                refine ⟨4915266255602094707977229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3276844170401396471984819 4915266255602094707977229)
                ·
                  refine ⟨1843224845850785515491461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4915266255602094707977229 1843224845850785515491461)
                  ·
                    refine ⟨345604658597022284154649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1843224845850785515491461 345604658597022284154649)
                    ·
                      refine ⟨259203493947766713115987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 345604658597022284154649 259203493947766713115987)
                      ·
                        rfl

theorem cell23_504797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 1, 3, 4, 2].length) (baseStart_504797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_504797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_504797 prefixEnd_504797 := by exact prefixLift 504797
  have htrace : WordTrace (prefixWord ++ tailWord_504797) baseStart_504797 baseEnd_504797 := by
    simpa [prefixWord, tailWord_504797, baseEnd_504797] using wordTrace_append hprefix tailTrace_504797
  have hstable : (prefixWord ++ tailWord_504797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504797).length < 2 ^ (prefixWord ++ tailWord_504797).sum := by decide
  have hdescent : baseEnd_504797 < baseStart_504797 := by decide
  rcases family_descends (prefixWord ++ tailWord_504797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504883 : List Nat := [1, 1, 1, 2, 4, 1, 1, 1, 4, 1, 6]
def baseStart_504883 : Nat := 118140960795 + 504883 * 2 ^ 59
def prefixEnd_504883 : Nat := 4983230072969 + 3 ^ 40 * 504883 * 2
def baseEnd_504883 : Nat := 259247653284053376640591

theorem tailTrace_504883 : CollatzResearch.WordTrace tailWord_504883 prefixEnd_504883 259247653284053376640591 := by
  unfold tailWord_504883
  simp only [CollatzResearch.WordTrace]
  refine ⟨18414595829902592996615303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12276397219935061997743535 18414595829902592996615303)
  ·
    refine ⟨27621893744853889494922955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18414595829902592996615303 27621893744853889494922955)
    ·
      refine ⟨41432840617280834242384433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27621893744853889494922955 41432840617280834242384433)
      ·
        refine ⟨31074630462960625681788325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41432840617280834242384433 31074630462960625681788325)
        ·
          refine ⟨5826493211805117315335311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31074630462960625681788325 5826493211805117315335311)
          ·
            refine ⟨8739739817707675973002967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5826493211805117315335311 8739739817707675973002967)
            ·
              refine ⟨13109609726561513959504451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8739739817707675973002967 13109609726561513959504451)
              ·
                refine ⟨19664414589842270939256677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13109609726561513959504451 19664414589842270939256677)
                ·
                  refine ⟨3687077735595425801110627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19664414589842270939256677 3687077735595425801110627)
                  ·
                    refine ⟨5530616603393138701665941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3687077735595425801110627 5530616603393138701665941)
                    ·
                      refine ⟨259247653284053376640591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5530616603393138701665941 259247653284053376640591)
                      ·
                        rfl

theorem cell23_504883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 4, 1, 6].length) (baseStart_504883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_504883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_504883 prefixEnd_504883 := by exact prefixLift 504883
  have htrace : WordTrace (prefixWord ++ tailWord_504883) baseStart_504883 baseEnd_504883 := by
    simpa [prefixWord, tailWord_504883, baseEnd_504883] using wordTrace_append hprefix tailTrace_504883
  have hstable : (prefixWord ++ tailWord_504883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504883).length < 2 ^ (prefixWord ++ tailWord_504883).sum := by decide
  have hdescent : baseEnd_504883 < baseStart_504883 := by decide
  rcases family_descends (prefixWord ++ tailWord_504883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504890 : List Nat := [3, 1, 1, 1, 3, 1, 3, 2, 1, 4, 3]
def baseStart_504890 : Nat := 118140960795 + 504890 * 2 ^ 59
def prefixEnd_504890 : Nat := 4983230072969 + 3 ^ 40 * 504890 * 2
def baseEnd_504890 : Nat := 259251247648634849253059

theorem tailTrace_504890 : CollatzResearch.WordTrace tailWord_504890 prefixEnd_504890 259251247648634849253059 := by
  unfold tailWord_504890
  simp only [CollatzResearch.WordTrace]
  refine ⟨4603712785219308298030031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12276567427251488794746749 4603712785219308298030031)
  ·
    refine ⟨6905569177828962447045047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4603712785219308298030031 6905569177828962447045047)
    ·
      refine ⟨10358353766743443670567571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6905569177828962447045047 10358353766743443670567571)
      ·
        refine ⟨15537530650115165505851357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10358353766743443670567571 15537530650115165505851357)
        ·
          refine ⟨5826573993793187064694259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15537530650115165505851357 5826573993793187064694259)
          ·
            refine ⟨8739860990689780597041389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5826573993793187064694259 8739860990689780597041389)
            ·
              refine ⟨3277447871508667723890521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8739860990689780597041389 3277447871508667723890521)
              ·
                refine ⟨2458085903631500792917891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3277447871508667723890521 2458085903631500792917891)
                ·
                  refine ⟨3687128855447251189376837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2458085903631500792917891 3687128855447251189376837)
                  ·
                    refine ⟨691336660396359598008157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3687128855447251189376837 691336660396359598008157)
                    ·
                      refine ⟨259251247648634849253059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 691336660396359598008157 259251247648634849253059)
                      ·
                        rfl

theorem cell23_504890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 2, 1, 4, 3].length) (baseStart_504890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_504890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_504890 prefixEnd_504890 := by exact prefixLift 504890
  have htrace : WordTrace (prefixWord ++ tailWord_504890) baseStart_504890 baseEnd_504890 := by
    simpa [prefixWord, tailWord_504890, baseEnd_504890] using wordTrace_append hprefix tailTrace_504890
  have hstable : (prefixWord ++ tailWord_504890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504890).length < 2 ^ (prefixWord ++ tailWord_504890).sum := by decide
  have hdescent : baseEnd_504890 < baseStart_504890 := by decide
  rcases family_descends (prefixWord ++ tailWord_504890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504940 : List Nat := [2, 2, 1, 1, 3, 2, 2, 2, 3, 5]
def baseStart_504940 : Nat := 118140960795 + 504940 * 2 ^ 59
def prefixEnd_504940 : Nat := 4983230072969 + 3 ^ 40 * 504940 * 2
def baseEnd_504940 : Nat := 86425640560453217875943

theorem tailTrace_504940 : CollatzResearch.WordTrace tailWord_504940 prefixEnd_504940 86425640560453217875943 := by
  unfold tailWord_504940
  simp only [CollatzResearch.WordTrace]
  refine ⟨9208337395348045865720137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12277783193797394487626849 9208337395348045865720137)
  ·
    refine ⟨6906253046511034399290103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9208337395348045865720137 6906253046511034399290103)
    ·
      refine ⟨10359379569766551598935155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6906253046511034399290103 10359379569766551598935155)
      ·
        refine ⟨15539069354649827398402733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10359379569766551598935155 15539069354649827398402733)
        ·
          refine ⟨5827151007993685274401025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15539069354649827398402733 5827151007993685274401025)
          ·
            refine ⟨4370363255995263955800769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5827151007993685274401025 4370363255995263955800769)
            ·
              refine ⟨3277772441996447966850577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4370363255995263955800769 3277772441996447966850577)
              ·
                refine ⟨2458329331497335975137933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3277772441996447966850577 2458329331497335975137933)
                ·
                  refine ⟨921873499311500990676725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2458329331497335975137933 921873499311500990676725)
                  ·
                    refine ⟨86425640560453217875943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 921873499311500990676725 86425640560453217875943)
                    ·
                      rfl

theorem cell23_504940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 5].length) (baseStart_504940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_504940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_504940 prefixEnd_504940 := by exact prefixLift 504940
  have htrace : WordTrace (prefixWord ++ tailWord_504940) baseStart_504940 baseEnd_504940 := by
    simpa [prefixWord, tailWord_504940, baseEnd_504940] using wordTrace_append hprefix tailTrace_504940
  have hstable : (prefixWord ++ tailWord_504940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504940).length < 2 ^ (prefixWord ++ tailWord_504940).sum := by decide
  have hdescent : baseEnd_504940 < baseStart_504940 := by decide
  rcases family_descends (prefixWord ++ tailWord_504940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504964 : List Nat := [2, 3, 2, 1, 2, 2, 1, 3, 2, 3, 2]
def baseStart_504964 : Nat := 118140960795 + 504964 * 2 ^ 59
def prefixEnd_504964 : Nat := 4983230072969 + 3 ^ 40 * 504964 * 2
def baseEnd_504964 : Nat := 259289245217067559727719

theorem tailTrace_504964 : CollatzResearch.WordTrace tailWord_504964 prefixEnd_504964 259289245217067559727719 := by
  unfold tailWord_504964
  simp only [CollatzResearch.WordTrace]
  refine ⟨9208775071304571915156973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12278366761739429220209297 9208775071304571915156973)
  ·
    refine ⟨3453290651739214468183865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9208775071304571915156973 3453290651739214468183865)
    ·
      refine ⟨2589967988804410851137899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3453290651739214468183865 2589967988804410851137899)
      ·
        refine ⟨3884951983206616276706849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2589967988804410851137899 3884951983206616276706849)
        ·
          refine ⟨2913713987404962207530137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3884951983206616276706849 2913713987404962207530137)
          ·
            refine ⟨2185285490553721655647603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2913713987404962207530137 2185285490553721655647603)
            ·
              refine ⟨3277928235830582483471405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2185285490553721655647603 3277928235830582483471405)
              ·
                refine ⟨1229223088436468431301777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3277928235830582483471405 1229223088436468431301777)
                ·
                  refine ⟨921917316327351323476333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1229223088436468431301777 921917316327351323476333)
                  ·
                    refine ⟨345718993622756746303625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 921917316327351323476333 345718993622756746303625)
                    ·
                      refine ⟨259289245217067559727719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 345718993622756746303625 259289245217067559727719)
                      ·
                        rfl

theorem cell23_504964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 3, 2, 3, 2].length) (baseStart_504964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_504964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_504964 prefixEnd_504964 := by exact prefixLift 504964
  have htrace : WordTrace (prefixWord ++ tailWord_504964) baseStart_504964 baseEnd_504964 := by
    simpa [prefixWord, tailWord_504964, baseEnd_504964] using wordTrace_append hprefix tailTrace_504964
  have hstable : (prefixWord ++ tailWord_504964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504964).length < 2 ^ (prefixWord ++ tailWord_504964).sum := by decide
  have hdescent : baseEnd_504964 < baseStart_504964 := by decide
  rcases family_descends (prefixWord ++ tailWord_504964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504988 : List Nat := [2, 2, 3, 2, 1, 2, 4, 2, 1, 1, 3]
def baseStart_504988 : Nat := 118140960795 + 504988 * 2 ^ 59
def prefixEnd_504988 : Nat := 4983230072969 + 3 ^ 40 * 504988 * 2
def baseEnd_504988 : Nat := 259301568752775465827609

theorem tailTrace_504988 : CollatzResearch.WordTrace tailWord_504988 prefixEnd_504988 259301568752775465827609 := by
  unfold tailWord_504988
  simp only [CollatzResearch.WordTrace]
  refine ⟨9209212747261097964593809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12278950329681463952791745 9209212747261097964593809)
  ·
    refine ⟨6906909560445823473445357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9209212747261097964593809 6906909560445823473445357)
    ·
      refine ⟨2590091085167183802542009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6906909560445823473445357 2590091085167183802542009)
      ·
        refine ⟨1942568313875387851906507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2590091085167183802542009 1942568313875387851906507)
        ·
          refine ⟨2913852470813081777859761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1942568313875387851906507 2913852470813081777859761)
          ·
            refine ⟨2185389353109811333394821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2913852470813081777859761 2185389353109811333394821)
            ·
              refine ⟨409760503708089625011529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2185389353109811333394821 409760503708089625011529)
              ·
                refine ⟨307320377781067218758647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 409760503708089625011529 307320377781067218758647)
                ·
                  refine ⟨460980566671600828137971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 307320377781067218758647 460980566671600828137971)
                  ·
                    refine ⟨691470850007401242206957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 460980566671600828137971 691470850007401242206957)
                    ·
                      refine ⟨259301568752775465827609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 691470850007401242206957 259301568752775465827609)
                      ·
                        rfl

theorem cell23_504988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 4, 2, 1, 1, 3].length) (baseStart_504988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_504988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_504988 prefixEnd_504988 := by exact prefixLift 504988
  have htrace : WordTrace (prefixWord ++ tailWord_504988) baseStart_504988 baseEnd_504988 := by
    simpa [prefixWord, tailWord_504988, baseEnd_504988] using wordTrace_append hprefix tailTrace_504988
  have hstable : (prefixWord ++ tailWord_504988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504988).length < 2 ^ (prefixWord ++ tailWord_504988).sum := by decide
  have hdescent : baseEnd_504988 < baseStart_504988 := by decide
  rcases family_descends (prefixWord ++ tailWord_504988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_504997 : List Nat := [1, 3, 1, 2, 1, 4, 1, 2, 3, 2, 3]
def baseStart_504997 : Nat := 118140960795 + 504997 * 2 ^ 59
def prefixEnd_504997 : Nat := 4983230072969 + 3 ^ 40 * 504997 * 2
def baseEnd_504997 : Nat := 259306190078665930615067

theorem tailTrace_504997 : CollatzResearch.WordTrace tailWord_504997 prefixEnd_504997 259306190078665930615067 := by
  unfold tailWord_504997
  simp only [CollatzResearch.WordTrace]
  refine ⟨18418753751489590466265245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12279169167659726977510163 18418753751489590466265245)
  ·
    refine ⟨6907032656808596424849467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18418753751489590466265245 6907032656808596424849467)
    ·
      refine ⟨10360548985212894637274201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6907032656808596424849467 10360548985212894637274201)
      ·
        refine ⟨7770411738909670977955651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10360548985212894637274201 7770411738909670977955651)
        ·
          refine ⟨11655617608364506466933477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7770411738909670977955651 11655617608364506466933477)
          ·
            refine ⟨2185428301568344962550027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11655617608364506466933477 2185428301568344962550027)
            ·
              refine ⟨3278142452352517443825041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2185428301568344962550027 3278142452352517443825041)
              ·
                refine ⟨2458606839264388082868781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3278142452352517443825041 2458606839264388082868781)
                ·
                  refine ⟨921977564724145531075793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2458606839264388082868781 921977564724145531075793)
                  ·
                    refine ⟨691483173543109148306845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 921977564724145531075793 691483173543109148306845)
                    ·
                      refine ⟨259306190078665930615067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 691483173543109148306845 259306190078665930615067)
                      ·
                        rfl

theorem cell23_504997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 2, 3, 2, 3].length) (baseStart_504997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_504997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_504997 prefixEnd_504997 := by exact prefixLift 504997
  have htrace : WordTrace (prefixWord ++ tailWord_504997) baseStart_504997 baseEnd_504997 := by
    simpa [prefixWord, tailWord_504997, baseEnd_504997] using wordTrace_append hprefix tailTrace_504997
  have hstable : (prefixWord ++ tailWord_504997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_504997).length < 2 ^ (prefixWord ++ tailWord_504997).sum := by decide
  have hdescent : baseEnd_504997 < baseStart_504997 := by decide
  rcases family_descends (prefixWord ++ tailWord_504997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505017 : List Nat := [1, 2, 1, 4, 1, 4, 3, 7]
def baseStart_505017 : Nat := 118140960795 + 505017 * 2 ^ 59
def prefixEnd_505017 : Nat := 4983230072969 + 3 ^ 40 * 505017 * 2
def baseEnd_505017 : Nat := 9604313321916883420925

theorem tailTrace_505017 : CollatzResearch.WordTrace tailWord_505017 prefixEnd_505017 9604313321916883420925 := by
  unfold tailWord_505017
  simp only [CollatzResearch.WordTrace]
  refine ⟨18419483211417133881993305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12279655474278089254662203 18419483211417133881993305)
  ·
    refine ⟨13814612408562850411494979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18419483211417133881993305 13814612408562850411494979)
    ·
      refine ⟨20721918612844275617242469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13814612408562850411494979 20721918612844275617242469)
      ·
        refine ⟨3885359739908301678232963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20721918612844275617242469 3885359739908301678232963)
        ·
          refine ⟨5828039609862452517349445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3885359739908301678232963 5828039609862452517349445)
          ·
            refine ⟨1092757426849209847003021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5828039609862452517349445 1092757426849209847003021)
            ·
              refine ⟨409784035068453692626133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1092757426849209847003021 409784035068453692626133)
              ·
                refine ⟨9604313321916883420925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 409784035068453692626133 9604313321916883420925)
                ·
                  rfl

theorem cell23_505017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 3, 7].length) (baseStart_505017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_505017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_505017 prefixEnd_505017 := by exact prefixLift 505017
  have htrace : WordTrace (prefixWord ++ tailWord_505017) baseStart_505017 baseEnd_505017 := by
    simpa [prefixWord, tailWord_505017, baseEnd_505017] using wordTrace_append hprefix tailTrace_505017
  have hstable : (prefixWord ++ tailWord_505017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505017).length < 2 ^ (prefixWord ++ tailWord_505017).sum := by decide
  have hdescent : baseEnd_505017 < baseStart_505017 := by decide
  rcases family_descends (prefixWord ++ tailWord_505017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505028 : List Nat := [2, 3, 3, 1, 3, 2, 2, 1, 1, 1, 4]
def baseStart_505028 : Nat := 118140960795 + 505028 * 2 ^ 59
def prefixEnd_505028 : Nat := 4983230072969 + 3 ^ 40 * 505028 * 2
def baseEnd_505028 : Nat := 259322107978955309327425

theorem tailTrace_505028 : CollatzResearch.WordTrace tailWord_505028 prefixEnd_505028 259322107978955309327425 := by
  unfold tailWord_505028
  simp only [CollatzResearch.WordTrace]
  refine ⟨9209942207188641380321869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12279922942918188507095825 9209942207188641380321869)
  ·
    refine ⟨3453728327695740517620701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9209942207188641380321869 3453728327695740517620701)
    ·
      refine ⟨1295148122885902694107763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3453728327695740517620701 1295148122885902694107763)
      ·
        refine ⟨1942722184328854041161645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1295148122885902694107763 1942722184328854041161645)
        ·
          refine ⟨728520819123320265435617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1942722184328854041161645 728520819123320265435617)
          ·
            refine ⟨546390614342490199076713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 728520819123320265435617 546390614342490199076713)
            ·
              refine ⟨409792960756867649307535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 546390614342490199076713 409792960756867649307535)
              ·
                refine ⟨614689441135301473961303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 409792960756867649307535 614689441135301473961303)
                ·
                  refine ⟨922034161702952210941955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 614689441135301473961303 922034161702952210941955)
                  ·
                    refine ⟨1383051242554428316412933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 922034161702952210941955 1383051242554428316412933)
                    ·
                      refine ⟨259322107978955309327425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1383051242554428316412933 259322107978955309327425)
                      ·
                        rfl

theorem cell23_505028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 2, 1, 1, 1, 4].length) (baseStart_505028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_505028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_505028 prefixEnd_505028 := by exact prefixLift 505028
  have htrace : WordTrace (prefixWord ++ tailWord_505028) baseStart_505028 baseEnd_505028 := by
    simpa [prefixWord, tailWord_505028, baseEnd_505028] using wordTrace_append hprefix tailTrace_505028
  have hstable : (prefixWord ++ tailWord_505028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505028).length < 2 ^ (prefixWord ++ tailWord_505028).sum := by decide
  have hdescent : baseEnd_505028 < baseStart_505028 := by decide
  rcases family_descends (prefixWord ++ tailWord_505028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505038 : List Nat := [4, 1, 1, 1, 6, 1, 1, 2, 2, 4]
def baseStart_505038 : Nat := 118140960795 + 505038 * 2 ^ 59
def prefixEnd_505038 : Nat := 4983230072969 + 3 ^ 40 * 505038 * 2
def baseEnd_505038 : Nat := 86442414261833423400793

theorem tailTrace_505038 : CollatzResearch.WordTrace tailWord_505038 prefixEnd_505038 86442414261833423400793 := by
  unfold tailWord_505038
  simp only [CollatzResearch.WordTrace]
  refine ⟨2302531143042631808563471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12280166096227369645671845 2302531143042631808563471)
  ·
    refine ⟨3453796714563947712845207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2302531143042631808563471 3453796714563947712845207)
    ·
      refine ⟨5180695071845921569267811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3453796714563947712845207 5180695071845921569267811)
      ·
        refine ⟨7771042607768882353901717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5180695071845921569267811 7771042607768882353901717)
        ·
          refine ⟨364267622239166360339143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 7771042607768882353901717 364267622239166360339143)
          ·
            refine ⟨546401433358749540508715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 364267622239166360339143 546401433358749540508715)
            ·
              refine ⟨819602150038124310763073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 546401433358749540508715 819602150038124310763073)
              ·
                refine ⟨614701612528593233072305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 819602150038124310763073 614701612528593233072305)
                ·
                  refine ⟨461026209396444924804229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 614701612528593233072305 461026209396444924804229)
                  ·
                    refine ⟨86442414261833423400793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 461026209396444924804229 86442414261833423400793)
                    ·
                      rfl

theorem cell23_505038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 1, 2, 2, 4].length) (baseStart_505038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_505038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_505038 prefixEnd_505038 := by exact prefixLift 505038
  have htrace : WordTrace (prefixWord ++ tailWord_505038) baseStart_505038 baseEnd_505038 := by
    simpa [prefixWord, tailWord_505038, baseEnd_505038] using wordTrace_append hprefix tailTrace_505038
  have hstable : (prefixWord ++ tailWord_505038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505038).length < 2 ^ (prefixWord ++ tailWord_505038).sum := by decide
  have hdescent : baseEnd_505038 < baseStart_505038 := by decide
  rcases family_descends (prefixWord ++ tailWord_505038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505061 : List Nat := [1, 3, 1, 4, 3, 2, 1, 1, 1, 3, 3]
def baseStart_505061 : Nat := 118140960795 + 505061 * 2 ^ 59
def prefixEnd_505061 : Nat := 4983230072969 + 3 ^ 40 * 505061 * 2
def baseEnd_505061 : Nat := 259339052840553680214773

theorem tailTrace_505061 : CollatzResearch.WordTrace tailWord_505061 prefixEnd_505061 259339052840553680214773 := by
  unfold tailWord_505061
  simp only [CollatzResearch.WordTrace]
  refine ⟨18421088023257729396595037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12280725348838486264396691 18421088023257729396595037)
  ·
    refine ⟨6907908008721648523723139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18421088023257729396595037 6907908008721648523723139)
    ·
      refine ⟨10361862013082472785584709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6907908008721648523723139 10361862013082472785584709)
      ·
        refine ⟨1942849127452963647297133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10361862013082472785584709 1942849127452963647297133)
        ·
          refine ⟨728568422794861367736425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1942849127452963647297133 728568422794861367736425)
          ·
            refine ⟨546426317096146025802319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 728568422794861367736425 546426317096146025802319)
            ·
              refine ⟨819639475644219038703479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 546426317096146025802319 819639475644219038703479)
              ·
                refine ⟨1229459213466328558055219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 819639475644219038703479 1229459213466328558055219)
                ·
                  refine ⟨1844188820199492837082829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1229459213466328558055219 1844188820199492837082829)
                  ·
                    refine ⟨691570807574809813906061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1844188820199492837082829 691570807574809813906061)
                    ·
                      refine ⟨259339052840553680214773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 691570807574809813906061 259339052840553680214773)
                      ·
                        rfl

theorem cell23_505061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 1, 1, 1, 3, 3].length) (baseStart_505061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_505061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_505061 prefixEnd_505061 := by exact prefixLift 505061
  have htrace : WordTrace (prefixWord ++ tailWord_505061) baseStart_505061 baseEnd_505061 := by
    simpa [prefixWord, tailWord_505061, baseEnd_505061] using wordTrace_append hprefix tailTrace_505061
  have hstable : (prefixWord ++ tailWord_505061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505061).length < 2 ^ (prefixWord ++ tailWord_505061).sum := by decide
  have hdescent : baseEnd_505061 < baseStart_505061 := by decide
  rcases family_descends (prefixWord ++ tailWord_505061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505087 : List Nat := [1, 1, 2, 2, 1, 6, 1, 1, 2, 1, 5]
def baseStart_505087 : Nat := 118140960795 + 505087 * 2 ^ 59
def prefixEnd_505087 : Nat := 4983230072969 + 3 ^ 40 * 505087 * 2
def baseEnd_505087 : Nat := 259352403337570578489653

theorem tailTrace_505087 : CollatzResearch.WordTrace tailWord_505087 prefixEnd_505087 259352403337570578489653 := by
  unfold tailWord_505087
  simp only [CollatzResearch.WordTrace]
  refine ⟨18422036321163535837041515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12281357547442357224694343 18422036321163535837041515)
  ·
    refine ⟨27633054481745303755562273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18422036321163535837041515 27633054481745303755562273)
    ·
      refine ⟨20724790861308977816671705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27633054481745303755562273 20724790861308977816671705)
      ·
        refine ⟨15543593145981733362503779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20724790861308977816671705 15543593145981733362503779)
        ·
          refine ⟨23315389718972600043755669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15543593145981733362503779 23315389718972600043755669)
          ·
            refine ⟨1092908893076840627051047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 23315389718972600043755669 1092908893076840627051047)
            ·
              refine ⟨1639363339615260940576571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1092908893076840627051047 1639363339615260940576571)
              ·
                refine ⟨2459045009422891410864857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1639363339615260940576571 2459045009422891410864857)
                ·
                  refine ⟨1844283757067168558148643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2459045009422891410864857 1844283757067168558148643)
                  ·
                    refine ⟨2766425635600752837222965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1844283757067168558148643 2766425635600752837222965)
                    ·
                      refine ⟨259352403337570578489653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2766425635600752837222965 259352403337570578489653)
                      ·
                        rfl

theorem cell23_505087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 1, 1, 2, 1, 5].length) (baseStart_505087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_505087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_505087 prefixEnd_505087 := by exact prefixLift 505087
  have htrace : WordTrace (prefixWord ++ tailWord_505087) baseStart_505087 baseEnd_505087 := by
    simpa [prefixWord, tailWord_505087, baseEnd_505087] using wordTrace_append hprefix tailTrace_505087
  have hstable : (prefixWord ++ tailWord_505087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505087).length < 2 ^ (prefixWord ++ tailWord_505087).sum := by decide
  have hdescent : baseEnd_505087 < baseStart_505087 := by decide
  rcases family_descends (prefixWord ++ tailWord_505087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505184 : List Nat := [2, 1, 1, 3, 4, 1, 1, 1, 5, 4]
def baseStart_505184 : Nat := 118140960795 + 505184 * 2 ^ 59
def prefixEnd_505184 : Nat := 4983230072969 + 3 ^ 40 * 505184 * 2
def baseEnd_505184 : Nat := 86467403653685566325569

theorem tailTrace_505184 : CollatzResearch.WordTrace tailWord_505184 prefixEnd_505184 86467403653685566325569 := by
  unfold tailWord_505184
  simp only [CollatzResearch.WordTrace]
  refine ⟨9212787100906060701661303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12283716134541414268881737 9212787100906060701661303)
  ·
    refine ⟨13819180651359091052491955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9212787100906060701661303 13819180651359091052491955)
    ·
      refine ⟨20728770977038636578737933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13819180651359091052491955 20728770977038636578737933)
      ·
        refine ⟨7773289116389488717026725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20728770977038636578737933 7773289116389488717026725)
        ·
          refine ⟨1457491709323029134442511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7773289116389488717026725 1457491709323029134442511)
          ·
            refine ⟨2186237563984543701663767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1457491709323029134442511 2186237563984543701663767)
            ·
              refine ⟨3279356345976815552495651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2186237563984543701663767 3279356345976815552495651)
              ·
                refine ⟨4919034518965223328743477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3279356345976815552495651 4919034518965223328743477)
                ·
                  refine ⟨461159486152989687069701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4919034518965223328743477 461159486152989687069701)
                  ·
                    refine ⟨86467403653685566325569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 461159486152989687069701 86467403653685566325569)
                    ·
                      rfl

theorem cell23_505184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 1, 5, 4].length) (baseStart_505184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_505184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_505184 prefixEnd_505184 := by exact prefixLift 505184
  have htrace : WordTrace (prefixWord ++ tailWord_505184) baseStart_505184 baseEnd_505184 := by
    simpa [prefixWord, tailWord_505184, baseEnd_505184] using wordTrace_append hprefix tailTrace_505184
  have hstable : (prefixWord ++ tailWord_505184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505184).length < 2 ^ (prefixWord ++ tailWord_505184).sum := by decide
  have hdescent : baseEnd_505184 < baseStart_505184 := by decide
  rcases family_descends (prefixWord ++ tailWord_505184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505201 : List Nat := [1, 2, 2, 2, 1, 2, 3, 5, 1, 4]
def baseStart_505201 : Nat := 118140960795 + 505201 * 2 ^ 59
def prefixEnd_505201 : Nat := 4983230072969 + 3 ^ 40 * 505201 * 2
def baseEnd_505201 : Nat := 86470313377394377488043

theorem tailTrace_505201 : CollatzResearch.WordTrace tailWord_505201 prefixEnd_505201 86470313377394377488043 := by
  unfold tailWord_505201
  simp only [CollatzResearch.WordTrace]
  refine ⟨18426194242750533306691457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12284129495167022204460971 18426194242750533306691457)
  ·
    refine ⟨13819645682062899980018593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18426194242750533306691457 13819645682062899980018593)
    ·
      refine ⟨10364734261547174985013945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13819645682062899980018593 10364734261547174985013945)
      ·
        refine ⟨7773550696160381238760459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10364734261547174985013945 7773550696160381238760459)
        ·
          refine ⟨11660326044240571858140689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7773550696160381238760459 11660326044240571858140689)
          ·
            refine ⟨8745244533180428893605517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11660326044240571858140689 8745244533180428893605517)
            ·
              refine ⟨3279466699942660835102069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8745244533180428893605517 3279466699942660835102069)
              ·
                refine ⟨307450003119624453290819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3279466699942660835102069 307450003119624453290819)
                ·
                  refine ⟨461175004679436679936229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 307450003119624453290819 461175004679436679936229)
                  ·
                    refine ⟨86470313377394377488043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 461175004679436679936229 86470313377394377488043)
                    ·
                      rfl

theorem cell23_505201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 5, 1, 4].length) (baseStart_505201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_505201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_505201 prefixEnd_505201 := by exact prefixLift 505201
  have htrace : WordTrace (prefixWord ++ tailWord_505201) baseStart_505201 baseEnd_505201 := by
    simpa [prefixWord, tailWord_505201, baseEnd_505201] using wordTrace_append hprefix tailTrace_505201
  have hstable : (prefixWord ++ tailWord_505201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505201).length < 2 ^ (prefixWord ++ tailWord_505201).sum := by decide
  have hdescent : baseEnd_505201 < baseStart_505201 := by decide
  rcases family_descends (prefixWord ++ tailWord_505201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505218 : List Nat := [3, 4, 2, 1, 1, 1, 1, 3, 3, 4]
def baseStart_505218 : Nat := 118140960795 + 505218 * 2 ^ 59
def prefixEnd_505218 : Nat := 4983230072969 + 3 ^ 40 * 505218 * 2
def baseEnd_505218 : Nat := 86473223101103188650517

theorem tailTrace_505218 : CollatzResearch.WordTrace tailWord_505218 prefixEnd_505218 86473223101103188650517 := by
  unfold tailWord_505218
  simp only [CollatzResearch.WordTrace]
  refine ⟨4606703570922236302515077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12284542855792630140040205 4606703570922236302515077)
  ·
    refine ⟨863756919547919306721577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4606703570922236302515077 863756919547919306721577)
    ·
      refine ⟨647817689660939480041183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 863756919547919306721577 647817689660939480041183)
      ·
        refine ⟨971726534491409220061775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 647817689660939480041183 971726534491409220061775)
        ·
          refine ⟨1457589801737113830092663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 971726534491409220061775 1457589801737113830092663)
          ·
            refine ⟨2186384702605670745138995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1457589801737113830092663 2186384702605670745138995)
            ·
              refine ⟨3279577053908506117708493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2186384702605670745138995 3279577053908506117708493)
              ·
                refine ⟨1229841395215689794140685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3279577053908506117708493 1229841395215689794140685)
                ·
                  refine ⟨461190523205883672802757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1229841395215689794140685 461190523205883672802757)
                  ·
                    refine ⟨86473223101103188650517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 461190523205883672802757 86473223101103188650517)
                    ·
                      rfl

theorem cell23_505218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_505218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_505218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_505218 prefixEnd_505218 := by exact prefixLift 505218
  have htrace : WordTrace (prefixWord ++ tailWord_505218) baseStart_505218 baseEnd_505218 := by
    simpa [prefixWord, tailWord_505218, baseEnd_505218] using wordTrace_append hprefix tailTrace_505218
  have hstable : (prefixWord ++ tailWord_505218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505218).length < 2 ^ (prefixWord ++ tailWord_505218).sum := by decide
  have hdescent : baseEnd_505218 < baseStart_505218 := by decide
  rcases family_descends (prefixWord ++ tailWord_505218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505237 : List Nat := [1, 3, 2, 1, 1, 2, 2, 1, 2, 1, 7]
def baseStart_505237 : Nat := 118140960795 + 505237 * 2 ^ 59
def prefixEnd_505237 : Nat := 4983230072969 + 3 ^ 40 * 505237 * 2
def baseEnd_505237 : Nat := 259429425435744991613963

theorem tailTrace_505237 : CollatzResearch.WordTrace tailWord_505237 prefixEnd_505237 259429425435744991613963 := by
  unfold tailWord_505237
  simp only [CollatzResearch.WordTrace]
  refine ⟨18427507270620111455001965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12285004847080074303334643 18427507270620111455001965)
  ·
    refine ⟨6910315226482541795625737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18427507270620111455001965 6910315226482541795625737)
    ·
      refine ⟨5182736419861906346719303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6910315226482541795625737 5182736419861906346719303)
      ·
        refine ⟨7774104629792859520078955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5182736419861906346719303 7774104629792859520078955)
        ·
          refine ⟨11661156944689289280118433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7774104629792859520078955 11661156944689289280118433)
          ·
            refine ⟨8745867708516966960088825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11661156944689289280118433 8745867708516966960088825)
            ·
              refine ⟨6559400781387725220066619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8745867708516966960088825 6559400781387725220066619)
              ·
                refine ⟨9839101172081587830099929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6559400781387725220066619 9839101172081587830099929)
                ·
                  refine ⟨7379325879061190872574947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9839101172081587830099929 7379325879061190872574947)
                  ·
                    refine ⟨11068988818591786308862421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7379325879061190872574947 11068988818591786308862421)
                    ·
                      refine ⟨259429425435744991613963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 11068988818591786308862421 259429425435744991613963)
                      ·
                        rfl

theorem cell23_505237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 1, 2, 1, 7].length) (baseStart_505237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_505237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_505237 prefixEnd_505237 := by exact prefixLift 505237
  have htrace : WordTrace (prefixWord ++ tailWord_505237) baseStart_505237 baseEnd_505237 := by
    simpa [prefixWord, tailWord_505237, baseEnd_505237] using wordTrace_append hprefix tailTrace_505237
  have hstable : (prefixWord ++ tailWord_505237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505237).length < 2 ^ (prefixWord ++ tailWord_505237).sum := by decide
  have hdescent : baseEnd_505237 < baseStart_505237 := by decide
  rcases family_descends (prefixWord ++ tailWord_505237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505241 : List Nat := [1, 2, 1, 2, 1, 5, 2, 2, 3, 1, 3]
def baseStart_505241 : Nat := 118140960795 + 505241 * 2 ^ 59
def prefixEnd_505241 : Nat := 4983230072969 + 3 ^ 40 * 505241 * 2
def baseEnd_505241 : Nat := 259431479358362975963945

theorem tailTrace_505241 : CollatzResearch.WordTrace tailWord_505241 prefixEnd_505241 259431479358362975963945 := by
  unfold tailWord_505241
  simp only [CollatzResearch.WordTrace]
  refine ⟨18427653162605620138147577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12285102108403746758765051 18427653162605620138147577)
  ·
    refine ⟨13820739871954215103610683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18427653162605620138147577 13820739871954215103610683)
    ·
      refine ⟨20731109807931322655416025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13820739871954215103610683 20731109807931322655416025)
      ·
        refine ⟨15548332355948491991562019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20731109807931322655416025 15548332355948491991562019)
        ·
          refine ⟨23322498533922737987343029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15548332355948491991562019 23322498533922737987343029)
          ·
            refine ⟨2186484237555256686313409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23322498533922737987343029 2186484237555256686313409)
            ·
              refine ⟨1639863178166442514735057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2186484237555256686313409 1639863178166442514735057)
              ·
                refine ⟨1229897383624831886051293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1639863178166442514735057 1229897383624831886051293)
                ·
                  refine ⟨461211518859311957269235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1229897383624831886051293 461211518859311957269235)
                  ·
                    refine ⟨691817278288967935903853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 461211518859311957269235 691817278288967935903853)
                    ·
                      refine ⟨259431479358362975963945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 691817278288967935903853 259431479358362975963945)
                      ·
                        rfl

theorem cell23_505241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 2, 3, 1, 3].length) (baseStart_505241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_505241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_505241 prefixEnd_505241 := by exact prefixLift 505241
  have htrace : WordTrace (prefixWord ++ tailWord_505241) baseStart_505241 baseEnd_505241 := by
    simpa [prefixWord, tailWord_505241, baseEnd_505241] using wordTrace_append hprefix tailTrace_505241
  have hstable : (prefixWord ++ tailWord_505241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505241).length < 2 ^ (prefixWord ++ tailWord_505241).sum := by decide
  have hdescent : baseEnd_505241 < baseStart_505241 := by decide
  rcases family_descends (prefixWord ++ tailWord_505241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505251 : List Nat := [1, 1, 1, 4, 1, 3, 2, 3, 2, 3, 2]
def baseStart_505251 : Nat := 118140960795 + 505251 * 2 ^ 59
def prefixEnd_505251 : Nat := 4983230072969 + 3 ^ 40 * 505251 * 2
def baseEnd_505251 : Nat := 259436614164907936838899

theorem tailTrace_505251 : CollatzResearch.WordTrace tailWord_505251 prefixEnd_505251 259436614164907936838899 := by
  unfold tailWord_505251
  simp only [CollatzResearch.WordTrace]
  refine ⟨18428017892569391846011607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12285345261712927897341071 18428017892569391846011607)
  ·
    refine ⟨27642026838854087769017411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18428017892569391846011607 27642026838854087769017411)
    ·
      refine ⟨41463040258281131653526117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27642026838854087769017411 41463040258281131653526117)
      ·
        refine ⟨7774320048427712185036147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41463040258281131653526117 7774320048427712185036147)
        ·
          refine ⟨11661480072641568277554221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7774320048427712185036147 11661480072641568277554221)
          ·
            refine ⟨4373055027240588104082833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11661480072641568277554221 4373055027240588104082833)
            ·
              refine ⟨3279791270430441078062125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4373055027240588104082833 3279791270430441078062125)
              ·
                refine ⟨1229921726411415404273297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3279791270430441078062125 1229921726411415404273297)
                ·
                  refine ⟨922441294808561553204973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1229921726411415404273297 922441294808561553204973)
                  ·
                    refine ⟨345915485553210582451865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 922441294808561553204973 345915485553210582451865)
                    ·
                      refine ⟨259436614164907936838899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 345915485553210582451865 259436614164907936838899)
                      ·
                        rfl

theorem cell23_505251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 3, 2, 3, 2].length) (baseStart_505251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_505251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_505251 prefixEnd_505251 := by exact prefixLift 505251
  have htrace : WordTrace (prefixWord ++ tailWord_505251) baseStart_505251 baseEnd_505251 := by
    simpa [prefixWord, tailWord_505251, baseEnd_505251] using wordTrace_append hprefix tailTrace_505251
  have hstable : (prefixWord ++ tailWord_505251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505251).length < 2 ^ (prefixWord ++ tailWord_505251).sum := by decide
  have hdescent : baseEnd_505251 < baseStart_505251 := by decide
  rcases family_descends (prefixWord ++ tailWord_505251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505282 : List Nat := [3, 5, 2, 1, 1, 1, 1, 3, 6]
def baseStart_505282 : Nat := 118140960795 + 505282 * 2 ^ 59
def prefixEnd_505282 : Nat := 4983230072969 + 3 ^ 40 * 505282 * 2
def baseEnd_505282 : Nat := 28828059118355257283473

theorem tailTrace_505282 : CollatzResearch.WordTrace tailWord_505282 prefixEnd_505282 28828059118355257283473 := by
  unfold tailWord_505282
  simp only [CollatzResearch.WordTrace]
  refine ⟨4607287138864271035097525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12286099036971389426926733 4607287138864271035097525)
  ·
    refine ⟨431933169268525409540393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4607287138864271035097525 431933169268525409540393)
    ·
      refine ⟨323949876951394057155295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 431933169268525409540393 323949876951394057155295)
      ·
        refine ⟨485924815427091085732943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323949876951394057155295 485924815427091085732943)
        ·
          refine ⟨728887223140636628599415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 485924815427091085732943 728887223140636628599415)
          ·
            refine ⟨1093330834710954942899123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 728887223140636628599415 1093330834710954942899123)
            ·
              refine ⟨1639996252066432414348685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1093330834710954942899123 1639996252066432414348685)
              ·
                refine ⟨614998594524912155380757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1639996252066432414348685 614998594524912155380757)
                ·
                  refine ⟨28828059118355257283473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 614998594524912155380757 28828059118355257283473)
                  ·
                    rfl

theorem cell23_505282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 3, 6].length) (baseStart_505282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_505282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_505282 prefixEnd_505282 := by exact prefixLift 505282
  have htrace : WordTrace (prefixWord ++ tailWord_505282) baseStart_505282 baseEnd_505282 := by
    simpa [prefixWord, tailWord_505282, baseEnd_505282] using wordTrace_append hprefix tailTrace_505282
  have hstable : (prefixWord ++ tailWord_505282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505282).length < 2 ^ (prefixWord ++ tailWord_505282).sum := by decide
  have hdescent : baseEnd_505282 < baseStart_505282 := by decide
  rcases family_descends (prefixWord ++ tailWord_505282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505294 : List Nat := [4, 1, 1, 1, 2, 1, 4, 1, 1, 1, 6]
def baseStart_505294 : Nat := 118140960795 + 505294 * 2 ^ 59
def prefixEnd_505294 : Nat := 4983230072969 + 3 ^ 40 * 505294 * 2
def baseEnd_505294 : Nat := 259458693833051268601201

theorem tailTrace_505294 : CollatzResearch.WordTrace tailWord_505294 prefixEnd_505294 259458693833051268601201 := by
  unfold tailWord_505294
  simp only [CollatzResearch.WordTrace]
  refine ⟨2303698278926701273728367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12286390820942406793217957 2303698278926701273728367)
  ·
    refine ⟨3455547418390051910592551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2303698278926701273728367 3455547418390051910592551)
    ·
      refine ⟨5183321127585077865888827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3455547418390051910592551 5183321127585077865888827)
      ·
        refine ⟨7774981691377616798833241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5183321127585077865888827 7774981691377616798833241)
        ·
          refine ⟨5831236268533212599124931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7774981691377616798833241 5831236268533212599124931)
          ·
            refine ⟨8746854402799818898687397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5831236268533212599124931 8746854402799818898687397)
            ·
              refine ⟨1640035200524966043503887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8746854402799818898687397 1640035200524966043503887)
              ·
                refine ⟨2460052800787449065255831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1640035200524966043503887 2460052800787449065255831)
                ·
                  refine ⟨3690079201181173597883747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2460052800787449065255831 3690079201181173597883747)
                  ·
                    refine ⟨5535118801771760396825621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3690079201181173597883747 5535118801771760396825621)
                    ·
                      refine ⟨259458693833051268601201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 5535118801771760396825621 259458693833051268601201)
                      ·
                        rfl

theorem cell23_505294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 1, 1, 1, 6].length) (baseStart_505294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_505294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_505294 prefixEnd_505294 := by exact prefixLift 505294
  have htrace : WordTrace (prefixWord ++ tailWord_505294) baseStart_505294 baseEnd_505294 := by
    simpa [prefixWord, tailWord_505294, baseEnd_505294] using wordTrace_append hprefix tailTrace_505294
  have hstable : (prefixWord ++ tailWord_505294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505294).length < 2 ^ (prefixWord ++ tailWord_505294).sum := by decide
  have hdescent : baseEnd_505294 < baseStart_505294 := by decide
  rcases family_descends (prefixWord ++ tailWord_505294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505301 : List Nat := [1, 3, 2, 3, 1, 1, 3, 1, 3, 2, 3]
def baseStart_505301 : Nat := 118140960795 + 505301 * 2 ^ 59
def prefixEnd_505301 : Nat := 4983230072969 + 3 ^ 40 * 505301 * 2
def baseEnd_505301 : Nat := 259462288197632741213669

theorem tailTrace_505301 : CollatzResearch.WordTrace tailWord_505301 prefixEnd_505301 259462288197632741213669 := by
  unfold tailWord_505301
  simp only [CollatzResearch.WordTrace]
  refine ⟨18429841542388250385331757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12286561028258833590221171 18429841542388250385331757)
  ·
    refine ⟨6911190578395593894499409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18429841542388250385331757 6911190578395593894499409)
    ·
      refine ⟨5183392933796695420874557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6911190578395593894499409 5183392933796695420874557)
      ·
        refine ⟨1943772350173760782827959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5183392933796695420874557 1943772350173760782827959)
        ·
          refine ⟨2915658525260641174241939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1943772350173760782827959 2915658525260641174241939)
          ·
            refine ⟨4373487787890961761362909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2915658525260641174241939 4373487787890961761362909)
            ·
              refine ⟨1640057920459110660511091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4373487787890961761362909 1640057920459110660511091)
              ·
                refine ⟨2460086880688665990766637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1640057920459110660511091 2460086880688665990766637)
                ·
                  refine ⟨922532580258249746537489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2460086880688665990766637 922532580258249746537489)
                  ·
                    refine ⟨691899435193687309903117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 922532580258249746537489 691899435193687309903117)
                    ·
                      refine ⟨259462288197632741213669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 691899435193687309903117 259462288197632741213669)
                      ·
                        rfl

theorem cell23_505301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 1, 3, 2, 3].length) (baseStart_505301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_505301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_505301 prefixEnd_505301 := by exact prefixLift 505301
  have htrace : WordTrace (prefixWord ++ tailWord_505301) baseStart_505301 baseEnd_505301 := by
    simpa [prefixWord, tailWord_505301, baseEnd_505301] using wordTrace_append hprefix tailTrace_505301
  have hstable : (prefixWord ++ tailWord_505301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505301).length < 2 ^ (prefixWord ++ tailWord_505301).sum := by decide
  have hdescent : baseEnd_505301 < baseStart_505301 := by decide
  rcases family_descends (prefixWord ++ tailWord_505301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505325 : List Nat := [1, 5, 1, 3, 2, 1, 2, 2, 2, 4]
def baseStart_505325 : Nat := 118140960795 + 505325 * 2 ^ 59
def prefixEnd_505325 : Nat := 4983230072969 + 3 ^ 40 * 505325 * 2
def baseEnd_505325 : Nat := 86491537244446882437853

theorem tailTrace_505325 : CollatzResearch.WordTrace tailWord_505325 prefixEnd_505325 86491537244446882437853 := by
  unfold tailWord_505325
  simp only [CollatzResearch.WordTrace]
  refine ⟨18430716894301302484205429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12287144596200868322803619 18430716894301302484205429)
  ·
    refine ⟨1727879708840747107894259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18430716894301302484205429 1727879708840747107894259)
    ·
      refine ⟨2591819563261120661841389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1727879708840747107894259 2591819563261120661841389)
      ·
        refine ⟨971932336222920248190521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2591819563261120661841389 971932336222920248190521)
        ·
          refine ⟨728949252167190186142891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 971932336222920248190521 728949252167190186142891)
          ·
            refine ⟨1093423878250785279214337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 728949252167190186142891 1093423878250785279214337)
            ·
              refine ⟨820067908688088959410753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1093423878250785279214337 820067908688088959410753)
              ·
                refine ⟨615050931516066719558065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 820067908688088959410753 615050931516066719558065)
                ·
                  refine ⟨461288198637050039668549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 615050931516066719558065 461288198637050039668549)
                  ·
                    refine ⟨86491537244446882437853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 461288198637050039668549 86491537244446882437853)
                    ·
                      rfl

theorem cell23_505325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 2, 2, 2, 4].length) (baseStart_505325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_505325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_505325 prefixEnd_505325 := by exact prefixLift 505325
  have htrace : WordTrace (prefixWord ++ tailWord_505325) baseStart_505325 baseEnd_505325 := by
    simpa [prefixWord, tailWord_505325, baseEnd_505325] using wordTrace_append hprefix tailTrace_505325
  have hstable : (prefixWord ++ tailWord_505325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505325).length < 2 ^ (prefixWord ++ tailWord_505325).sum := by decide
  have hdescent : baseEnd_505325 < baseStart_505325 := by decide
  rcases family_descends (prefixWord ++ tailWord_505325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505375 : List Nat := [1, 1, 2, 4, 1, 1, 6, 1, 1, 3, 2]
def baseStart_505375 : Nat := 118140960795 + 505375 * 2 ^ 59
def prefixEnd_505375 : Nat := 4983230072969 + 3 ^ 40 * 505375 * 2
def baseEnd_505375 : Nat := 259500285766065451688329

theorem tailTrace_505375 : CollatzResearch.WordTrace tailWord_505375 prefixEnd_505375 259500285766065451688329 := by
  unfold tailWord_505375
  simp only [CollatzResearch.WordTrace]
  refine ⟨18432540544120161023525579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12288360362746774015683719 18432540544120161023525579)
  ·
    refine ⟨27648810816180241535288369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18432540544120161023525579 27648810816180241535288369)
    ·
      refine ⟨20736608112135181151466277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27648810816180241535288369 20736608112135181151466277)
      ·
        refine ⟨3888114021025346465899927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20736608112135181151466277 3888114021025346465899927)
        ·
          refine ⟨5832171031538019698849891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3888114021025346465899927 5832171031538019698849891)
          ·
            refine ⟨8748256547307029548274837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5832171031538019698849891 8748256547307029548274837)
            ·
              refine ⟨410074525655017010075383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 8748256547307029548274837 410074525655017010075383)
              ·
                refine ⟨615111788482525515113075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 410074525655017010075383 615111788482525515113075)
                ·
                  refine ⟨922667682723788272669613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 615111788482525515113075 922667682723788272669613)
                  ·
                    refine ⟨346000381021420602251105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 922667682723788272669613 346000381021420602251105)
                    ·
                      refine ⟨259500285766065451688329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 346000381021420602251105 259500285766065451688329)
                      ·
                        rfl

theorem cell23_505375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 6, 1, 1, 3, 2].length) (baseStart_505375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_505375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_505375 prefixEnd_505375 := by exact prefixLift 505375
  have htrace : WordTrace (prefixWord ++ tailWord_505375) baseStart_505375 baseEnd_505375 := by
    simpa [prefixWord, tailWord_505375, baseEnd_505375] using wordTrace_append hprefix tailTrace_505375
  have hstable : (prefixWord ++ tailWord_505375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505375).length < 2 ^ (prefixWord ++ tailWord_505375).sum := by decide
  have hdescent : baseEnd_505375 < baseStart_505375 := by decide
  rcases family_descends (prefixWord ++ tailWord_505375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505401 : List Nat := [1, 2, 1, 5, 1, 2, 2, 1, 2, 2, 4]
def baseStart_505401 : Nat := 118140960795 + 505401 * 2 ^ 59
def prefixEnd_505401 : Nat := 4983230072969 + 3 ^ 40 * 505401 * 2
def baseEnd_505401 : Nat := 259513636263082349963209

theorem tailTrace_505401 : CollatzResearch.WordTrace tailWord_505401 prefixEnd_505401 259513636263082349963209 := by
  unfold tailWord_505401
  simp only [CollatzResearch.WordTrace]
  refine ⟨18433488842025967463972057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12288992561350644975981371 18433488842025967463972057)
  ·
    refine ⟨13825116631519475597979043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18433488842025967463972057 13825116631519475597979043)
    ·
      refine ⟨20737674947279213396968565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13825116631519475597979043 20737674947279213396968565)
      ·
        refine ⟨1944157026307426255965803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20737674947279213396968565 1944157026307426255965803)
        ·
          refine ⟨2916235539461139383948705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1944157026307426255965803 2916235539461139383948705)
          ·
            refine ⟨2187176654595854537961529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2916235539461139383948705 2187176654595854537961529)
            ·
              refine ⟨1640382490946890903471147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2187176654595854537961529 1640382490946890903471147)
              ·
                refine ⟨2460573736420336355206721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1640382490946890903471147 2460573736420336355206721)
                ·
                  refine ⟨1845430302315252266405041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2460573736420336355206721 1845430302315252266405041)
                  ·
                    refine ⟨1384072726736439199803781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1845430302315252266405041 1384072726736439199803781)
                    ·
                      refine ⟨259513636263082349963209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1384072726736439199803781 259513636263082349963209)
                      ·
                        rfl

theorem cell23_505401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_505401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_505401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_505401 prefixEnd_505401 := by exact prefixLift 505401
  have htrace : WordTrace (prefixWord ++ tailWord_505401) baseStart_505401 baseEnd_505401 := by
    simpa [prefixWord, tailWord_505401, baseEnd_505401] using wordTrace_append hprefix tailTrace_505401
  have hstable : (prefixWord ++ tailWord_505401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505401).length < 2 ^ (prefixWord ++ tailWord_505401).sum := by decide
  have hdescent : baseEnd_505401 < baseStart_505401 := by decide
  rcases family_descends (prefixWord ++ tailWord_505401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505424 : List Nat := [2, 1, 1, 1, 1, 3, 3, 3, 1, 7]
def baseStart_505424 : Nat := 118140960795 + 505424 * 2 ^ 59
def prefixEnd_505424 : Nat := 4983230072969 + 3 ^ 40 * 505424 * 2
def baseEnd_505424 : Nat := 86508482106045253325201

theorem tailTrace_505424 : CollatzResearch.WordTrace tailWord_505424 prefixEnd_505424 86508482106045253325201 := by
  unfold tailWord_505424
  simp only [CollatzResearch.WordTrace]
  refine ⟨9217163860471321196029663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12289551813961761594706217 9217163860471321196029663)
  ·
    refine ⟨13825745790706981794044495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9217163860471321196029663 13825745790706981794044495)
    ·
      refine ⟨20738618686060472691066743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13825745790706981794044495 20738618686060472691066743)
      ·
        refine ⟨31107928029090709036600115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20738618686060472691066743 31107928029090709036600115)
        ·
          refine ⟨46661892043636063554900173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31107928029090709036600115 46661892043636063554900173)
          ·
            refine ⟨17498209516363523833087565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46661892043636063554900173 17498209516363523833087565)
            ·
              refine ⟨6561828568636321437407837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17498209516363523833087565 6561828568636321437407837)
              ·
                refine ⟨2460685713238620539027939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6561828568636321437407837 2460685713238620539027939)
                ·
                  refine ⟨3691028569857930808541909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2460685713238620539027939 3691028569857930808541909)
                  ·
                    refine ⟨86508482106045253325201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3691028569857930808541909 86508482106045253325201)
                    ·
                      rfl

theorem cell23_505424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 3, 1, 7].length) (baseStart_505424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_505424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_505424 prefixEnd_505424 := by exact prefixLift 505424
  have htrace : WordTrace (prefixWord ++ tailWord_505424) baseStart_505424 baseEnd_505424 := by
    simpa [prefixWord, tailWord_505424, baseEnd_505424] using wordTrace_append hprefix tailTrace_505424
  have hstable : (prefixWord ++ tailWord_505424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505424).length < 2 ^ (prefixWord ++ tailWord_505424).sum := by decide
  have hdescent : baseEnd_505424 < baseStart_505424 := by decide
  rcases family_descends (prefixWord ++ tailWord_505424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_505434 : List Nat := [3, 1, 1, 2, 1, 1, 1, 2, 3, 1, 7]
def baseStart_505434 : Nat := 118140960795 + 505434 * 2 ^ 59
def prefixEnd_505434 : Nat := 4983230072969 + 3 ^ 40 * 505434 * 2
def baseEnd_505434 : Nat := 259530581124680720850557

theorem tailTrace_505434 : CollatzResearch.WordTrace tailWord_505434 prefixEnd_505434 259530581124680720850557 := by
  unfold tailWord_505434
  simp only [CollatzResearch.WordTrace]
  refine ⟨4608673112726603524980839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12289794967270942733282237 4608673112726603524980839)
  ·
    refine ⟨6913009669089905287471259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4608673112726603524980839 6913009669089905287471259)
    ·
      refine ⟨10369514503634857931206889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6913009669089905287471259 10369514503634857931206889)
      ·
        refine ⟨7777135877726143448405167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10369514503634857931206889 7777135877726143448405167)
        ·
          refine ⟨11665703816589215172607751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7777135877726143448405167 11665703816589215172607751)
          ·
            refine ⟨17498555724883822758911627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11665703816589215172607751 17498555724883822758911627)
            ·
              refine ⟨26247833587325734138367441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17498555724883822758911627 26247833587325734138367441)
              ·
                refine ⟨19685875190494300603775581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26247833587325734138367441 19685875190494300603775581)
                ·
                  refine ⟨7382203196435362726415843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19685875190494300603775581 7382203196435362726415843)
                  ·
                    refine ⟨11073304794653044089623765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7382203196435362726415843 11073304794653044089623765)
                    ·
                      refine ⟨259530581124680720850557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 11073304794653044089623765 259530581124680720850557)
                      ·
                        rfl

theorem cell23_505434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 3, 1, 7].length) (baseStart_505434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_505434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_505434 prefixEnd_505434 := by exact prefixLift 505434
  have htrace : WordTrace (prefixWord ++ tailWord_505434) baseStart_505434 baseEnd_505434 := by
    simpa [prefixWord, tailWord_505434, baseEnd_505434] using wordTrace_append hprefix tailTrace_505434
  have hstable : (prefixWord ++ tailWord_505434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_505434).length < 2 ^ (prefixWord ++ tailWord_505434).sum := by decide
  have hdescent : baseEnd_505434 < baseStart_505434 := by decide
  rcases family_descends (prefixWord ++ tailWord_505434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
