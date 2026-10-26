import V185TrunkScan20Chunk049

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_304130 : List Nat := [3, 4, 1, 3, 2, 1, 2, 4]
def baseStart_304130 : Nat := 118140960795 + 304130 * 2 ^ 59
def prefixEnd_304130 : Nat := 4983230072969 + 3 ^ 40 * 304130 * 2
def baseEnd_304130 : Nat := 46271073022814910718915

theorem tailTrace_304130 : CollatzResearch.WordTrace tailWord_304130 prefixEnd_304130 46271073022814910718915 := by
  unfold tailWord_304130
  simp only [CollatzResearch.WordTrace]
  refine ⟨2773133097049106528463461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7395021592130950742569229 2773133097049106528463461)
  ·
    refine ⟨519962455696707474086899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2773133097049106528463461 519962455696707474086899)
    ·
      refine ⟨779943683545061211130349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 519962455696707474086899 779943683545061211130349)
      ·
        refine ⟨292478881329397954173881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 779943683545061211130349 292478881329397954173881)
        ·
          refine ⟨219359160997048465630411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 292478881329397954173881 219359160997048465630411)
          ·
            refine ⟨329038741495572698445617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 219359160997048465630411 329038741495572698445617)
            ·
              refine ⟨246779056121679523834213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 329038741495572698445617 246779056121679523834213)
              ·
                refine ⟨46271073022814910718915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 246779056121679523834213 46271073022814910718915)
                ·
                  rfl

theorem cell20_304130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 2, 4].length) (baseStart_304130 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_304130 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_304130 prefixEnd_304130 := by exact prefixLift 304130
  have htrace : WordTrace (prefixWord ++ tailWord_304130) baseStart_304130 baseEnd_304130 := by
    simpa [prefixWord, tailWord_304130, baseEnd_304130] using wordTrace_append hprefix tailTrace_304130
  have hstable : (prefixWord ++ tailWord_304130).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304130).length < 2 ^ (prefixWord ++ tailWord_304130).sum := by decide
  have hdescent : baseEnd_304130 < baseStart_304130 := by decide
  rcases family_descends (prefixWord ++ tailWord_304130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304138 : List Nat := [3, 1, 2, 2, 3, 2, 1, 6]
def baseStart_304138 : Nat := 118140960795 + 304138 * 2 ^ 59
def prefixEnd_304138 : Nat := 4983230072969 + 3 ^ 40 * 304138 * 2
def baseEnd_304138 : Nat := 46272290162144086630015

theorem tailTrace_304138 : CollatzResearch.WordTrace tailWord_304138 prefixEnd_304138 46272290162144086630015 := by
  unfold tailWord_304138
  simp only [CollatzResearch.WordTrace]
  refine ⟨2773206043041860870036267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7395216114778295653430045 2773206043041860870036267)
  ·
    refine ⟨4159809064562791305054401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2773206043041860870036267 4159809064562791305054401)
    ·
      refine ⟨3119856798422093478790801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4159809064562791305054401 3119856798422093478790801)
      ·
        refine ⟨2339892598816570109093101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3119856798422093478790801 2339892598816570109093101)
        ·
          refine ⟨877459724556213790909913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2339892598816570109093101 877459724556213790909913)
          ·
            refine ⟨658094793417160343182435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 877459724556213790909913 658094793417160343182435)
            ·
              refine ⟨987142190125740514773653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 658094793417160343182435 987142190125740514773653)
              ·
                refine ⟨46272290162144086630015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 987142190125740514773653 46272290162144086630015)
                ·
                  rfl

theorem cell20_304138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 6].length) (baseStart_304138 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_304138 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_304138 prefixEnd_304138 := by exact prefixLift 304138
  have htrace : WordTrace (prefixWord ++ tailWord_304138) baseStart_304138 baseEnd_304138 := by
    simpa [prefixWord, tailWord_304138, baseEnd_304138] using wordTrace_append hprefix tailTrace_304138
  have hstable : (prefixWord ++ tailWord_304138).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304138).length < 2 ^ (prefixWord ++ tailWord_304138).sum := by decide
  have hdescent : baseEnd_304138 < baseStart_304138 := by decide
  rcases family_descends (prefixWord ++ tailWord_304138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304159 : List Nat := [1, 1, 2, 4, 1, 3, 8]
def baseStart_304159 : Nat := 118140960795 + 304159 * 2 ^ 59
def prefixEnd_304159 : Nat := 4983230072969 + 3 ^ 40 * 304159 * 2
def baseEnd_304159 : Nat := 15425161717627724465551

theorem tailTrace_304159 : CollatzResearch.WordTrace tailWord_304159 prefixEnd_304159 15425161717627724465551 := by
  unfold tailWord_304159
  simp only [CollatzResearch.WordTrace]
  refine ⟨11093590105091364066659531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7395726736727576044439687 11093590105091364066659531)
  ·
    refine ⟨16640385157637046099989297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11093590105091364066659531 16640385157637046099989297)
    ·
      refine ⟨12480288868227784574991973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16640385157637046099989297 12480288868227784574991973)
      ·
        refine ⟨2340054162792709607810995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12480288868227784574991973 2340054162792709607810995)
        ·
          refine ⟨3510081244189064411716493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2340054162792709607810995 3510081244189064411716493)
          ·
            refine ⟨1316280466570899154393685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3510081244189064411716493 1316280466570899154393685)
            ·
              refine ⟨15425161717627724465551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1316280466570899154393685 15425161717627724465551)
              ·
                rfl

theorem cell20_304159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 8].length) (baseStart_304159 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_304159 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_304159 prefixEnd_304159 := by exact prefixLift 304159
  have htrace : WordTrace (prefixWord ++ tailWord_304159) baseStart_304159 baseEnd_304159 := by
    simpa [prefixWord, tailWord_304159, baseEnd_304159] using wordTrace_append hprefix tailTrace_304159
  have hstable : (prefixWord ++ tailWord_304159).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304159).length < 2 ^ (prefixWord ++ tailWord_304159).sum := by decide
  have hdescent : baseEnd_304159 < baseStart_304159 := by decide
  rcases family_descends (prefixWord ++ tailWord_304159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304197 : List Nat := [1, 3, 1, 1, 1, 3, 4, 6]
def baseStart_304197 : Nat := 118140960795 + 304197 * 2 ^ 59
def prefixEnd_304197 : Nat := 4983230072969 + 3 ^ 40 * 304197 * 2
def baseEnd_304197 : Nat := 46281266564696758974379

theorem tailTrace_304197 : CollatzResearch.WordTrace tailWord_304197 prefixEnd_304197 46281266564696758974379 := by
  unfold tailWord_304197
  simp only [CollatzResearch.WordTrace]
  refine ⟨11094976078953696556542845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7396650719302464371028563 11094976078953696556542845)
  ·
    refine ⟨4160616029607636208703567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11094976078953696556542845 4160616029607636208703567)
    ·
      refine ⟨6240924044411454313055351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4160616029607636208703567 6240924044411454313055351)
      ·
        refine ⟨9361386066617181469583027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6240924044411454313055351 9361386066617181469583027)
        ·
          refine ⟨14042079099925772204374541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9361386066617181469583027 14042079099925772204374541)
          ·
            refine ⟨5265779662472164576640453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14042079099925772204374541 5265779662472164576640453)
            ·
              refine ⟨987333686713530858120085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5265779662472164576640453 987333686713530858120085)
              ·
                refine ⟨46281266564696758974379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 987333686713530858120085 46281266564696758974379)
                ·
                  rfl

theorem cell20_304197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 6].length) (baseStart_304197 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_304197 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_304197 prefixEnd_304197 := by exact prefixLift 304197
  have htrace : WordTrace (prefixWord ++ tailWord_304197) baseStart_304197 baseEnd_304197 := by
    simpa [prefixWord, tailWord_304197, baseEnd_304197] using wordTrace_append hprefix tailTrace_304197
  have hstable : (prefixWord ++ tailWord_304197).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304197).length < 2 ^ (prefixWord ++ tailWord_304197).sum := by decide
  have hdescent : baseEnd_304197 < baseStart_304197 := by decide
  rcases family_descends (prefixWord ++ tailWord_304197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304228 : List Nat := [2, 3, 1, 1, 2, 1, 1, 5, 4]
def baseStart_304228 : Nat := 118140960795 + 304228 * 2 ^ 59
def prefixEnd_304228 : Nat := 4983230072969 + 3 ^ 40 * 304228 * 2
def baseEnd_304228 : Nat := 138857948938791946889677

theorem tailTrace_304228 : CollatzResearch.WordTrace tailWord_304228 prefixEnd_304228 138857948938791946889677 := by
  unfold tailWord_304228
  simp only [CollatzResearch.WordTrace]
  refine ⟨5548053370920694425460669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7397404494560925900614225 5548053370920694425460669)
  ·
    refine ⟨2080520014095260409547751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5548053370920694425460669 2080520014095260409547751)
    ·
      refine ⟨3120780021142890614321627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2080520014095260409547751 3120780021142890614321627)
      ·
        refine ⟨4681170031714335921482441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3120780021142890614321627 4681170031714335921482441)
        ·
          refine ⟨3510877523785751941111831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4681170031714335921482441 3510877523785751941111831)
          ·
            refine ⟨5266316285678627911667747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3510877523785751941111831 5266316285678627911667747)
            ·
              refine ⟨7899474428517941867501621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5266316285678627911667747 7899474428517941867501621)
              ·
                refine ⟨740575727673557050078277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7899474428517941867501621 740575727673557050078277)
                ·
                  refine ⟨138857948938791946889677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 740575727673557050078277 138857948938791946889677)
                  ·
                    rfl

theorem cell20_304228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 5, 4].length) (baseStart_304228 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_304228 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_304228 prefixEnd_304228 := by exact prefixLift 304228
  have htrace : WordTrace (prefixWord ++ tailWord_304228) baseStart_304228 baseEnd_304228 := by
    simpa [prefixWord, tailWord_304228, baseEnd_304228] using wordTrace_append hprefix tailTrace_304228
  have hstable : (prefixWord ++ tailWord_304228).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304228).length < 2 ^ (prefixWord ++ tailWord_304228).sum := by decide
  have hdescent : baseEnd_304228 < baseStart_304228 := by decide
  rcases family_descends (prefixWord ++ tailWord_304228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304238 : List Nat := [4, 1, 2, 2, 1, 2, 2, 3, 3]
def baseStart_304238 : Nat := 118140960795 + 304238 * 2 ^ 59
def prefixEnd_304238 : Nat := 4983230072969 + 3 ^ 40 * 304238 * 2
def baseEnd_304238 : Nat := 138862513211276356556303

theorem tailTrace_304238 : CollatzResearch.WordTrace tailWord_304238 prefixEnd_304238 138862513211276356556303 := by
  unfold tailWord_304238
  simp only [CollatzResearch.WordTrace]
  refine ⟨1387058933975645069848171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7397647647870107039190245 1387058933975645069848171)
  ·
    refine ⟨2080588400963467604772257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1387058933975645069848171 2080588400963467604772257)
    ·
      refine ⟨1560441300722600703579193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2080588400963467604772257 1560441300722600703579193)
      ·
        refine ⟨1170330975541950527684395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1560441300722600703579193 1170330975541950527684395)
        ·
          refine ⟨1755496463312925791526593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1170330975541950527684395 1755496463312925791526593)
          ·
            refine ⟨1316622347484694343644945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1755496463312925791526593 1316622347484694343644945)
            ·
              refine ⟨987466760613520757733709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1316622347484694343644945 987466760613520757733709)
              ·
                refine ⟨370300035230070284150141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 987466760613520757733709 370300035230070284150141)
                ·
                  refine ⟨138862513211276356556303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 370300035230070284150141 138862513211276356556303)
                  ·
                    rfl

theorem cell20_304238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 3, 3].length) (baseStart_304238 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_304238 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_304238 prefixEnd_304238 := by exact prefixLift 304238
  have htrace : WordTrace (prefixWord ++ tailWord_304238) baseStart_304238 baseEnd_304238 := by
    simpa [prefixWord, tailWord_304238, baseEnd_304238] using wordTrace_append hprefix tailTrace_304238
  have hstable : (prefixWord ++ tailWord_304238).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304238).length < 2 ^ (prefixWord ++ tailWord_304238).sum := by decide
  have hdescent : baseEnd_304238 < baseStart_304238 := by decide
  rcases family_descends (prefixWord ++ tailWord_304238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304252 : List Nat := [2, 2, 2, 1, 1, 3, 5, 4]
def baseStart_304252 : Nat := 118140960795 + 304252 * 2 ^ 59
def prefixEnd_304252 : Nat := 4983230072969 + 3 ^ 40 * 304252 * 2
def baseEnd_304252 : Nat := 46289634397584843363193

theorem tailTrace_304252 : CollatzResearch.WordTrace tailWord_304252 prefixEnd_304252 46289634397584843363193 := by
  unfold tailWord_304252
  simp only [CollatzResearch.WordTrace]
  refine ⟨5548491046877220474897505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7397988062502960633196673 5548491046877220474897505)
  ·
    refine ⟨4161368285157915356173129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5548491046877220474897505 4161368285157915356173129)
    ·
      refine ⟨3121026213868436517129847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4161368285157915356173129 3121026213868436517129847)
      ·
        refine ⟨4681539320802654775694771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3121026213868436517129847 4681539320802654775694771)
        ·
          refine ⟨7022308981203982163542157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4681539320802654775694771 7022308981203982163542157)
          ·
            refine ⟨2633365867951493311328309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7022308981203982163542157 2633365867951493311328309)
            ·
              refine ⟨246878050120452497937029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2633365867951493311328309 246878050120452497937029)
              ·
                refine ⟨46289634397584843363193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 246878050120452497937029 46289634397584843363193)
                ·
                  rfl

theorem cell20_304252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 5, 4].length) (baseStart_304252 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_304252 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_304252 prefixEnd_304252 := by exact prefixLift 304252
  have htrace : WordTrace (prefixWord ++ tailWord_304252) baseStart_304252 baseEnd_304252 := by
    simpa [prefixWord, tailWord_304252, baseEnd_304252] using wordTrace_append hprefix tailTrace_304252
  have hstable : (prefixWord ++ tailWord_304252).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304252).length < 2 ^ (prefixWord ++ tailWord_304252).sum := by decide
  have hdescent : baseEnd_304252 < baseStart_304252 := by decide
  rcases family_descends (prefixWord ++ tailWord_304252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304266 : List Nat := [3, 1, 2, 3, 1, 1, 1, 2, 6]
def baseStart_304266 : Nat := 118140960795 + 304266 * 2 ^ 59
def prefixEnd_304266 : Nat := 4983230072969 + 3 ^ 40 * 304266 * 2
def baseEnd_304266 : Nat := 138875293174232703622855

theorem tailTrace_304266 : CollatzResearch.WordTrace tailWord_304266 prefixEnd_304266 138875293174232703622855 := by
  unfold tailWord_304266
  simp only [CollatzResearch.WordTrace]
  refine ⟨2774373178925930335201163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7398328477135814227203101 2774373178925930335201163)
  ·
    refine ⟨4161559768388895502801745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2774373178925930335201163 4161559768388895502801745)
    ·
      refine ⟨3121169826291671627101309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4161559768388895502801745 3121169826291671627101309)
      ·
        refine ⟨1170438684859376860162991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3121169826291671627101309 1170438684859376860162991)
        ·
          refine ⟨1755658027289065290244487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1170438684859376860162991 1755658027289065290244487)
          ·
            refine ⟨2633487040933597935366731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1755658027289065290244487 2633487040933597935366731)
            ·
              refine ⟨3950230561400396903050097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2633487040933597935366731 3950230561400396903050097)
              ·
                refine ⟨2962672921050297677287573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3950230561400396903050097 2962672921050297677287573)
                ·
                  refine ⟨138875293174232703622855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2962672921050297677287573 138875293174232703622855)
                  ·
                    rfl

theorem cell20_304266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 2, 6].length) (baseStart_304266 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_304266 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_304266 prefixEnd_304266 := by exact prefixLift 304266
  have htrace : WordTrace (prefixWord ++ tailWord_304266) baseStart_304266 baseEnd_304266 := by
    simpa [prefixWord, tailWord_304266, baseEnd_304266] using wordTrace_append hprefix tailTrace_304266
  have hstable : (prefixWord ++ tailWord_304266).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304266).length < 2 ^ (prefixWord ++ tailWord_304266).sum := by decide
  have hdescent : baseEnd_304266 < baseStart_304266 := by decide
  rcases family_descends (prefixWord ++ tailWord_304266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304311 : List Nat := [1, 1, 3, 1, 4, 1, 3, 6]
def baseStart_304311 : Nat := 118140960795 + 304311 * 2 ^ 59
def prefixEnd_304311 : Nat := 4983230072969 + 3 ^ 40 * 304311 * 2
def baseEnd_304311 : Nat := 46298610800137515707557

theorem tailTrace_304311 : CollatzResearch.WordTrace tailWord_304311 prefixEnd_304311 46298610800137515707557 := by
  unfold tailWord_304311
  simp only [CollatzResearch.WordTrace]
  refine ⟨11099134000540694026192787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7399422667027129350795191 11099134000540694026192787)
  ·
    refine ⟨16648701000811041039289181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11099134000540694026192787 16648701000811041039289181)
    ·
      refine ⟨6243262875304140389733443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16648701000811041039289181 6243262875304140389733443)
      ·
        refine ⟨9364894312956210584600165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6243262875304140389733443 9364894312956210584600165)
        ·
          refine ⟨1755917683679289484612531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9364894312956210584600165 1755917683679289484612531)
          ·
            refine ⟨2633876525518934226918797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1755917683679289484612531 2633876525518934226918797)
            ·
              refine ⟨987703697069600335094549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2633876525518934226918797 987703697069600335094549)
              ·
                refine ⟨46298610800137515707557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 987703697069600335094549 46298610800137515707557)
                ·
                  rfl

theorem cell20_304311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 6].length) (baseStart_304311 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_304311 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_304311 prefixEnd_304311 := by exact prefixLift 304311
  have htrace : WordTrace (prefixWord ++ tailWord_304311) baseStart_304311 baseEnd_304311 := by
    simpa [prefixWord, tailWord_304311, baseEnd_304311] using wordTrace_append hprefix tailTrace_304311
  have hstable : (prefixWord ++ tailWord_304311).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304311).length < 2 ^ (prefixWord ++ tailWord_304311).sum := by decide
  have hdescent : baseEnd_304311 < baseStart_304311 := by decide
  rcases family_descends (prefixWord ++ tailWord_304311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304352 : List Nat := [2, 1, 1, 3, 1, 4, 4, 1, 3]
def baseStart_304352 : Nat := 118140960795 + 304352 * 2 ^ 59
def prefixEnd_304352 : Nat := 4983230072969 + 3 ^ 40 * 304352 * 2
def baseEnd_304352 : Nat := 138914545917598626755837

theorem tailTrace_304352 : CollatzResearch.WordTrace tailWord_304352 prefixEnd_304352 138914545917598626755837 := by
  unfold tailWord_304352
  simp only [CollatzResearch.WordTrace]
  refine ⟨5550314696696079014217655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7400419595594772018956873 5550314696696079014217655)
  ·
    refine ⟨8325472045044118521326483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5550314696696079014217655 8325472045044118521326483)
    ·
      refine ⟨12488208067566177781989725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8325472045044118521326483 12488208067566177781989725)
      ·
        refine ⟨4683078025337316668246147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12488208067566177781989725 4683078025337316668246147)
        ·
          refine ⟨7024617038005975002369221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4683078025337316668246147 7024617038005975002369221)
          ·
            refine ⟨1317115694626120312944229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7024617038005975002369221 1317115694626120312944229)
            ·
              refine ⟨246959192742397558677043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1317115694626120312944229 246959192742397558677043)
              ·
                refine ⟨370438789113596338015565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 246959192742397558677043 370438789113596338015565)
                ·
                  refine ⟨138914545917598626755837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 370438789113596338015565 138914545917598626755837)
                  ·
                    rfl

theorem cell20_304352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 4, 1, 3].length) (baseStart_304352 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_304352 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_304352 prefixEnd_304352 := by exact prefixLift 304352
  have htrace : WordTrace (prefixWord ++ tailWord_304352) baseStart_304352 baseEnd_304352 := by
    simpa [prefixWord, tailWord_304352, baseEnd_304352] using wordTrace_append hprefix tailTrace_304352
  have hstable : (prefixWord ++ tailWord_304352).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304352).length < 2 ^ (prefixWord ++ tailWord_304352).sum := by decide
  have hdescent : baseEnd_304352 < baseStart_304352 := by decide
  rcases family_descends (prefixWord ++ tailWord_304352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304432 : List Nat := [2, 1, 1, 1, 2, 2, 4, 2, 5]
def baseStart_304432 : Nat := 118140960795 + 304432 * 2 ^ 59
def prefixEnd_304432 : Nat := 4983230072969 + 3 ^ 40 * 304432 * 2
def baseEnd_304432 : Nat := 138951060097473904088843

theorem tailTrace_304432 : CollatzResearch.WordTrace tailWord_304432 prefixEnd_304432 138951060097473904088843 := by
  unfold tailWord_304432
  simp only [CollatzResearch.WordTrace]
  refine ⟨5551773616551165845673775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7402364822068221127565033 5551773616551165845673775)
  ·
    refine ⟨8327660424826748768510663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5551773616551165845673775 8327660424826748768510663)
    ·
      refine ⟨12491490637240123152765995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8327660424826748768510663 12491490637240123152765995)
      ·
        refine ⟨18737235955860184729148993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12491490637240123152765995 18737235955860184729148993)
        ·
          refine ⟨14052926966895138546861745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18737235955860184729148993 14052926966895138546861745)
          ·
            refine ⟨10539695225171353910146309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14052926966895138546861745 10539695225171353910146309)
            ·
              refine ⟨1976192854719628858152433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10539695225171353910146309 1976192854719628858152433)
              ·
                refine ⟨1482144641039721643614325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1976192854719628858152433 1482144641039721643614325)
                ·
                  refine ⟨138951060097473904088843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1482144641039721643614325 138951060097473904088843)
                  ·
                    rfl

theorem cell20_304432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 2, 5].length) (baseStart_304432 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_304432 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_304432 prefixEnd_304432 := by exact prefixLift 304432
  have htrace : WordTrace (prefixWord ++ tailWord_304432) baseStart_304432 baseEnd_304432 := by
    simpa [prefixWord, tailWord_304432, baseEnd_304432] using wordTrace_append hprefix tailTrace_304432
  have hstable : (prefixWord ++ tailWord_304432).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304432).length < 2 ^ (prefixWord ++ tailWord_304432).sum := by decide
  have hdescent : baseEnd_304432 < baseStart_304432 := by decide
  rcases family_descends (prefixWord ++ tailWord_304432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304435 : List Nat := [1, 1, 1, 2, 5, 2, 1, 5, 2]
def baseStart_304435 : Nat := 118140960795 + 304435 * 2 ^ 59
def prefixEnd_304435 : Nat := 4983230072969 + 3 ^ 40 * 304435 * 2
def baseEnd_304435 : Nat := 138952429379219226988831

theorem tailTrace_304435 : CollatzResearch.WordTrace tailWord_304435 prefixEnd_304435 138952429379219226988831 := by
  unfold tailWord_304435
  simp only [CollatzResearch.WordTrace]
  refine ⟨11103656652091463203706759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7402437768060975469137839 11103656652091463203706759)
  ·
    refine ⟨16655484978137194805560139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11103656652091463203706759 16655484978137194805560139)
    ·
      refine ⟨24983227467205792208340209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16655484978137194805560139 24983227467205792208340209)
      ·
        refine ⟨18737420600404344156255157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24983227467205792208340209 18737420600404344156255157)
        ·
          refine ⟨1756633181287907264648921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18737420600404344156255157 1756633181287907264648921)
          ·
            refine ⟨1317474885965930448486691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1756633181287907264648921 1317474885965930448486691)
            ·
              refine ⟨1976212328948895672730037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1317474885965930448486691 1976212328948895672730037)
              ·
                refine ⟨185269905838958969318441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1976212328948895672730037 185269905838958969318441)
                ·
                  refine ⟨138952429379219226988831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 185269905838958969318441 138952429379219226988831)
                  ·
                    rfl

theorem cell20_304435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 5, 2].length) (baseStart_304435 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_304435 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_304435 prefixEnd_304435 := by exact prefixLift 304435
  have htrace : WordTrace (prefixWord ++ tailWord_304435) baseStart_304435 baseEnd_304435 := by
    simpa [prefixWord, tailWord_304435, baseEnd_304435] using wordTrace_append hprefix tailTrace_304435
  have hstable : (prefixWord ++ tailWord_304435).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304435).length < 2 ^ (prefixWord ++ tailWord_304435).sum := by decide
  have hdescent : baseEnd_304435 < baseStart_304435 := by decide
  rcases family_descends (prefixWord ++ tailWord_304435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304452 : List Nat := [2, 3, 4, 1, 1, 2, 2, 1, 4]
def baseStart_304452 : Nat := 118140960795 + 304452 * 2 ^ 59
def prefixEnd_304452 : Nat := 4983230072969 + 3 ^ 40 * 304452 * 2
def baseEnd_304452 : Nat := 138960188642442723422095

theorem tailTrace_304452 : CollatzResearch.WordTrace tailWord_304452 prefixEnd_304452 138960188642442723422095 := by
  unfold tailWord_304452
  simp only [CollatzResearch.WordTrace]
  refine ⟨5552138346514937553537805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7402851128686583404717073 5552138346514937553537805)
  ·
    refine ⟨2082051879943101582576677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5552138346514937553537805 2082051879943101582576677)
    ·
      refine ⟨390384727489331546733127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2082051879943101582576677 390384727489331546733127)
      ·
        refine ⟨585577091233997320099691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 390384727489331546733127 585577091233997320099691)
        ·
          refine ⟨878365636850995980149537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 585577091233997320099691 878365636850995980149537)
          ·
            refine ⟨658774227638246985112153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 878365636850995980149537 658774227638246985112153)
            ·
              refine ⟨494080670728685238834115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 658774227638246985112153 494080670728685238834115)
              ·
                refine ⟨741121006093027858251173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 494080670728685238834115 741121006093027858251173)
                ·
                  refine ⟨138960188642442723422095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 741121006093027858251173 138960188642442723422095)
                  ·
                    rfl

theorem cell20_304452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 2, 1, 4].length) (baseStart_304452 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_304452 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_304452 prefixEnd_304452 := by exact prefixLift 304452
  have htrace : WordTrace (prefixWord ++ tailWord_304452) baseStart_304452 baseEnd_304452 := by
    simpa [prefixWord, tailWord_304452, baseEnd_304452] using wordTrace_append hprefix tailTrace_304452
  have hstable : (prefixWord ++ tailWord_304452).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304452).length < 2 ^ (prefixWord ++ tailWord_304452).sum := by decide
  have hdescent : baseEnd_304452 < baseStart_304452 := by decide
  rcases family_descends (prefixWord ++ tailWord_304452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304480 : List Nat := [2, 1, 1, 3, 4, 1, 4, 4]
def baseStart_304480 : Nat := 118140960795 + 304480 * 2 ^ 59
def prefixEnd_304480 : Nat := 4983230072969 + 3 ^ 40 * 304480 * 2
def baseEnd_304480 : Nat := 46324322868466356829549

theorem tailTrace_304480 : CollatzResearch.WordTrace tailWord_304480 prefixEnd_304480 46324322868466356829549 := by
  unfold tailWord_304480
  simp only [CollatzResearch.WordTrace]
  refine ⟨5552648968464217944547447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7403531957952290592729929 5552648968464217944547447)
  ·
    refine ⟨8328973452696326916821171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5552648968464217944547447 8328973452696326916821171)
    ·
      refine ⟨12493460179044490375231757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8328973452696326916821171 12493460179044490375231757)
      ·
        refine ⟨4685047567141683890711909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12493460179044490375231757 4685047567141683890711909)
        ·
          refine ⟨878446418839065729508483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4685047567141683890711909 878446418839065729508483)
          ·
            refine ⟨1317669628258598594262725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 878446418839065729508483 1317669628258598594262725)
            ·
              refine ⟨247063055298487236424261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1317669628258598594262725 247063055298487236424261)
              ·
                refine ⟨46324322868466356829549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 247063055298487236424261 46324322868466356829549)
                ·
                  rfl

theorem cell20_304480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 4, 4].length) (baseStart_304480 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_304480 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_304480 prefixEnd_304480 := by exact prefixLift 304480
  have htrace : WordTrace (prefixWord ++ tailWord_304480) baseStart_304480 baseEnd_304480 := by
    simpa [prefixWord, tailWord_304480, baseEnd_304480] using wordTrace_append hprefix tailTrace_304480
  have hstable : (prefixWord ++ tailWord_304480).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304480).length < 2 ^ (prefixWord ++ tailWord_304480).sum := by decide
  have hdescent : baseEnd_304480 < baseStart_304480 := by decide
  rcases family_descends (prefixWord ++ tailWord_304480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304508 : List Nat := [2, 2, 2, 1, 1, 1, 3, 3, 5]
def baseStart_304508 : Nat := 118140960795 + 304508 * 2 ^ 59
def prefixEnd_304508 : Nat := 4983230072969 + 3 ^ 40 * 304508 * 2
def baseEnd_304508 : Nat := 138985748568355417555199

theorem tailTrace_304508 : CollatzResearch.WordTrace tailWord_304508 prefixEnd_304508 138985748568355417555199 := by
  unfold tailWord_304508
  simp only [CollatzResearch.WordTrace]
  refine ⟨5553159590413498335557089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7404212787217997780742785 5553159590413498335557089)
  ·
    refine ⟨4164869692810123751667817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5553159590413498335557089 4164869692810123751667817)
    ·
      refine ⟨3123652269607592813750863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4164869692810123751667817 3123652269607592813750863)
      ·
        refine ⟨4685478404411389220626295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3123652269607592813750863 4685478404411389220626295)
        ·
          refine ⟨7028217606617083830939443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4685478404411389220626295 7028217606617083830939443)
          ·
            refine ⟨10542326409925625746409165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7028217606617083830939443 10542326409925625746409165)
            ·
              refine ⟨3953372403722109654903437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10542326409925625746409165 3953372403722109654903437)
              ·
                refine ⟨1482514651395791120588789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3953372403722109654903437 1482514651395791120588789)
                ·
                  refine ⟨138985748568355417555199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1482514651395791120588789 138985748568355417555199)
                  ·
                    rfl

theorem cell20_304508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 3, 5].length) (baseStart_304508 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_304508 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_304508 prefixEnd_304508 := by exact prefixLift 304508
  have htrace : WordTrace (prefixWord ++ tailWord_304508) baseStart_304508 baseEnd_304508 := by
    simpa [prefixWord, tailWord_304508, baseEnd_304508] using wordTrace_append hprefix tailTrace_304508
  have hstable : (prefixWord ++ tailWord_304508).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304508).length < 2 ^ (prefixWord ++ tailWord_304508).sum := by decide
  have hdescent : baseEnd_304508 < baseStart_304508 := by decide
  rcases family_descends (prefixWord ++ tailWord_304508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304521 : List Nat := [1, 2, 1, 1, 7, 2, 2, 1, 3]
def baseStart_304521 : Nat := 118140960795 + 304521 * 2 ^ 59
def prefixEnd_304521 : Nat := 4983230072969 + 3 ^ 40 * 304521 * 2
def baseEnd_304521 : Nat := 138991682122585150121813

theorem tailTrace_304521 : CollatzResearch.WordTrace tailWord_304521 prefixEnd_304521 138991682122585150121813 := by
  unfold tailWord_304521
  simp only [CollatzResearch.WordTrace]
  refine ⟨11106793329779899891337417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7404528886519933260891611 11106793329779899891337417)
  ·
    refine ⟨8330094997334924918503063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11106793329779899891337417 8330094997334924918503063)
    ·
      refine ⟨12495142496002387377754595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8330094997334924918503063 12495142496002387377754595)
      ·
        refine ⟨18742713744003581066631893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12495142496002387377754595 18742713744003581066631893)
        ·
          refine ⟨439282353375083931249185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 18742713744003581066631893 439282353375083931249185)
          ·
            refine ⟨329461765031312948436889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 439282353375083931249185 329461765031312948436889)
            ·
              refine ⟨247096323773484711327667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 329461765031312948436889 247096323773484711327667)
              ·
                refine ⟨370644485660227066991501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 247096323773484711327667 370644485660227066991501)
                ·
                  refine ⟨138991682122585150121813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 370644485660227066991501 138991682122585150121813)
                  ·
                    rfl

theorem cell20_304521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 2, 1, 3].length) (baseStart_304521 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_304521 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_304521 prefixEnd_304521 := by exact prefixLift 304521
  have htrace : WordTrace (prefixWord ++ tailWord_304521) baseStart_304521 baseEnd_304521 := by
    simpa [prefixWord, tailWord_304521, baseEnd_304521] using wordTrace_append hprefix tailTrace_304521
  have hstable : (prefixWord ++ tailWord_304521).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304521).length < 2 ^ (prefixWord ++ tailWord_304521).sum := by decide
  have hdescent : baseEnd_304521 < baseStart_304521 := by decide
  rcases family_descends (prefixWord ++ tailWord_304521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304580 : List Nat := [2, 3, 3, 2, 1, 1, 2, 3, 3]
def baseStart_304580 : Nat := 118140960795 + 304580 * 2 ^ 59
def prefixEnd_304580 : Nat := 4983230072969 + 3 ^ 40 * 304580 * 2
def baseEnd_304580 : Nat := 139018611330243167154905

theorem tailTrace_304580 : CollatzResearch.WordTrace tailWord_304580 prefixEnd_304580 139018611330243167154905 := by
  unfold tailWord_304580
  simp only [CollatzResearch.WordTrace]
  refine ⟨5554472618283076483867597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7405963491044101978490129 5554472618283076483867597)
  ·
    refine ⟨2082927231856153681450349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5554472618283076483867597 2082927231856153681450349)
    ·
      refine ⟨781097711946057630543881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2082927231856153681450349 781097711946057630543881)
      ·
        refine ⟨585823283959543222907911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 781097711946057630543881 585823283959543222907911)
        ·
          refine ⟨878734925939314834361867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 585823283959543222907911 878734925939314834361867)
          ·
            refine ⟨1318102388908972251542801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 878734925939314834361867 1318102388908972251542801)
            ·
              refine ⟨988576791681729188657101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1318102388908972251542801 988576791681729188657101)
              ·
                refine ⟨370716296880648445746413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 988576791681729188657101 370716296880648445746413)
                ·
                  refine ⟨139018611330243167154905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 370716296880648445746413 139018611330243167154905)
                  ·
                    rfl

theorem cell20_304580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 3, 3].length) (baseStart_304580 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_304580 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_304580 prefixEnd_304580 := by exact prefixLift 304580
  have htrace : WordTrace (prefixWord ++ tailWord_304580) baseStart_304580 baseEnd_304580 := by
    simpa [prefixWord, tailWord_304580, baseEnd_304580] using wordTrace_append hprefix tailTrace_304580
  have hstable : (prefixWord ++ tailWord_304580).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304580).length < 2 ^ (prefixWord ++ tailWord_304580).sum := by decide
  have hdescent : baseEnd_304580 < baseStart_304580 := by decide
  rcases family_descends (prefixWord ++ tailWord_304580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304591 : List Nat := [1, 1, 2, 1, 1, 4, 3, 1, 6]
def baseStart_304591 : Nat := 118140960795 + 304591 * 2 ^ 59
def prefixEnd_304591 : Nat := 4983230072969 + 3 ^ 40 * 304591 * 2
def baseEnd_304591 : Nat := 139023632029976017788193

theorem tailTrace_304591 : CollatzResearch.WordTrace tailWord_304591 prefixEnd_304591 139023632029976017788193 := by
  unfold tailWord_304591
  simp only [CollatzResearch.WordTrace]
  refine ⟨11109346439526301846385627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7406230959684201230923751 11109346439526301846385627)
  ·
    refine ⟨16664019659289452769578441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11109346439526301846385627 16664019659289452769578441)
    ·
      refine ⟨12498014744467089577183831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16664019659289452769578441 12498014744467089577183831)
      ·
        refine ⟨18747022116700634365775747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12498014744467089577183831 18747022116700634365775747)
        ·
          refine ⟨28120533175050951548663621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18747022116700634365775747 28120533175050951548663621)
          ·
            refine ⟨5272599970322053415374429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28120533175050951548663621 5272599970322053415374429)
            ·
              refine ⟨1977224988870770030765411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5272599970322053415374429 1977224988870770030765411)
              ·
                refine ⟨2965837483306155046148117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1977224988870770030765411 2965837483306155046148117)
                ·
                  refine ⟨139023632029976017788193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2965837483306155046148117 139023632029976017788193)
                  ·
                    rfl

theorem cell20_304591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 1, 6].length) (baseStart_304591 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_304591 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_304591 prefixEnd_304591 := by exact prefixLift 304591
  have htrace : WordTrace (prefixWord ++ tailWord_304591) baseStart_304591 baseEnd_304591 := by
    simpa [prefixWord, tailWord_304591, baseEnd_304591] using wordTrace_append hprefix tailTrace_304591
  have hstable : (prefixWord ++ tailWord_304591).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304591).length < 2 ^ (prefixWord ++ tailWord_304591).sum := by decide
  have hdescent : baseEnd_304591 < baseStart_304591 := by decide
  rcases family_descends (prefixWord ++ tailWord_304591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304615 : List Nat := [1, 1, 5, 2, 1, 3, 7]
def baseStart_304615 : Nat := 118140960795 + 304615 * 2 ^ 59
def prefixEnd_304615 : Nat := 4983230072969 + 3 ^ 40 * 304615 * 2
def baseEnd_304615 : Nat := 15448287364882066776455

theorem tailTrace_304615 : CollatzResearch.WordTrace tailWord_304615 prefixEnd_304615 15448287364882066776455 := by
  unfold tailWord_304615
  simp only [CollatzResearch.WordTrace]
  refine ⟨11110221791439353945259299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7406814527626235963506199 11110221791439353945259299)
  ·
    refine ⟨16665332687159030917888949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11110221791439353945259299 16665332687159030917888949)
    ·
      refine ⟨1562374939421159148552089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16665332687159030917888949 1562374939421159148552089)
      ·
        refine ⟨1171781204565869361414067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1562374939421159148552089 1171781204565869361414067)
        ·
          refine ⟨1757671806848804042121101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1171781204565869361414067 1757671806848804042121101)
          ·
            refine ⟨659126927568301515795413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1757671806848804042121101 659126927568301515795413)
            ·
              refine ⟨15448287364882066776455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 659126927568301515795413 15448287364882066776455)
              ·
                rfl

theorem cell20_304615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 7].length) (baseStart_304615 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_304615 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_304615 prefixEnd_304615 := by exact prefixLift 304615
  have htrace : WordTrace (prefixWord ++ tailWord_304615) baseStart_304615 baseEnd_304615 := by
    simpa [prefixWord, tailWord_304615, baseEnd_304615] using wordTrace_append hprefix tailTrace_304615
  have hstable : (prefixWord ++ tailWord_304615).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304615).length < 2 ^ (prefixWord ++ tailWord_304615).sum := by decide
  have hdescent : baseEnd_304615 < baseStart_304615 := by decide
  rcases family_descends (prefixWord ++ tailWord_304615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304625 : List Nat := [1, 2, 2, 2, 3, 2, 2, 4, 2]
def baseStart_304625 : Nat := 118140960795 + 304625 * 2 ^ 59
def prefixEnd_304625 : Nat := 4983230072969 + 3 ^ 40 * 304625 * 2
def baseEnd_304625 : Nat := 139039150556423010654721

theorem tailTrace_304625 : CollatzResearch.WordTrace tailWord_304625 prefixEnd_304625 139039150556423010654721 := by
  unfold tailWord_304625
  simp only [CollatzResearch.WordTrace]
  refine ⟨11110586521403125653123329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7407057680935417102082219 11110586521403125653123329)
  ·
    refine ⟨8332939891052344239842497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11110586521403125653123329 8332939891052344239842497)
    ·
      refine ⟨6249704918289258179881873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8332939891052344239842497 6249704918289258179881873)
      ·
        refine ⟨4687278688716943634911405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6249704918289258179881873 4687278688716943634911405)
        ·
          refine ⟨1757729508268853863091777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4687278688716943634911405 1757729508268853863091777)
          ·
            refine ⟨1318297131201640397318833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1757729508268853863091777 1318297131201640397318833)
            ·
              refine ⟨988722848401230297989125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1318297131201640397318833 988722848401230297989125)
              ·
                refine ⟨185385534075230680872961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 988722848401230297989125 185385534075230680872961)
                ·
                  refine ⟨139039150556423010654721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 185385534075230680872961 139039150556423010654721)
                  ·
                    rfl

theorem cell20_304625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 4, 2].length) (baseStart_304625 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_304625 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_304625 prefixEnd_304625 := by exact prefixLift 304625
  have htrace : WordTrace (prefixWord ++ tailWord_304625) baseStart_304625 baseEnd_304625 := by
    simpa [prefixWord, tailWord_304625, baseEnd_304625] using wordTrace_append hprefix tailTrace_304625
  have hstable : (prefixWord ++ tailWord_304625).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304625).length < 2 ^ (prefixWord ++ tailWord_304625).sum := by decide
  have hdescent : baseEnd_304625 < baseStart_304625 := by decide
  rcases family_descends (prefixWord ++ tailWord_304625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304680 : List Nat := [2, 1, 5, 2, 2, 2, 1, 1, 4]
def baseStart_304680 : Nat := 118140960795 + 304680 * 2 ^ 59
def prefixEnd_304680 : Nat := 4983230072969 + 3 ^ 40 * 304680 * 2
def baseEnd_304680 : Nat := 139064254055087263821163

theorem tailTrace_304680 : CollatzResearch.WordTrace tailWord_304680 prefixEnd_304680 139064254055087263821163 := by
  unfold tailWord_304680
  simp only [CollatzResearch.WordTrace]
  refine ⟨5556296268101935023187747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7408395024135913364250329 5556296268101935023187747)
  ·
    refine ⟨8334444402152902534781621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5556296268101935023187747 8334444402152902534781621)
    ·
      refine ⟨781354162701834612635777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8334444402152902534781621 781354162701834612635777)
      ·
        refine ⟨586015622026375959476833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 781354162701834612635777 586015622026375959476833)
        ·
          refine ⟨439511716519781969607625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 586015622026375959476833 439511716519781969607625)
          ·
            refine ⟨329633787389836477205719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 439511716519781969607625 329633787389836477205719)
            ·
              refine ⟨494450681084754715808579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 329633787389836477205719 494450681084754715808579)
              ·
                refine ⟨741676021627132073712869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 494450681084754715808579 741676021627132073712869)
                ·
                  refine ⟨139064254055087263821163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 741676021627132073712869 139064254055087263821163)
                  ·
                    rfl

theorem cell20_304680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 1, 1, 4].length) (baseStart_304680 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_304680 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_304680 prefixEnd_304680 := by exact prefixLift 304680
  have htrace : WordTrace (prefixWord ++ tailWord_304680) baseStart_304680 baseEnd_304680 := by
    simpa [prefixWord, tailWord_304680, baseEnd_304680] using wordTrace_append hprefix tailTrace_304680
  have hstable : (prefixWord ++ tailWord_304680).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304680).length < 2 ^ (prefixWord ++ tailWord_304680).sum := by decide
  have hdescent : baseEnd_304680 < baseStart_304680 := by decide
  rcases family_descends (prefixWord ++ tailWord_304680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304691 : List Nat := [1, 1, 1, 2, 4, 4, 2, 5]
def baseStart_304691 : Nat := 118140960795 + 304691 * 2 ^ 59
def prefixEnd_304691 : Nat := 4983230072969 + 3 ^ 40 * 304691 * 2
def baseEnd_304691 : Nat := 46356424918273371484817

theorem tailTrace_304691 : CollatzResearch.WordTrace tailWord_304691 prefixEnd_304691 46356424918273371484817 := by
  unfold tailWord_304691
  simp only [CollatzResearch.WordTrace]
  refine ⟨11112993739164018925025927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7408662492776012616683951 11112993739164018925025927)
  ·
    refine ⟨16669490608746028387538891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11112993739164018925025927 16669490608746028387538891)
    ·
      refine ⟨25004235913119042581308337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16669490608746028387538891 25004235913119042581308337)
      ·
        refine ⟨18753176934839281935981253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25004235913119042581308337 18753176934839281935981253)
        ·
          refine ⟨3516220675282365362996485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18753176934839281935981253 3516220675282365362996485)
          ·
            refine ⟨659291376615443505561841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3516220675282365362996485 659291376615443505561841)
            ·
              refine ⟨494468532461582629171381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 659291376615443505561841 494468532461582629171381)
              ·
                refine ⟨46356424918273371484817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 494468532461582629171381 46356424918273371484817)
                ·
                  rfl

theorem cell20_304691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 2, 5].length) (baseStart_304691 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_304691 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_304691 prefixEnd_304691 := by exact prefixLift 304691
  have htrace : WordTrace (prefixWord ++ tailWord_304691) baseStart_304691 baseEnd_304691 := by
    simpa [prefixWord, tailWord_304691, baseEnd_304691] using wordTrace_append hprefix tailTrace_304691
  have hstable : (prefixWord ++ tailWord_304691).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304691).length < 2 ^ (prefixWord ++ tailWord_304691).sum := by decide
  have hdescent : baseEnd_304691 < baseStart_304691 := by decide
  rcases family_descends (prefixWord ++ tailWord_304691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304732 : List Nat := [2, 2, 4, 1, 2, 2, 2, 2, 3]
def baseStart_304732 : Nat := 118140960795 + 304732 * 2 ^ 59
def prefixEnd_304732 : Nat := 4983230072969 + 3 ^ 40 * 304732 * 2
def baseEnd_304732 : Nat := 139087988272006194087617

theorem tailTrace_304732 : CollatzResearch.WordTrace tailWord_304732 prefixEnd_304732 139087988272006194087617 := by
  unfold tailWord_304732
  simp only [CollatzResearch.WordTrace]
  refine ⟨5557244566007741463634225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7409659421343655284845633 5557244566007741463634225)
  ·
    refine ⟨4167933424505806097725669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5557244566007741463634225 4167933424505806097725669)
    ·
      refine ⟨781487517094838643323563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4167933424505806097725669 781487517094838643323563)
      ·
        refine ⟨1172231275642257964985345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 781487517094838643323563 1172231275642257964985345)
        ·
          refine ⟨879173456731693473739009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1172231275642257964985345 879173456731693473739009)
          ·
            refine ⟨659380092548770105304257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 879173456731693473739009 659380092548770105304257)
            ·
              refine ⟨494535069411577578978193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 659380092548770105304257 494535069411577578978193)
              ·
                refine ⟨370901302058683184233645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 494535069411577578978193 370901302058683184233645)
                ·
                  refine ⟨139087988272006194087617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 370901302058683184233645 139087988272006194087617)
                  ·
                    rfl

theorem cell20_304732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 2, 2, 3].length) (baseStart_304732 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_304732 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_304732 prefixEnd_304732 := by exact prefixLift 304732
  have htrace : WordTrace (prefixWord ++ tailWord_304732) baseStart_304732 baseEnd_304732 := by
    simpa [prefixWord, tailWord_304732, baseEnd_304732] using wordTrace_append hprefix tailTrace_304732
  have hstable : (prefixWord ++ tailWord_304732).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304732).length < 2 ^ (prefixWord ++ tailWord_304732).sum := by decide
  have hdescent : baseEnd_304732 < baseStart_304732 := by decide
  rcases family_descends (prefixWord ++ tailWord_304732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304739 : List Nat := [1, 1, 1, 5, 1, 4, 1, 4, 2]
def baseStart_304739 : Nat := 118140960795 + 304739 * 2 ^ 59
def prefixEnd_304739 : Nat := 4983230072969 + 3 ^ 40 * 304739 * 2
def baseEnd_304739 : Nat := 139091183262745280854255

theorem tailTrace_304739 : CollatzResearch.WordTrace tailWord_304739 prefixEnd_304739 139091183262745280854255 := by
  unfold tailWord_304739
  simp only [CollatzResearch.WordTrace]
  refine ⟨11114744442990123122773271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7409829628660082081848847 11114744442990123122773271)
  ·
    refine ⟨16672116664485184684159907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11114744442990123122773271 16672116664485184684159907)
    ·
      refine ⟨25008174996727777026239861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16672116664485184684159907 25008174996727777026239861)
      ·
        refine ⟨2344516405943229096209987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25008174996727777026239861 2344516405943229096209987)
        ·
          refine ⟨3516774608914843644314981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2344516405943229096209987 3516774608914843644314981)
          ·
            refine ⟨659395239171533183309059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3516774608914843644314981 659395239171533183309059)
            ·
              refine ⟨989092858757299774963589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 659395239171533183309059 989092858757299774963589)
              ·
                refine ⟨185454911016993707805673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 989092858757299774963589 185454911016993707805673)
                ·
                  refine ⟨139091183262745280854255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 185454911016993707805673 139091183262745280854255)
                  ·
                    rfl

theorem cell20_304739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 4, 2].length) (baseStart_304739 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_304739 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_304739 prefixEnd_304739 := by exact prefixLift 304739
  have htrace : WordTrace (prefixWord ++ tailWord_304739) baseStart_304739 baseEnd_304739 := by
    simpa [prefixWord, tailWord_304739, baseEnd_304739] using wordTrace_append hprefix tailTrace_304739
  have hstable : (prefixWord ++ tailWord_304739).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304739).length < 2 ^ (prefixWord ++ tailWord_304739).sum := by decide
  have hdescent : baseEnd_304739 < baseStart_304739 := by decide
  rcases family_descends (prefixWord ++ tailWord_304739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304746 : List Nat := [3, 1, 3, 2, 1, 4, 1, 5]
def baseStart_304746 : Nat := 118140960795 + 304746 * 2 ^ 59
def prefixEnd_304746 : Nat := 4983230072969 + 3 ^ 40 * 304746 * 2
def baseEnd_304746 : Nat := 46364792751161455873631

theorem tailTrace_304746 : CollatzResearch.WordTrace tailWord_304746 prefixEnd_304746 46364792751161455873631 := by
  unfold tailWord_304746
  simp only [CollatzResearch.WordTrace]
  refine ⟨2778749938491190829569523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7409999835976508878852061 2778749938491190829569523)
  ·
    refine ⟨4168124907736786244354285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2778749938491190829569523 4168124907736786244354285)
    ·
      refine ⟨1563046840401294841632857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4168124907736786244354285 1563046840401294841632857)
      ·
        refine ⟨1172285130300971131224643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1563046840401294841632857 1172285130300971131224643)
        ·
          refine ⟨1758427695451456696836965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1172285130300971131224643 1758427695451456696836965)
          ·
            refine ⟨329705192897148130656931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1758427695451456696836965 329705192897148130656931)
            ·
              refine ⟨494557789345722195985397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 329705192897148130656931 494557789345722195985397)
              ·
                refine ⟨46364792751161455873631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 494557789345722195985397 46364792751161455873631)
                ·
                  rfl

theorem cell20_304746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 1, 5].length) (baseStart_304746 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_304746 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_304746 prefixEnd_304746 := by exact prefixLift 304746
  have htrace : WordTrace (prefixWord ++ tailWord_304746) baseStart_304746 baseEnd_304746 := by
    simpa [prefixWord, tailWord_304746, baseEnd_304746] using wordTrace_append hprefix tailTrace_304746
  have hstable : (prefixWord ++ tailWord_304746).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304746).length < 2 ^ (prefixWord ++ tailWord_304746).sum := by decide
  have hdescent : baseEnd_304746 < baseStart_304746 := by decide
  rcases family_descends (prefixWord ++ tailWord_304746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304791 : List Nat := [1, 1, 3, 3, 2, 2, 3, 2, 3]
def baseStart_304791 : Nat := 118140960795 + 304791 * 2 ^ 59
def prefixEnd_304791 : Nat := 4983230072969 + 3 ^ 40 * 304791 * 2
def baseEnd_304791 : Nat := 139114917479664211120709

theorem tailTrace_304791 : CollatzResearch.WordTrace tailWord_304791 prefixEnd_304791 139114917479664211120709 := by
  unfold tailWord_304791
  simp only [CollatzResearch.WordTrace]
  refine ⟨11116641038801736003666227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7411094025867824002444151 11116641038801736003666227)
  ·
    refine ⟨16674961558202604005499341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11116641038801736003666227 16674961558202604005499341)
    ·
      refine ⟨6253110584325976502062253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16674961558202604005499341 6253110584325976502062253)
      ·
        refine ⟨2344916469122241188273345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6253110584325976502062253 2344916469122241188273345)
        ·
          refine ⟨1758687351841680891205009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2344916469122241188273345 1758687351841680891205009)
          ·
            refine ⟨1319015513881260668403757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1758687351841680891205009 1319015513881260668403757)
            ·
              refine ⟨494630817705472750651409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1319015513881260668403757 494630817705472750651409)
              ·
                refine ⟨370973113279104562988557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 494630817705472750651409 370973113279104562988557)
                ·
                  refine ⟨139114917479664211120709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 370973113279104562988557 139114917479664211120709)
                  ·
                    rfl

theorem cell20_304791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 3, 2, 3].length) (baseStart_304791 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_304791 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_304791 prefixEnd_304791 := by exact prefixLift 304791
  have htrace : WordTrace (prefixWord ++ tailWord_304791) baseStart_304791 baseEnd_304791 := by
    simpa [prefixWord, tailWord_304791, baseEnd_304791] using wordTrace_append hprefix tailTrace_304791
  have hstable : (prefixWord ++ tailWord_304791).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304791).length < 2 ^ (prefixWord ++ tailWord_304791).sum := by decide
  have hdescent : baseEnd_304791 < baseStart_304791 := by decide
  rcases family_descends (prefixWord ++ tailWord_304791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304819 : List Nat := [1, 1, 1, 2, 3, 3, 1, 4, 4]
def baseStart_304819 : Nat := 118140960795 + 304819 * 2 ^ 59
def prefixEnd_304819 : Nat := 4983230072969 + 3 ^ 40 * 304819 * 2
def baseEnd_304819 : Nat := 139127697442620558187261

theorem tailTrace_304819 : CollatzResearch.WordTrace tailWord_304819 prefixEnd_304819 139127697442620558187261 := by
  unfold tailWord_304819
  simp only [CollatzResearch.WordTrace]
  refine ⟨11117662282700296785685511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7411774855133531190457007 11117662282700296785685511)
  ·
    refine ⟨16676493424050445178528267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11117662282700296785685511 16676493424050445178528267)
    ·
      refine ⟨25014740136075667767792401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16676493424050445178528267 25014740136075667767792401)
      ·
        refine ⟨18761055102056750825844301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25014740136075667767792401 18761055102056750825844301)
        ·
          refine ⟨7035395663271281559691613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18761055102056750825844301 7035395663271281559691613)
          ·
            refine ⟨2638273373726730584884355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7035395663271281559691613 2638273373726730584884355)
            ·
              refine ⟨3957410060590095877326533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2638273373726730584884355 3957410060590095877326533)
              ·
                refine ⟨742014386360642976998725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3957410060590095877326533 742014386360642976998725)
                ·
                  refine ⟨139127697442620558187261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 742014386360642976998725 139127697442620558187261)
                  ·
                    rfl

theorem cell20_304819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 4, 4].length) (baseStart_304819 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_304819 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_304819 prefixEnd_304819 := by exact prefixLift 304819
  have htrace : WordTrace (prefixWord ++ tailWord_304819) baseStart_304819 baseEnd_304819 := by
    simpa [prefixWord, tailWord_304819, baseEnd_304819] using wordTrace_append hprefix tailTrace_304819
  have hstable : (prefixWord ++ tailWord_304819).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304819).length < 2 ^ (prefixWord ++ tailWord_304819).sum := by decide
  have hdescent : baseEnd_304819 < baseStart_304819 := by decide
  rcases family_descends (prefixWord ++ tailWord_304819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304864 : List Nat := [2, 1, 1, 3, 1, 2, 3, 7]
def baseStart_304864 : Nat := 118140960795 + 304864 * 2 ^ 59
def prefixEnd_304864 : Nat := 4983230072969 + 3 ^ 40 * 304864 * 2
def baseEnd_304864 : Nat := 46382745556266800562359

theorem tailTrace_304864 : CollatzResearch.WordTrace tailWord_304864 prefixEnd_304864 46382745556266800562359 := by
  unfold tailWord_304864
  simp only [CollatzResearch.WordTrace]
  refine ⟨5559651783768634735536823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7412869045024846314049097 5559651783768634735536823)
  ·
    refine ⟨8339477675652952103305235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5559651783768634735536823 8339477675652952103305235)
    ·
      refine ⟨12509216513479428154957853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8339477675652952103305235 12509216513479428154957853)
      ·
        refine ⟨4690956192554785558109195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12509216513479428154957853 4690956192554785558109195)
        ·
          refine ⟨7036434288832178337163793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4690956192554785558109195 7036434288832178337163793)
          ·
            refine ⟨5277325716624133752872845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7036434288832178337163793 5277325716624133752872845)
            ·
              refine ⟨1978997143734050157327317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5277325716624133752872845 1978997143734050157327317)
              ·
                refine ⟨46382745556266800562359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1978997143734050157327317 46382745556266800562359)
                ·
                  rfl

theorem cell20_304864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 7].length) (baseStart_304864 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_304864 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_304864 prefixEnd_304864 := by exact prefixLift 304864
  have htrace : WordTrace (prefixWord ++ tailWord_304864) baseStart_304864 baseEnd_304864 := by
    simpa [prefixWord, tailWord_304864, baseEnd_304864] using wordTrace_append hprefix tailTrace_304864
  have hstable : (prefixWord ++ tailWord_304864).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304864).length < 2 ^ (prefixWord ++ tailWord_304864).sum := by decide
  have hdescent : baseEnd_304864 < baseStart_304864 := by decide
  rcases family_descends (prefixWord ++ tailWord_304864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304919 : List Nat := [1, 1, 3, 4, 2, 1, 3, 5]
def baseStart_304919 : Nat := 118140960795 + 304919 * 2 ^ 59
def prefixEnd_304919 : Nat := 4983230072969 + 3 ^ 40 * 304919 * 2
def baseEnd_304919 : Nat := 46391113389154884951173

theorem tailTrace_304919 : CollatzResearch.WordTrace tailWord_304919 prefixEnd_304919 46391113389154884951173 := by
  unfold tailWord_304919
  simp only [CollatzResearch.WordTrace]
  refine ⟨11121309582338013864325811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7414206388225342576217207 11121309582338013864325811)
  ·
    refine ⟨16681964373507020796488717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11121309582338013864325811 16681964373507020796488717)
    ·
      refine ⟨6255736640065132798683269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16681964373507020796488717 6255736640065132798683269)
      ·
        refine ⟨1172950620012212399753113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6255736640065132798683269 1172950620012212399753113)
        ·
          refine ⟨879712965009159299814835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1172950620012212399753113 879712965009159299814835)
          ·
            refine ⟨1319569447513738949722253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 879712965009159299814835 1319569447513738949722253)
            ·
              refine ⟨494838542817652106145845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1319569447513738949722253 494838542817652106145845)
              ·
                refine ⟨46391113389154884951173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 494838542817652106145845 46391113389154884951173)
                ·
                  rfl

theorem cell20_304919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 3, 5].length) (baseStart_304919 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_304919 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_304919 prefixEnd_304919 := by exact prefixLift 304919
  have htrace : WordTrace (prefixWord ++ tailWord_304919) baseStart_304919 baseEnd_304919 := by
    simpa [prefixWord, tailWord_304919, baseEnd_304919] using wordTrace_append hprefix tailTrace_304919
  have hstable : (prefixWord ++ tailWord_304919).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304919).length < 2 ^ (prefixWord ++ tailWord_304919).sum := by decide
  have hdescent : baseEnd_304919 < baseStart_304919 := by decide
  rcases family_descends (prefixWord ++ tailWord_304919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304933 : List Nat := [1, 3, 1, 2, 3, 2, 1, 1, 6]
def baseStart_304933 : Nat := 118140960795 + 304933 * 2 ^ 59
def prefixEnd_304933 : Nat := 4983230072969 + 3 ^ 40 * 304933 * 2
def baseEnd_304933 : Nat := 139179730148942828386795

theorem tailTrace_304933 : CollatzResearch.WordTrace tailWord_304933 prefixEnd_304933 139179730148942828386795 := by
  unfold tailWord_304933
  simp only [CollatzResearch.WordTrace]
  refine ⟨11121820204287294255335453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7414546802858196170223635 11121820204287294255335453)
  ·
    refine ⟨4170682576607735345750795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11121820204287294255335453 4170682576607735345750795)
    ·
      refine ⟨6256023864911603018626193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4170682576607735345750795 6256023864911603018626193)
      ·
        refine ⟨4692017898683702263969645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6256023864911603018626193 4692017898683702263969645)
        ·
          refine ⟨1759506712006388348988617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4692017898683702263969645 1759506712006388348988617)
          ·
            refine ⟨1319630034004791261741463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1759506712006388348988617 1319630034004791261741463)
            ·
              refine ⟨1979445051007186892612195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1319630034004791261741463 1979445051007186892612195)
              ·
                refine ⟨2969167576510780338918293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1979445051007186892612195 2969167576510780338918293)
                ·
                  refine ⟨139179730148942828386795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2969167576510780338918293 139179730148942828386795)
                  ·
                    rfl

theorem cell20_304933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 1, 6].length) (baseStart_304933 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_304933 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_304933 prefixEnd_304933 := by exact prefixLift 304933
  have htrace : WordTrace (prefixWord ++ tailWord_304933) baseStart_304933 baseEnd_304933 := by
    simpa [prefixWord, tailWord_304933, baseEnd_304933] using wordTrace_append hprefix tailTrace_304933
  have hstable : (prefixWord ++ tailWord_304933).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304933).length < 2 ^ (prefixWord ++ tailWord_304933).sum := by decide
  have hdescent : baseEnd_304933 < baseStart_304933 := by decide
  rcases family_descends (prefixWord ++ tailWord_304933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304936 : List Nat := [2, 1, 5, 1, 1, 3, 3, 4]
def baseStart_304936 : Nat := 118140960795 + 304936 * 2 ^ 59
def prefixEnd_304936 : Nat := 4983230072969 + 3 ^ 40 * 304936 * 2
def baseEnd_304936 : Nat := 46393699810229383762261

theorem tailTrace_304936 : CollatzResearch.WordTrace tailWord_304936 prefixEnd_304936 46393699810229383762261 := by
  unfold tailWord_304936
  simp only [CollatzResearch.WordTrace]
  refine ⟨5560964811638212883847331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7414619748850950511796441 5560964811638212883847331)
  ·
    refine ⟨8341447217457319325770997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5560964811638212883847331 8341447217457319325770997)
    ·
      refine ⟨782010676636623686791031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8341447217457319325770997 782010676636623686791031)
      ·
        refine ⟨1173016014954935530186547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 782010676636623686791031 1173016014954935530186547)
        ·
          refine ⟨1759524022432403295279821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1173016014954935530186547 1759524022432403295279821)
          ·
            refine ⟨659821508412151235729933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1759524022432403295279821 659821508412151235729933)
            ·
              refine ⟨247433065654556713398725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 659821508412151235729933 247433065654556713398725)
              ·
                refine ⟨46393699810229383762261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 247433065654556713398725 46393699810229383762261)
                ·
                  rfl

theorem cell20_304936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 3, 4].length) (baseStart_304936 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_304936 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_304936 prefixEnd_304936 := by exact prefixLift 304936
  have htrace : WordTrace (prefixWord ++ tailWord_304936) baseStart_304936 baseEnd_304936 := by
    simpa [prefixWord, tailWord_304936, baseEnd_304936] using wordTrace_append hprefix tailTrace_304936
  have hstable : (prefixWord ++ tailWord_304936).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304936).length < 2 ^ (prefixWord ++ tailWord_304936).sum := by decide
  have hdescent : baseEnd_304936 < baseStart_304936 := by decide
  rcases family_descends (prefixWord ++ tailWord_304936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304957 : List Nat := [1, 4, 1, 4, 1, 2, 7]
def baseStart_304957 : Nat := 118140960795 + 304957 * 2 ^ 59
def prefixEnd_304957 : Nat := 4983230072969 + 3 ^ 40 * 304957 * 2
def baseEnd_304957 : Nat := 15465631600322823509633

theorem tailTrace_304957 : CollatzResearch.WordTrace tailWord_304957 prefixEnd_304957 15465631600322823509633 := by
  unfold tailWord_304957
  simp only [CollatzResearch.WordTrace]
  refine ⟨11122695556200346354209125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7415130370800230902806083 11122695556200346354209125)
  ·
    refine ⟨2085505416787564941414211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11122695556200346354209125 2085505416787564941414211)
    ·
      refine ⟨3128258125181347412121317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2085505416787564941414211 3128258125181347412121317)
      ·
        refine ⟨586548398471502639772747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3128258125181347412121317 586548398471502639772747)
        ·
          refine ⟨879822597707253959659121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 586548398471502639772747 879822597707253959659121)
          ·
            refine ⟨659866948280440469744341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 879822597707253959659121 659866948280440469744341)
            ·
              refine ⟨15465631600322823509633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 659866948280440469744341 15465631600322823509633)
              ·
                rfl

theorem cell20_304957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 7].length) (baseStart_304957 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_304957 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_304957 prefixEnd_304957 := by exact prefixLift 304957
  have htrace : WordTrace (prefixWord ++ tailWord_304957) baseStart_304957 baseEnd_304957 := by
    simpa [prefixWord, tailWord_304957, baseEnd_304957] using wordTrace_append hprefix tailTrace_304957
  have hstable : (prefixWord ++ tailWord_304957).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304957).length < 2 ^ (prefixWord ++ tailWord_304957).sum := by decide
  have hdescent : baseEnd_304957 < baseStart_304957 := by decide
  rcases family_descends (prefixWord ++ tailWord_304957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_304995 : List Nat := [1, 1, 1, 5, 4, 1, 1, 6]
def baseStart_304995 : Nat := 118140960795 + 304995 * 2 ^ 59
def prefixEnd_304995 : Nat := 4983230072969 + 3 ^ 40 * 304995 * 2
def baseEnd_304995 : Nat := 46402676212782056106625

theorem tailTrace_304995 : CollatzResearch.WordTrace tailWord_304995 prefixEnd_304995 46402676212782056106625 := by
  unfold tailWord_304995
  simp only [CollatzResearch.WordTrace]
  refine ⟨11124081530062678844092439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7416054353375119229394959 11124081530062678844092439)
  ·
    refine ⟨16686122295094018266138659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11124081530062678844092439 16686122295094018266138659)
    ·
      refine ⟨25029183442641027399207989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16686122295094018266138659 25029183442641027399207989)
      ·
        refine ⟨2346485947747596318675749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25029183442641027399207989 2346485947747596318675749)
        ·
          refine ⟨439966115202674309751703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2346485947747596318675749 439966115202674309751703)
          ·
            refine ⟨659949172804011464627555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 439966115202674309751703 659949172804011464627555)
            ·
              refine ⟨989923759206017196941333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 659949172804011464627555 989923759206017196941333)
              ·
                refine ⟨46402676212782056106625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 989923759206017196941333 46402676212782056106625)
                ·
                  rfl

theorem cell20_304995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 6].length) (baseStart_304995 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_304995 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_304995 prefixEnd_304995 := by exact prefixLift 304995
  have htrace : WordTrace (prefixWord ++ tailWord_304995) baseStart_304995 baseEnd_304995 := by
    simpa [prefixWord, tailWord_304995, baseEnd_304995] using wordTrace_append hprefix tailTrace_304995
  have hstable : (prefixWord ++ tailWord_304995).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_304995).length < 2 ^ (prefixWord ++ tailWord_304995).sum := by decide
  have hdescent : baseEnd_304995 < baseStart_304995 := by decide
  rcases family_descends (prefixWord ++ tailWord_304995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305005 : List Nat := [1, 5, 1, 1, 1, 1, 5, 3, 2]
def baseStart_305005 : Nat := 118140960795 + 305005 * 2 ^ 59
def prefixEnd_305005 : Nat := 4983230072969 + 3 ^ 40 * 305005 * 2
def baseEnd_305005 : Nat := 139212592910830577986501

theorem tailTrace_305005 : CollatzResearch.WordTrace tailWord_305005 prefixEnd_305005 139212592910830577986501 := by
  unfold tailWord_305005
  simp only [CollatzResearch.WordTrace]
  refine ⟨11124446260026450551956469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7416297506684300367970979 11124446260026450551956469)
  ·
    refine ⟨1042916836877479739245919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11124446260026450551956469 1042916836877479739245919)
    ·
      refine ⟨1564375255316219608868879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1042916836877479739245919 1564375255316219608868879)
      ·
        refine ⟨2346562882974329413303319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1564375255316219608868879 2346562882974329413303319)
        ·
          refine ⟨3519844324461494119954979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2346562882974329413303319 3519844324461494119954979)
          ·
            refine ⟨5279766486692241179932469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3519844324461494119954979 5279766486692241179932469)
            ·
              refine ⟨494978108127397610618669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5279766486692241179932469 494978108127397610618669)
              ·
                refine ⟨185616790547774103982001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 494978108127397610618669 185616790547774103982001)
                ·
                  refine ⟨139212592910830577986501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 185616790547774103982001 139212592910830577986501)
                  ·
                    rfl

theorem cell20_305005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 5, 3, 2].length) (baseStart_305005 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_305005 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_305005 prefixEnd_305005 := by exact prefixLift 305005
  have htrace : WordTrace (prefixWord ++ tailWord_305005) baseStart_305005 baseEnd_305005 := by
    simpa [prefixWord, tailWord_305005, baseEnd_305005] using wordTrace_append hprefix tailTrace_305005
  have hstable : (prefixWord ++ tailWord_305005).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305005).length < 2 ^ (prefixWord ++ tailWord_305005).sum := by decide
  have hdescent : baseEnd_305005 < baseStart_305005 := by decide
  rcases family_descends (prefixWord ++ tailWord_305005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305022 : List Nat := [4, 2, 3, 1, 1, 3, 1, 1, 4]
def baseStart_305022 : Nat := 118140960795 + 305022 * 2 ^ 59
def prefixEnd_305022 : Nat := 4983230072969 + 3 ^ 40 * 305022 * 2
def baseEnd_305022 : Nat := 139220352174054074419765

theorem tailTrace_305022 : CollatzResearch.WordTrace tailWord_305022 prefixEnd_305022 139220352174054074419765 := by
  unfold tailWord_305022
  simp only [CollatzResearch.WordTrace]
  refine ⟨1390633287620607806915665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7416710867309908303550213 1390633287620607806915665)
  ·
    refine ⟨1042974965715455855186749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1390633287620607806915665 1042974965715455855186749)
    ·
      refine ⟨391115612143295945695031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1042974965715455855186749 391115612143295945695031)
      ·
        refine ⟨586673418214943918542547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 391115612143295945695031 586673418214943918542547)
        ·
          refine ⟨880010127322415877813821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 586673418214943918542547 880010127322415877813821)
          ·
            refine ⟨330003797745905954180183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 880010127322415877813821 330003797745905954180183)
            ·
              refine ⟨495005696618858931270275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 330003797745905954180183 495005696618858931270275)
              ·
                refine ⟨742508544928288396905413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 495005696618858931270275 742508544928288396905413)
                ·
                  refine ⟨139220352174054074419765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 742508544928288396905413 139220352174054074419765)
                  ·
                    rfl

theorem cell20_305022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 1, 1, 4].length) (baseStart_305022 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_305022 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_305022 prefixEnd_305022 := by exact prefixLift 305022
  have htrace : WordTrace (prefixWord ++ tailWord_305022) baseStart_305022 baseEnd_305022 := by
    simpa [prefixWord, tailWord_305022, baseEnd_305022] using wordTrace_append hprefix tailTrace_305022
  have hstable : (prefixWord ++ tailWord_305022).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305022).length < 2 ^ (prefixWord ++ tailWord_305022).sum := by decide
  have hdescent : baseEnd_305022 < baseStart_305022 := by decide
  rcases family_descends (prefixWord ++ tailWord_305022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305061 : List Nat := [1, 3, 1, 2, 1, 1, 1, 3, 7]
def baseStart_305061 : Nat := 118140960795 + 305061 * 2 ^ 59
def prefixEnd_305061 : Nat := 4983230072969 + 3 ^ 40 * 305061 * 2
def baseEnd_305061 : Nat := 139238152836743272119605

theorem tailTrace_305061 : CollatzResearch.WordTrace tailWord_305061 prefixEnd_305061 139238152836743272119605 := by
  unfold tailWord_305061
  simp only [CollatzResearch.WordTrace]
  refine ⟨11126488747823572115995037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7417659165215714743996691 11126488747823572115995037)
  ·
    refine ⟨4172433280433839543498139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11126488747823572115995037 4172433280433839543498139)
    ·
      refine ⟨6258649920650759315247209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4172433280433839543498139 6258649920650759315247209)
      ·
        refine ⟨4693987440488069486435407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6258649920650759315247209 4693987440488069486435407)
        ·
          refine ⟨7040981160732104229653111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4693987440488069486435407 7040981160732104229653111)
          ·
            refine ⟨10561471741098156344479667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7040981160732104229653111 10561471741098156344479667)
            ·
              refine ⟨15842207611647234516719501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10561471741098156344479667 15842207611647234516719501)
              ·
                refine ⟨5940827854367712943769813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15842207611647234516719501 5940827854367712943769813)
                ·
                  refine ⟨139238152836743272119605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5940827854367712943769813 139238152836743272119605)
                  ·
                    rfl

theorem cell20_305061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 3, 7].length) (baseStart_305061 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_305061 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_305061 prefixEnd_305061 := by exact prefixLift 305061
  have htrace : WordTrace (prefixWord ++ tailWord_305061) baseStart_305061 baseEnd_305061 := by
    simpa [prefixWord, tailWord_305061, baseEnd_305061] using wordTrace_append hprefix tailTrace_305061
  have hstable : (prefixWord ++ tailWord_305061).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305061).length < 2 ^ (prefixWord ++ tailWord_305061).sum := by decide
  have hdescent : baseEnd_305061 < baseStart_305061 := by decide
  rcases family_descends (prefixWord ++ tailWord_305061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305070 : List Nat := [4, 1, 5, 1, 1, 1, 2, 2, 3]
def baseStart_305070 : Nat := 118140960795 + 305070 * 2 ^ 59
def prefixEnd_305070 : Nat := 4983230072969 + 3 ^ 40 * 305070 * 2
def baseEnd_305070 : Nat := 139242260681979240819569

theorem tailTrace_305070 : CollatzResearch.WordTrace tailWord_305070 prefixEnd_305070 139242260681979240819569 := by
  unfold tailWord_305070
  simp only [CollatzResearch.WordTrace]
  refine ⟨1390852125598870831634083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7417878003193977768715109 1390852125598870831634083)
  ·
    refine ⟨2086278188398306247451125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1390852125598870831634083 2086278188398306247451125)
    ·
      refine ⟨195588580162341210698543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2086278188398306247451125 195588580162341210698543)
      ·
        refine ⟨293382870243511816047815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195588580162341210698543 293382870243511816047815)
        ·
          refine ⟨440074305365267724071723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 293382870243511816047815 440074305365267724071723)
          ·
            refine ⟨660111458047901586107585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 440074305365267724071723 660111458047901586107585)
            ·
              refine ⟨495083593535926189580689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 660111458047901586107585 495083593535926189580689)
              ·
                refine ⟨371312695151944642185517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 495083593535926189580689 371312695151944642185517)
                ·
                  refine ⟨139242260681979240819569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 371312695151944642185517 139242260681979240819569)
                  ·
                    rfl

theorem cell20_305070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 2, 2, 3].length) (baseStart_305070 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_305070 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_305070 prefixEnd_305070 := by exact prefixLift 305070
  have htrace : WordTrace (prefixWord ++ tailWord_305070) baseStart_305070 baseEnd_305070 := by
    simpa [prefixWord, tailWord_305070, baseEnd_305070] using wordTrace_append hprefix tailTrace_305070
  have hstable : (prefixWord ++ tailWord_305070).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305070).length < 2 ^ (prefixWord ++ tailWord_305070).sum := by decide
  have hdescent : baseEnd_305070 < baseStart_305070 := by decide
  rcases family_descends (prefixWord ++ tailWord_305070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305119 : List Nat := [1, 1, 2, 3, 4, 2, 2, 3, 2]
def baseStart_305119 : Nat := 118140960795 + 305119 * 2 ^ 59
def prefixEnd_305119 : Nat := 4983230072969 + 3 ^ 40 * 305119 * 2
def baseEnd_305119 : Nat := 139264625617152848186035

theorem tailTrace_305119 : CollatzResearch.WordTrace tailWord_305119 prefixEnd_305119 139264625617152848186035 := by
  unfold tailWord_305119
  simp only [CollatzResearch.WordTrace]
  refine ⟨11128604181613448021606411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7419069454408965347737607 11128604181613448021606411)
  ·
    refine ⟨16692906272420172032409617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11128604181613448021606411 16692906272420172032409617)
    ·
      refine ⟨12519679704315129024307213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16692906272420172032409617 12519679704315129024307213)
      ·
        refine ⟨4694879889118173384115205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12519679704315129024307213 4694879889118173384115205)
        ·
          refine ⟨880289979209657509521601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4694879889118173384115205 880289979209657509521601)
          ·
            refine ⟨660217484407243132141201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 880289979209657509521601 660217484407243132141201)
            ·
              refine ⟨495163113305432349105901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 660217484407243132141201 495163113305432349105901)
              ·
                refine ⟨185686167489537130914713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 495163113305432349105901 185686167489537130914713)
                ·
                  refine ⟨139264625617152848186035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 185686167489537130914713 139264625617152848186035)
                  ·
                    rfl

theorem cell20_305119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 2, 3, 2].length) (baseStart_305119 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_305119 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_305119 prefixEnd_305119 := by exact prefixLift 305119
  have htrace : WordTrace (prefixWord ++ tailWord_305119) baseStart_305119 baseEnd_305119 := by
    simpa [prefixWord, tailWord_305119, baseEnd_305119] using wordTrace_append hprefix tailTrace_305119
  have hstable : (prefixWord ++ tailWord_305119).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305119).length < 2 ^ (prefixWord ++ tailWord_305119).sum := by decide
  have hdescent : baseEnd_305119 < baseStart_305119 := by decide
  rcases family_descends (prefixWord ++ tailWord_305119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305130 : List Nat := [3, 1, 3, 1, 2, 1, 9]
def baseStart_305130 : Nat := 118140960795 + 305130 * 2 ^ 59
def prefixEnd_305130 : Nat := 4983230072969 + 3 ^ 40 * 305130 * 2
def baseEnd_305130 : Nat := 15474405146320633202147

theorem tailTrace_305130 : CollatzResearch.WordTrace tailWord_305130 prefixEnd_305130 15474405146320633202147 := by
  unfold tailWord_305130
  simp only [CollatzResearch.WordTrace]
  refine ⟨2782251346143399225064211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7419336923049064600171229 2782251346143399225064211)
  ·
    refine ⟨4173377019215098837596317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2782251346143399225064211 4173377019215098837596317)
    ·
      refine ⟨1565016382205662064098619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4173377019215098837596317 1565016382205662064098619)
      ·
        refine ⟨2347524573308493096147929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1565016382205662064098619 2347524573308493096147929)
        ·
          refine ⟨1760643429981369822110947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2347524573308493096147929 1760643429981369822110947)
          ·
            refine ⟨2640965144972054733166421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1760643429981369822110947 2640965144972054733166421)
            ·
              refine ⟨15474405146320633202147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2640965144972054733166421 15474405146320633202147)
              ·
                rfl

theorem cell20_305130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 9].length) (baseStart_305130 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_305130 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_305130 prefixEnd_305130 := by exact prefixLift 305130
  have htrace : WordTrace (prefixWord ++ tailWord_305130) baseStart_305130 baseEnd_305130 := by
    simpa [prefixWord, tailWord_305130, baseEnd_305130] using wordTrace_append hprefix tailTrace_305130
  have hstable : (prefixWord ++ tailWord_305130).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305130).length < 2 ^ (prefixWord ++ tailWord_305130).sum := by decide
  have hdescent : baseEnd_305130 < baseStart_305130 := by decide
  rcases family_descends (prefixWord ++ tailWord_305130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305185 : List Nat := [1, 2, 3, 2, 4, 2, 6]
def baseStart_305185 : Nat := 118140960795 + 305185 * 2 ^ 59
def prefixEnd_305185 : Nat := 4983230072969 + 3 ^ 40 * 305185 * 2
def baseEnd_305185 : Nat := 15477194423949994665085

theorem tailTrace_305185 : CollatzResearch.WordTrace tailWord_305185 prefixEnd_305185 15477194423949994665085 := by
  unfold tailWord_305185
  simp only [CollatzResearch.WordTrace]
  refine ⟨11131011399374341293509009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7420674266249560862339339 11131011399374341293509009)
  ·
    refine ⟨8348258549530755970131757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11131011399374341293509009 8348258549530755970131757)
    ·
      refine ⟨3130596956074033488799409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8348258549530755970131757 3130596956074033488799409)
      ·
        refine ⟨2347947717055525116599557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3130596956074033488799409 2347947717055525116599557)
        ·
          refine ⟨440240196947910959362417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2347947717055525116599557 440240196947910959362417)
          ·
            refine ⟨330180147710933219521813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 440240196947910959362417 330180147710933219521813)
            ·
              refine ⟨15477194423949994665085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 330180147710933219521813 15477194423949994665085)
              ·
                rfl

theorem cell20_305185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 6].length) (baseStart_305185 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_305185 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_305185 prefixEnd_305185 := by exact prefixLift 305185
  have htrace : WordTrace (prefixWord ++ tailWord_305185) baseStart_305185 baseEnd_305185 := by
    simpa [prefixWord, tailWord_305185, baseEnd_305185] using wordTrace_append hprefix tailTrace_305185
  have hstable : (prefixWord ++ tailWord_305185).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305185).length < 2 ^ (prefixWord ++ tailWord_305185).sum := by decide
  have hdescent : baseEnd_305185 < baseStart_305185 := by decide
  rcases family_descends (prefixWord ++ tailWord_305185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305191 : List Nat := [1, 1, 7, 1, 2, 1, 3, 2, 2]
def baseStart_305191 : Nat := 118140960795 + 305191 * 2 ^ 59
def prefixEnd_305191 : Nat := 4983230072969 + 3 ^ 40 * 305191 * 2
def baseEnd_305191 : Nat := 139297488379040597785741

theorem tailTrace_305191 : CollatzResearch.WordTrace tailWord_305191 prefixEnd_305191 139297488379040597785741 := by
  unfold tailWord_305191
  simp only [CollatzResearch.WordTrace]
  refine ⟨11131230237352604318227427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7420820158235069545484951 11131230237352604318227427)
  ·
    refine ⟨16696845356028906477341141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11131230237352604318227427 16696845356028906477341141)
    ·
      refine ⟨391332313031927495562683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 16696845356028906477341141 391332313031927495562683)
      ·
        refine ⟨586998469547891243344025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 391332313031927495562683 586998469547891243344025)
        ·
          refine ⟨440248852160918432508019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 586998469547891243344025 440248852160918432508019)
          ·
            refine ⟨660373278241377648762029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 440248852160918432508019 660373278241377648762029)
            ·
              refine ⟨247639979340516618285761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 660373278241377648762029 247639979340516618285761)
              ·
                refine ⟨185729984505387463714321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 247639979340516618285761 185729984505387463714321)
                ·
                  refine ⟨139297488379040597785741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 185729984505387463714321 139297488379040597785741)
                  ·
                    rfl

theorem cell20_305191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 3, 2, 2].length) (baseStart_305191 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_305191 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_305191 prefixEnd_305191 := by exact prefixLift 305191
  have htrace : WordTrace (prefixWord ++ tailWord_305191) baseStart_305191 baseEnd_305191 := by
    simpa [prefixWord, tailWord_305191, baseEnd_305191] using wordTrace_append hprefix tailTrace_305191
  have hstable : (prefixWord ++ tailWord_305191).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305191).length < 2 ^ (prefixWord ++ tailWord_305191).sum := by decide
  have hdescent : baseEnd_305191 < baseStart_305191 := by decide
  rcases family_descends (prefixWord ++ tailWord_305191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305209 : List Nat := [1, 2, 1, 5, 3, 1, 1, 3, 3]
def baseStart_305209 : Nat := 118140960795 + 305209 * 2 ^ 59
def prefixEnd_305209 : Nat := 4983230072969 + 3 ^ 40 * 305209 * 2
def baseEnd_305209 : Nat := 139305704069512535185667

theorem tailTrace_305209 : CollatzResearch.WordTrace tailWord_305209 prefixEnd_305209 139305704069512535185667 := by
  unfold tailWord_305209
  simp only [CollatzResearch.WordTrace]
  refine ⟨11131886751287393392382681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7421257834191595594921787 11131886751287393392382681)
  ·
    refine ⟨8348915063465545044287011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11131886751287393392382681 8348915063465545044287011)
    ·
      refine ⟨12523372595198317566430517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8348915063465545044287011 12523372595198317566430517)
      ·
        refine ⟨1174066180799842271852861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12523372595198317566430517 1174066180799842271852861)
        ·
          refine ⟨440274817799940851944823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1174066180799842271852861 440274817799940851944823)
          ·
            refine ⟨660412226699911277917235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 440274817799940851944823 660412226699911277917235)
            ·
              refine ⟨990618340049866916875853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 660412226699911277917235 990618340049866916875853)
              ·
                refine ⟨371481877518700093828445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 990618340049866916875853 371481877518700093828445)
                ·
                  refine ⟨139305704069512535185667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 371481877518700093828445 139305704069512535185667)
                  ·
                    rfl

theorem cell20_305209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 3, 3].length) (baseStart_305209 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_305209 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_305209 prefixEnd_305209 := by exact prefixLift 305209
  have htrace : WordTrace (prefixWord ++ tailWord_305209) baseStart_305209 baseEnd_305209 := by
    simpa [prefixWord, tailWord_305209, baseEnd_305209] using wordTrace_append hprefix tailTrace_305209
  have hstable : (prefixWord ++ tailWord_305209).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305209).length < 2 ^ (prefixWord ++ tailWord_305209).sum := by decide
  have hdescent : baseEnd_305209 < baseStart_305209 := by decide
  rcases family_descends (prefixWord ++ tailWord_305209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305244 : List Nat := [2, 2, 4, 1, 1, 10]
def baseStart_305244 : Nat := 118140960795 + 305244 * 2 ^ 59
def prefixEnd_305244 : Nat := 4983230072969 + 3 ^ 40 * 305244 * 2
def baseEnd_305244 : Nat := 5160062186044739593291

theorem tailTrace_305244 : CollatzResearch.WordTrace tailWord_305244 prefixEnd_305244 5160062186044739593291 := by
  unfold tailWord_305244
  simp only [CollatzResearch.WordTrace]
  refine ⟨5566581653080297184953393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7422108870773729579937857 5566581653080297184953393)
  ·
    refine ⟨4174936239810222888715045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5566581653080297184953393 4174936239810222888715045)
    ·
      refine ⟨782800544964416791634071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4174936239810222888715045 782800544964416791634071)
      ·
        refine ⟨1174200817446625187451107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 782800544964416791634071 1174200817446625187451107)
        ·
          refine ⟨1761301226169937781176661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1174200817446625187451107 1761301226169937781176661)
          ·
            refine ⟨5160062186044739593291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1761301226169937781176661 5160062186044739593291)
            ·
              rfl

theorem cell20_305244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 10].length) (baseStart_305244 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_305244 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_305244 prefixEnd_305244 := by exact prefixLift 305244
  have htrace : WordTrace (prefixWord ++ tailWord_305244) baseStart_305244 baseEnd_305244 := by
    simpa [prefixWord, tailWord_305244, baseEnd_305244] using wordTrace_append hprefix tailTrace_305244
  have hstable : (prefixWord ++ tailWord_305244).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305244).length < 2 ^ (prefixWord ++ tailWord_305244).sum := by decide
  have hdescent : baseEnd_305244 < baseStart_305244 := by decide
  rcases family_descends (prefixWord ++ tailWord_305244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305250 : List Nat := [3, 3, 2, 2, 2, 1, 1, 4, 2]
def baseStart_305250 : Nat := 118140960795 + 305250 * 2 ^ 59
def prefixEnd_305250 : Nat := 4983230072969 + 3 ^ 40 * 305250 * 2
def baseEnd_305250 : Nat := 139324417586698614818833

theorem tailTrace_305250 : CollatzResearch.WordTrace tailWord_305250 prefixEnd_305250 139324417586698614818833 := by
  unfold tailWord_305250
  simp only [CollatzResearch.WordTrace]
  refine ⟨2783345536034714348656301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7422254762759238263083469 2783345536034714348656301)
  ·
    refine ⟨1043754576013017880746113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2783345536034714348656301 1043754576013017880746113)
    ·
      refine ⟨782815932009763410559585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1043754576013017880746113 782815932009763410559585)
      ·
        refine ⟨587111949007322557919689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 782815932009763410559585 587111949007322557919689)
        ·
          refine ⟨440333961755491918439767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 587111949007322557919689 440333961755491918439767)
          ·
            refine ⟨660500942633237877659651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 440333961755491918439767 660500942633237877659651)
            ·
              refine ⟨990751413949856816489477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 660500942633237877659651 990751413949856816489477)
              ·
                refine ⟨185765890115598153091777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 990751413949856816489477 185765890115598153091777)
                ·
                  refine ⟨139324417586698614818833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 185765890115598153091777 139324417586698614818833)
                  ·
                    rfl

theorem cell20_305250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 4, 2].length) (baseStart_305250 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_305250 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_305250 prefixEnd_305250 := by exact prefixLift 305250
  have htrace : WordTrace (prefixWord ++ tailWord_305250) baseStart_305250 baseEnd_305250 := by
    simpa [prefixWord, tailWord_305250, baseEnd_305250] using wordTrace_append hprefix tailTrace_305250
  have hstable : (prefixWord ++ tailWord_305250).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305250).length < 2 ^ (prefixWord ++ tailWord_305250).sum := by decide
  have hdescent : baseEnd_305250 < baseStart_305250 := by decide
  rcases family_descends (prefixWord ++ tailWord_305250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305251 : List Nat := [1, 1, 1, 5, 1, 1, 2, 3, 5]
def baseStart_305251 : Nat := 118140960795 + 305251 * 2 ^ 59
def prefixEnd_305251 : Nat := 4983230072969 + 3 ^ 40 * 305251 * 2
def baseEnd_305251 : Nat := 139324874013947055785495

theorem tailTrace_305251 : CollatzResearch.WordTrace tailWord_305251 prefixEnd_305251 139324874013947055785495 := by
  unfold tailWord_305251
  simp only [CollatzResearch.WordTrace]
  refine ⟨11133418617135234565411607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7422279078090156376941071 11133418617135234565411607)
  ·
    refine ⟨16700127925702851848117411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11133418617135234565411607 16700127925702851848117411)
    ·
      refine ⟨25050191888554277772176117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16700127925702851848117411 25050191888554277772176117)
      ·
        refine ⟨2348455489551963541141511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25050191888554277772176117 2348455489551963541141511)
        ·
          refine ⟨3522683234327945311712267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2348455489551963541141511 3522683234327945311712267)
          ·
            refine ⟨5284024851491917967568401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3522683234327945311712267 5284024851491917967568401)
            ·
              refine ⟨3963018638618938475676301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5284024851491917967568401 3963018638618938475676301)
              ·
                refine ⟨1486131989482101928378613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3963018638618938475676301 1486131989482101928378613)
                ·
                  refine ⟨139324874013947055785495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1486131989482101928378613 139324874013947055785495)
                  ·
                    rfl

theorem cell20_305251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 3, 5].length) (baseStart_305251 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_305251 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_305251 prefixEnd_305251 := by exact prefixLift 305251
  have htrace : WordTrace (prefixWord ++ tailWord_305251) baseStart_305251 baseEnd_305251 := by
    simpa [prefixWord, tailWord_305251, baseEnd_305251] using wordTrace_append hprefix tailTrace_305251
  have hstable : (prefixWord ++ tailWord_305251).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305251).length < 2 ^ (prefixWord ++ tailWord_305251).sum := by decide
  have hdescent : baseEnd_305251 < baseStart_305251 := by decide
  rcases family_descends (prefixWord ++ tailWord_305251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305289 : List Nat := [1, 2, 1, 1, 4, 2, 2, 2, 5]
def baseStart_305289 : Nat := 118140960795 + 305289 * 2 ^ 59
def prefixEnd_305289 : Nat := 4983230072969 + 3 ^ 40 * 305289 * 2
def baseEnd_305289 : Nat := 139342218249387812518673

theorem tailTrace_305289 : CollatzResearch.WordTrace tailWord_305289 prefixEnd_305289 139342218249387812518673 := by
  unfold tailWord_305289
  simp only [CollatzResearch.WordTrace]
  refine ⟨11134804590997567055294921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7423203060665044703529947 11134804590997567055294921)
  ·
    refine ⟨8351103443248175291471191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11134804590997567055294921 8351103443248175291471191)
    ·
      refine ⟨12526655164872262937206787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8351103443248175291471191 12526655164872262937206787)
      ·
        refine ⟨18789982747308394405810181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12526655164872262937206787 18789982747308394405810181)
        ·
          refine ⟨3523121765120323951089409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18789982747308394405810181 3523121765120323951089409)
          ·
            refine ⟨2642341323840242963317057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3523121765120323951089409 2642341323840242963317057)
            ·
              refine ⟨1981755992880182222487793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2642341323840242963317057 1981755992880182222487793)
              ·
                refine ⟨1486316994660136666865845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1981755992880182222487793 1486316994660136666865845)
                ·
                  refine ⟨139342218249387812518673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1486316994660136666865845 139342218249387812518673)
                  ·
                    rfl

theorem cell20_305289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 2, 5].length) (baseStart_305289 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_305289 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_305289 prefixEnd_305289 := by exact prefixLift 305289
  have htrace : WordTrace (prefixWord ++ tailWord_305289) baseStart_305289 baseEnd_305289 := by
    simpa [prefixWord, tailWord_305289, baseEnd_305289] using wordTrace_append hprefix tailTrace_305289
  have hstable : (prefixWord ++ tailWord_305289).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305289).length < 2 ^ (prefixWord ++ tailWord_305289).sum := by decide
  have hdescent : baseEnd_305289 < baseStart_305289 := by decide
  rcases family_descends (prefixWord ++ tailWord_305289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305296 : List Nat := [2, 1, 1, 1, 1, 1, 5, 2, 6]
def baseStart_305296 : Nat := 118140960795 + 305296 * 2 ^ 59
def prefixEnd_305296 : Nat := 4983230072969 + 3 ^ 40 * 305296 * 2
def baseEnd_305296 : Nat := 139345413240126899285311

theorem tailTrace_305296 : CollatzResearch.WordTrace tailWord_305296 prefixEnd_305296 139345413240126899285311 := by
  unfold tailWord_305296
  simp only [CollatzResearch.WordTrace]
  refine ⟨5567529950986103625399871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7423373267981471500533161 5567529950986103625399871)
  ·
    refine ⟨8351294926479155438099807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5567529950986103625399871 8351294926479155438099807)
    ·
      refine ⟨12526942389718733157149711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8351294926479155438099807 12526942389718733157149711)
      ·
        refine ⟨18790413584578099735724567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12526942389718733157149711 18790413584578099735724567)
        ·
          refine ⟨28185620376867149603586851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18790413584578099735724567 28185620376867149603586851)
          ·
            refine ⟨42278430565300724405380277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28185620376867149603586851 42278430565300724405380277)
            ·
              refine ⟨3963602865496942913004401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42278430565300724405380277 3963602865496942913004401)
              ·
                refine ⟨2972702149122707184753301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3963602865496942913004401 2972702149122707184753301)
                ·
                  refine ⟨139345413240126899285311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2972702149122707184753301 139345413240126899285311)
                  ·
                    rfl

theorem cell20_305296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 2, 6].length) (baseStart_305296 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_305296 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_305296 prefixEnd_305296 := by exact prefixLift 305296
  have htrace : WordTrace (prefixWord ++ tailWord_305296) baseStart_305296 baseEnd_305296 := by
    simpa [prefixWord, tailWord_305296, baseEnd_305296] using wordTrace_append hprefix tailTrace_305296
  have hstable : (prefixWord ++ tailWord_305296).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305296).length < 2 ^ (prefixWord ++ tailWord_305296).sum := by decide
  have hdescent : baseEnd_305296 < baseStart_305296 := by decide
  rcases family_descends (prefixWord ++ tailWord_305296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305313 : List Nat := [1, 2, 3, 3, 1, 2, 1, 3, 4]
def baseStart_305313 : Nat := 118140960795 + 305313 * 2 ^ 59
def prefixEnd_305313 : Nat := 4983230072969 + 3 ^ 40 * 305313 * 2
def baseEnd_305313 : Nat := 139353172503350395718575

theorem tailTrace_305313 : CollatzResearch.WordTrace tailWord_305313 prefixEnd_305313 139353172503350395718575 := by
  unfold tailWord_305313
  simp only [CollatzResearch.WordTrace]
  refine ⟨11135679942910619154168593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7423786628607079436112395 11135679942910619154168593)
  ·
    refine ⟨8351759957182964365626445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11135679942910619154168593 8351759957182964365626445)
    ·
      refine ⟨3131909983943611637109917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8351759957182964365626445 3131909983943611637109917)
      ·
        refine ⟨1174466243978854363916219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3131909983943611637109917 1174466243978854363916219)
        ·
          refine ⟨1761699365968281545874329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1174466243978854363916219 1761699365968281545874329)
          ·
            refine ⟨1321274524476211159405747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1761699365968281545874329 1321274524476211159405747)
            ·
              refine ⟨1981911786714316739108621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1321274524476211159405747 1981911786714316739108621)
              ·
                refine ⟨743216920017868777165733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1981911786714316739108621 743216920017868777165733)
                ·
                  refine ⟨139353172503350395718575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 743216920017868777165733 139353172503350395718575)
                  ·
                    rfl

theorem cell20_305313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 3, 4].length) (baseStart_305313 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_305313 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_305313 prefixEnd_305313 := by exact prefixLift 305313
  have htrace : WordTrace (prefixWord ++ tailWord_305313) baseStart_305313 baseEnd_305313 := by
    simpa [prefixWord, tailWord_305313, baseEnd_305313] using wordTrace_append hprefix tailTrace_305313
  have hstable : (prefixWord ++ tailWord_305313).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305313).length < 2 ^ (prefixWord ++ tailWord_305313).sum := by decide
  have hdescent : baseEnd_305313 < baseStart_305313 := by decide
  rcases family_descends (prefixWord ++ tailWord_305313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305333 : List Nat := [1, 3, 3, 4, 1, 2, 2, 4]
def baseStart_305333 : Nat := 118140960795 + 305333 * 2 ^ 59
def prefixEnd_305333 : Nat := 4983230072969 + 3 ^ 40 * 305333 * 2
def baseEnd_305333 : Nat := 46454100349439738350609

theorem tailTrace_305333 : CollatzResearch.WordTrace tailWord_305333 prefixEnd_305333 46454100349439738350609 := by
  unfold tailWord_305333
  simp only [CollatzResearch.WordTrace]
  refine ⟨11136409402838162569896653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7424272935225441713264435 11136409402838162569896653)
  ·
    refine ⟨4176153526064310963711245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11136409402838162569896653 4176153526064310963711245)
    ·
      refine ⟨1566057572274116611391717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4176153526064310963711245 1566057572274116611391717)
      ·
        refine ⟨293635794801396864635947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1566057572274116611391717 293635794801396864635947)
        ·
          refine ⟨440453692202095296953921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 293635794801396864635947 440453692202095296953921)
          ·
            refine ⟨330340269151571472715441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 440453692202095296953921 330340269151571472715441)
            ·
              refine ⟨247755201863678604536581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 330340269151571472715441 247755201863678604536581)
              ·
                refine ⟨46454100349439738350609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 247755201863678604536581 46454100349439738350609)
                ·
                  rfl

theorem cell20_305333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 2, 4].length) (baseStart_305333 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_305333 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_305333 prefixEnd_305333 := by exact prefixLift 305333
  have htrace : WordTrace (prefixWord ++ tailWord_305333) baseStart_305333 baseEnd_305333 := by
    simpa [prefixWord, tailWord_305333, baseEnd_305333] using wordTrace_append hprefix tailTrace_305333
  have hstable : (prefixWord ++ tailWord_305333).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305333).length < 2 ^ (prefixWord ++ tailWord_305333).sum := by decide
  have hdescent : baseEnd_305333 < baseStart_305333 := by decide
  rcases family_descends (prefixWord ++ tailWord_305333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305358 : List Nat := [4, 1, 1, 1, 4, 1, 8]
def baseStart_305358 : Nat := 118140960795 + 305358 * 2 ^ 59
def prefixEnd_305358 : Nat := 4983230072969 + 3 ^ 40 * 305358 * 2
def baseEnd_305358 : Nat := 15485967969947804357599

theorem tailTrace_305358 : CollatzResearch.WordTrace tailWord_305358 prefixEnd_305358 15485967969947804357599 := by
  unfold tailWord_305358
  simp only [CollatzResearch.WordTrace]
  refine ⟨1392165153468448979944591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7424880818498394559704485 1392165153468448979944591)
  ·
    refine ⟨2088247730202673469916887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1392165153468448979944591 2088247730202673469916887)
    ·
      refine ⟨3132371595304010204875331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2088247730202673469916887 3132371595304010204875331)
      ·
        refine ⟨4698557392956015307312997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3132371595304010204875331 4698557392956015307312997)
        ·
          refine ⟨880979511179252870121187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4698557392956015307312997 880979511179252870121187)
          ·
            refine ⟨1321469266768879305181781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 880979511179252870121187 1321469266768879305181781)
            ·
              refine ⟨15485967969947804357599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1321469266768879305181781 15485967969947804357599)
              ·
                rfl

theorem cell20_305358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 8].length) (baseStart_305358 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_305358 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_305358 prefixEnd_305358 := by exact prefixLift 305358
  have htrace : WordTrace (prefixWord ++ tailWord_305358) baseStart_305358 baseEnd_305358 := by
    simpa [prefixWord, tailWord_305358, baseEnd_305358] using wordTrace_append hprefix tailTrace_305358
  have hstable : (prefixWord ++ tailWord_305358).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305358).length < 2 ^ (prefixWord ++ tailWord_305358).sum := by decide
  have hdescent : baseEnd_305358 < baseStart_305358 := by decide
  rcases family_descends (prefixWord ++ tailWord_305358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305368 : List Nat := [2, 1, 2, 2, 4, 3, 1, 1, 4]
def baseStart_305368 : Nat := 118140960795 + 305368 * 2 ^ 59
def prefixEnd_305368 : Nat := 4983230072969 + 3 ^ 40 * 305368 * 2
def baseEnd_305368 : Nat := 139378276002014648885017

theorem tailTrace_305368 : CollatzResearch.WordTrace tailWord_305368 prefixEnd_305368 139378276002014648885017 := by
  unfold tailWord_305368
  simp only [CollatzResearch.WordTrace]
  refine ⟨5568842978855681773710379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7425123971807575698280505 5568842978855681773710379)
  ·
    refine ⟨8353264468283522660565569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5568842978855681773710379 8353264468283522660565569)
    ·
      refine ⟨6264948351212641995424177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8353264468283522660565569 6264948351212641995424177)
      ·
        refine ⟨4698711263409481496568133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6264948351212641995424177 4698711263409481496568133)
        ·
          refine ⟨881008361889277780606525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4698711263409481496568133 881008361889277780606525)
          ·
            refine ⟨330378135708479167727447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 881008361889277780606525 330378135708479167727447)
            ·
              refine ⟨495567203562718751591171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 330378135708479167727447 495567203562718751591171)
              ·
                refine ⟨743350805344078127386757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 495567203562718751591171 743350805344078127386757)
                ·
                  refine ⟨139378276002014648885017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 743350805344078127386757 139378276002014648885017)
                  ·
                    rfl

theorem cell20_305368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 1, 1, 4].length) (baseStart_305368 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_305368 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_305368 prefixEnd_305368 := by exact prefixLift 305368
  have htrace : WordTrace (prefixWord ++ tailWord_305368) baseStart_305368 baseEnd_305368 := by
    simpa [prefixWord, tailWord_305368, baseEnd_305368] using wordTrace_append hprefix tailTrace_305368
  have hstable : (prefixWord ++ tailWord_305368).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305368).length < 2 ^ (prefixWord ++ tailWord_305368).sum := by decide
  have hdescent : baseEnd_305368 < baseStart_305368 := by decide
  rcases family_descends (prefixWord ++ tailWord_305368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305417 : List Nat := [1, 2, 1, 1, 3, 12]
def baseStart_305417 : Nat := 118140960795 + 305417 * 2 ^ 59
def prefixEnd_305417 : Nat := 4983230072969 + 3 ^ 40 * 305417 * 2
def baseEnd_305417 : Nat := 5162986701377342824129

theorem tailTrace_305417 : CollatzResearch.WordTrace tailWord_305417 prefixEnd_305417 5162986701377342824129 := by
  unfold tailWord_305417
  simp only [CollatzResearch.WordTrace]
  refine ⟨11139473134533844915954505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7426315423022563277303003 11139473134533844915954505)
  ·
    refine ⟨8354604850900383686965879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11139473134533844915954505 8354604850900383686965879)
    ·
      refine ⟨12531907276350575530448819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8354604850900383686965879 12531907276350575530448819)
      ·
        refine ⟨18797860914525863295673229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12531907276350575530448819 18797860914525863295673229)
        ·
          refine ⟨7049197842947198735877461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18797860914525863295673229 7049197842947198735877461)
          ·
            refine ⟨5162986701377342824129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 7049197842947198735877461 5162986701377342824129)
            ·
              rfl

theorem cell20_305417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 12].length) (baseStart_305417 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_305417 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_305417 prefixEnd_305417 := by exact prefixLift 305417
  have htrace : WordTrace (prefixWord ++ tailWord_305417) baseStart_305417 baseEnd_305417 := by
    simpa [prefixWord, tailWord_305417, baseEnd_305417] using wordTrace_append hprefix tailTrace_305417
  have hstable : (prefixWord ++ tailWord_305417).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305417).length < 2 ^ (prefixWord ++ tailWord_305417).sum := by decide
  have hdescent : baseEnd_305417 < baseStart_305417 := by decide
  rcases family_descends (prefixWord ++ tailWord_305417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305420 : List Nat := [2, 2, 1, 2, 2, 2, 4, 2, 3]
def baseStart_305420 : Nat := 118140960795 + 305420 * 2 ^ 59
def prefixEnd_305420 : Nat := 4983230072969 + 3 ^ 40 * 305420 * 2
def baseEnd_305420 : Nat := 139402010218933579151471

theorem tailTrace_305420 : CollatzResearch.WordTrace tailWord_305420 prefixEnd_305420 139402010218933579151471 := by
  unfold tailWord_305420
  simp only [CollatzResearch.WordTrace]
  refine ⟨5569791276761488214156857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7426388369015317618875809 5569791276761488214156857)
  ·
    refine ⟨4177343457571116160617643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5569791276761488214156857 4177343457571116160617643)
    ·
      refine ⟨6266015186356674240926465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4177343457571116160617643 6266015186356674240926465)
      ·
        refine ⟨4699511389767505680694849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6266015186356674240926465 4699511389767505680694849)
        ·
          refine ⟨3524633542325629260521137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4699511389767505680694849 3524633542325629260521137)
          ·
            refine ⟨2643475156744221945390853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3524633542325629260521137 2643475156744221945390853)
            ·
              refine ⟨495651591889541614760785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2643475156744221945390853 495651591889541614760785)
              ·
                refine ⟨371738693917156211070589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 495651591889541614760785 371738693917156211070589)
                ·
                  refine ⟨139402010218933579151471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 371738693917156211070589 139402010218933579151471)
                  ·
                    rfl

theorem cell20_305420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 4, 2, 3].length) (baseStart_305420 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_305420 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_305420 prefixEnd_305420 := by exact prefixLift 305420
  have htrace : WordTrace (prefixWord ++ tailWord_305420) baseStart_305420 baseEnd_305420 := by
    simpa [prefixWord, tailWord_305420, baseEnd_305420] using wordTrace_append hprefix tailTrace_305420
  have hstable : (prefixWord ++ tailWord_305420).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305420).length < 2 ^ (prefixWord ++ tailWord_305420).sum := by decide
  have hdescent : baseEnd_305420 < baseStart_305420 := by decide
  rcases family_descends (prefixWord ++ tailWord_305420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305455 : List Nat := [1, 1, 2, 1, 2, 1, 4, 8]
def baseStart_305455 : Nat := 118140960795 + 305455 * 2 ^ 59
def prefixEnd_305455 : Nat := 4983230072969 + 3 ^ 40 * 305455 * 2
def baseEnd_305455 : Nat := 46472661724209670994887

theorem tailTrace_305455 : CollatzResearch.WordTrace tailWord_305455 prefixEnd_305455 46472661724209670994887 := by
  unfold tailWord_305455
  simp only [CollatzResearch.WordTrace]
  refine ⟨11140859108396177405837819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7427239405597451603891879 11140859108396177405837819)
  ·
    refine ⟨16711288662594266108756729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11140859108396177405837819 16711288662594266108756729)
    ·
      refine ⟨12533466496945699581567547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16711288662594266108756729 12533466496945699581567547)
      ·
        refine ⟨18800199745418549372351321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12533466496945699581567547 18800199745418549372351321)
        ·
          refine ⟨14100149809063912029263491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18800199745418549372351321 14100149809063912029263491)
          ·
            refine ⟨21150224713595868043895237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14100149809063912029263491 21150224713595868043895237)
            ·
              refine ⟨3965667133799225258230357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21150224713595868043895237 3965667133799225258230357)
              ·
                refine ⟨46472661724209670994887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3965667133799225258230357 46472661724209670994887)
                ·
                  rfl

theorem cell20_305455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 8].length) (baseStart_305455 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_305455 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_305455 prefixEnd_305455 := by exact prefixLift 305455
  have htrace : WordTrace (prefixWord ++ tailWord_305455) baseStart_305455 baseEnd_305455 := by
    simpa [prefixWord, tailWord_305455, baseEnd_305455] using wordTrace_append hprefix tailTrace_305455
  have hstable : (prefixWord ++ tailWord_305455).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305455).length < 2 ^ (prefixWord ++ tailWord_305455).sum := by decide
  have hdescent : baseEnd_305455 < baseStart_305455 := by decide
  rcases family_descends (prefixWord ++ tailWord_305455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305479 : List Nat := [1, 1, 4, 1, 2, 2, 3, 1, 5]
def baseStart_305479 : Nat := 118140960795 + 305479 * 2 ^ 59
def prefixEnd_305479 : Nat := 4983230072969 + 3 ^ 40 * 305479 * 2
def baseEnd_305479 : Nat := 139428939426591596184563

theorem tailTrace_305479 : CollatzResearch.WordTrace tailWord_305479 prefixEnd_305479 139428939426591596184563 := by
  unfold tailWord_305479
  simp only [CollatzResearch.WordTrace]
  refine ⟨11141734460309229504711491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7427822973539486336474327 11141734460309229504711491)
  ·
    refine ⟨16712601690463844257067237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11141734460309229504711491 16712601690463844257067237)
    ·
      refine ⟨3133612816961970798200107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16712601690463844257067237 3133612816961970798200107)
      ·
        refine ⟨4700419225442956197300161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3133612816961970798200107 4700419225442956197300161)
        ·
          refine ⟨3525314419082217147975121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4700419225442956197300161 3525314419082217147975121)
          ·
            refine ⟨2643985814311662860981341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3525314419082217147975121 2643985814311662860981341)
            ·
              refine ⟨991494680366873572868003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2643985814311662860981341 991494680366873572868003)
              ·
                refine ⟨1487242020550310359302005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 991494680366873572868003 1487242020550310359302005)
                ·
                  refine ⟨139428939426591596184563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1487242020550310359302005 139428939426591596184563)
                  ·
                    rfl

theorem cell20_305479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 1, 5].length) (baseStart_305479 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_305479 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_305479 prefixEnd_305479 := by exact prefixLift 305479
  have htrace : WordTrace (prefixWord ++ tailWord_305479) baseStart_305479 baseEnd_305479 := by
    simpa [prefixWord, tailWord_305479, baseEnd_305479] using wordTrace_append hprefix tailTrace_305479
  have hstable : (prefixWord ++ tailWord_305479).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305479).length < 2 ^ (prefixWord ++ tailWord_305479).sum := by decide
  have hdescent : baseEnd_305479 < baseStart_305479 := by decide
  rcases family_descends (prefixWord ++ tailWord_305479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305502 : List Nat := [4, 4, 2, 1, 1, 1, 1, 6]
def baseStart_305502 : Nat := 118140960795 + 305502 * 2 ^ 59
def prefixEnd_305502 : Nat := 4983230072969 + 3 ^ 40 * 305502 * 2
def baseEnd_305502 : Nat := 46479812417768579472601

theorem tailTrace_305502 : CollatzResearch.WordTrace tailWord_305502 prefixEnd_305502 46479812417768579472601 := by
  unfold tailWord_305502
  simp only [CollatzResearch.WordTrace]
  refine ⟨1392821667403238054099845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7428382226150602955199173 1392821667403238054099845)
  ·
    refine ⟨261154062638107135143721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1392821667403238054099845 261154062638107135143721)
    ·
      refine ⟨195865546978580351357791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 261154062638107135143721 195865546978580351357791)
      ·
        refine ⟨293798320467870527036687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195865546978580351357791 293798320467870527036687)
        ·
          refine ⟨440697480701805790555031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 293798320467870527036687 440697480701805790555031)
          ·
            refine ⟨661046221052708685832547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 440697480701805790555031 661046221052708685832547)
            ·
              refine ⟨991569331579063028748821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 661046221052708685832547 991569331579063028748821)
              ·
                refine ⟨46479812417768579472601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 991569331579063028748821 46479812417768579472601)
                ·
                  rfl

theorem cell20_305502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 6].length) (baseStart_305502 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_305502 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_305502 prefixEnd_305502 := by exact prefixLift 305502
  have htrace : WordTrace (prefixWord ++ tailWord_305502) baseStart_305502 baseEnd_305502 := by
    simpa [prefixWord, tailWord_305502, baseEnd_305502] using wordTrace_append hprefix tailTrace_305502
  have hstable : (prefixWord ++ tailWord_305502).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305502).length < 2 ^ (prefixWord ++ tailWord_305502).sum := by decide
  have hdescent : baseEnd_305502 < baseStart_305502 := by decide
  rcases family_descends (prefixWord ++ tailWord_305502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305506 : List Nat := [3, 3, 2, 1, 1, 4, 2, 4]
def baseStart_305506 : Nat := 118140960795 + 305506 * 2 ^ 59
def prefixEnd_305506 : Nat := 4983230072969 + 3 ^ 40 * 305506 * 2
def baseEnd_305506 : Nat := 46480420987433167428151

theorem tailTrace_305506 : CollatzResearch.WordTrace tailWord_305506 prefixEnd_305506 46480420987433167428151 := by
  unfold tailWord_305506
  simp only [CollatzResearch.WordTrace]
  refine ⟨2785679807802853278986093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7428479487474275410629581 2785679807802853278986093)
  ·
    refine ⟨1044629927926069979619785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2785679807802853278986093 1044629927926069979619785)
    ·
      refine ⟨783472445944552484714839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1044629927926069979619785 783472445944552484714839)
      ·
        refine ⟨1175208668916828727072259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 783472445944552484714839 1175208668916828727072259)
        ·
          refine ⟨1762813003375243090608389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1175208668916828727072259 1762813003375243090608389)
          ·
            refine ⟨330527438132858079489073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1762813003375243090608389 330527438132858079489073)
            ·
              refine ⟨247895578599643559616805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 330527438132858079489073 247895578599643559616805)
              ·
                refine ⟨46480420987433167428151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 247895578599643559616805 46480420987433167428151)
                ·
                  rfl

theorem cell20_305506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 2, 4].length) (baseStart_305506 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_305506 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_305506 prefixEnd_305506 := by exact prefixLift 305506
  have htrace : WordTrace (prefixWord ++ tailWord_305506) baseStart_305506 baseEnd_305506 := by
    simpa [prefixWord, tailWord_305506, baseEnd_305506] using wordTrace_append hprefix tailTrace_305506
  have hstable : (prefixWord ++ tailWord_305506).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305506).length < 2 ^ (prefixWord ++ tailWord_305506).sum := by decide
  have hdescent : baseEnd_305506 < baseStart_305506 := by decide
  rcases family_descends (prefixWord ++ tailWord_305506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305516 : List Nat := [2, 2, 1, 1, 7, 1, 1, 3, 2]
def baseStart_305516 : Nat := 118140960795 + 305516 * 2 ^ 59
def prefixEnd_305516 : Nat := 4983230072969 + 3 ^ 40 * 305516 * 2
def baseEnd_305516 : Nat := 139445827234783911951079

theorem tailTrace_305516 : CollatzResearch.WordTrace tailWord_305516 prefixEnd_305516 139445827234783911951079 := by
  unfold tailWord_305516
  simp only [CollatzResearch.WordTrace]
  refine ⟨5571541980587592411904201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7428722640783456549205601 5571541980587592411904201)
  ·
    refine ⟨4178656485440694308928151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5571541980587592411904201 4178656485440694308928151)
    ·
      refine ⟨6267984728161041463392227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4178656485440694308928151 6267984728161041463392227)
      ·
        refine ⟨9401977092241562195088341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6267984728161041463392227 9401977092241562195088341)
        ·
          refine ⟨220358838099411613947383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 9401977092241562195088341 220358838099411613947383)
          ·
            refine ⟨330538257149117420921075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 220358838099411613947383 330538257149117420921075)
            ·
              refine ⟨495807385723676131381613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 330538257149117420921075 495807385723676131381613)
              ·
                refine ⟨185927769646378549268105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 495807385723676131381613 185927769646378549268105)
                ·
                  refine ⟨139445827234783911951079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 185927769646378549268105 139445827234783911951079)
                  ·
                    rfl

theorem cell20_305516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 1, 3, 2].length) (baseStart_305516 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_305516 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_305516 prefixEnd_305516 := by exact prefixLift 305516
  have htrace : WordTrace (prefixWord ++ tailWord_305516) baseStart_305516 baseEnd_305516 := by
    simpa [prefixWord, tailWord_305516, baseEnd_305516] using wordTrace_append hprefix tailTrace_305516
  have hstable : (prefixWord ++ tailWord_305516).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305516).length < 2 ^ (prefixWord ++ tailWord_305516).sum := by decide
  have hdescent : baseEnd_305516 < baseStart_305516 := by decide
  rcases family_descends (prefixWord ++ tailWord_305516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305517 : List Nat := [1, 5, 1, 1, 1, 2, 1, 1, 7]
def baseStart_305517 : Nat := 118140960795 + 305517 * 2 ^ 59
def prefixEnd_305517 : Nat := 4983230072969 + 3 ^ 40 * 305517 * 2
def baseEnd_305517 : Nat := 139446283662032352917741

theorem tailTrace_305517 : CollatzResearch.WordTrace tailWord_305517 prefixEnd_305517 139446283662032352917741 := by
  unfold tailWord_305517
  simp only [CollatzResearch.WordTrace]
  refine ⟨11143120434171561994594805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7428746956114374663063203 11143120434171561994594805)
  ·
    refine ⟨1044667540703583936993263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11143120434171561994594805 1044667540703583936993263)
    ·
      refine ⟨1567001311055375905489895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1044667540703583936993263 1567001311055375905489895)
      ·
        refine ⟨2350501966583063858234843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1567001311055375905489895 2350501966583063858234843)
        ·
          refine ⟨3525752949874595787352265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2350501966583063858234843 3525752949874595787352265)
          ·
            refine ⟨2644314712405946840514199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3525752949874595787352265 2644314712405946840514199)
            ·
              refine ⟨3966472068608920260771299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2644314712405946840514199 3966472068608920260771299)
              ·
                refine ⟨5949708102913380391156949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3966472068608920260771299 5949708102913380391156949)
                ·
                  refine ⟨139446283662032352917741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5949708102913380391156949 139446283662032352917741)
                  ·
                    rfl

theorem cell20_305517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_305517 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_305517 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_305517 prefixEnd_305517 := by exact prefixLift 305517
  have htrace : WordTrace (prefixWord ++ tailWord_305517) baseStart_305517 baseEnd_305517 := by
    simpa [prefixWord, tailWord_305517, baseEnd_305517] using wordTrace_append hprefix tailTrace_305517
  have hstable : (prefixWord ++ tailWord_305517).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305517).length < 2 ^ (prefixWord ++ tailWord_305517).sum := by decide
  have hdescent : baseEnd_305517 < baseStart_305517 := by decide
  rcases family_descends (prefixWord ++ tailWord_305517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305520 : List Nat := [2, 1, 1, 1, 4, 3, 3, 3, 2]
def baseStart_305520 : Nat := 118140960795 + 305520 * 2 ^ 59
def prefixEnd_305520 : Nat := 4983230072969 + 3 ^ 40 * 305520 * 2
def baseEnd_305520 : Nat := 139447652943777675817729

theorem tailTrace_305520 : CollatzResearch.WordTrace tailWord_305520 prefixEnd_305520 139447652943777675817729 := by
  unfold tailWord_305520
  simp only [CollatzResearch.WordTrace]
  refine ⟨5571614926580346753477007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7428819902107129004636009 5571614926580346753477007)
  ·
    refine ⟨8357422389870520130215511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5571614926580346753477007 8357422389870520130215511)
    ·
      refine ⟨12536133584805780195323267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8357422389870520130215511 12536133584805780195323267)
      ·
        refine ⟨18804200377208670292984901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12536133584805780195323267 18804200377208670292984901)
        ·
          refine ⟨3525787570726625679934669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18804200377208670292984901 3525787570726625679934669)
          ·
            refine ⟨1322170339022484629975501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3525787570726625679934669 1322170339022484629975501)
            ·
              refine ⟨495813877133431736240813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1322170339022484629975501 495813877133431736240813)
              ·
                refine ⟨185930203925036901090305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 495813877133431736240813 185930203925036901090305)
                ·
                  refine ⟨139447652943777675817729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 185930203925036901090305 139447652943777675817729)
                  ·
                    rfl

theorem cell20_305520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 3, 3, 2].length) (baseStart_305520 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_305520 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_305520 prefixEnd_305520 := by exact prefixLift 305520
  have htrace : WordTrace (prefixWord ++ tailWord_305520) baseStart_305520 baseEnd_305520 := by
    simpa [prefixWord, tailWord_305520, baseEnd_305520] using wordTrace_append hprefix tailTrace_305520
  have hstable : (prefixWord ++ tailWord_305520).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305520).length < 2 ^ (prefixWord ++ tailWord_305520).sum := by decide
  have hdescent : baseEnd_305520 < baseStart_305520 := by decide
  rcases family_descends (prefixWord ++ tailWord_305520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305531 : List Nat := [1, 1, 1, 1, 1, 7, 8]
def baseStart_305531 : Nat := 118140960795 + 305531 * 2 ^ 59
def prefixEnd_305531 : Nat := 4983230072969 + 3 ^ 40 * 305531 * 2
def baseEnd_305531 : Nat := 15494741515945614050113

theorem tailTrace_305531 : CollatzResearch.WordTrace tailWord_305531 prefixEnd_305531 15494741515945614050113 := by
  unfold tailWord_305531
  simp only [CollatzResearch.WordTrace]
  refine ⟨11143631056120842385604447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7429087370747228257069631 11143631056120842385604447)
  ·
    refine ⟨16715446584181263578406671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11143631056120842385604447 16715446584181263578406671)
    ·
      refine ⟨25073169876271895367610007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16715446584181263578406671 25073169876271895367610007)
      ·
        refine ⟨37609754814407843051415011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25073169876271895367610007 37609754814407843051415011)
        ·
          refine ⟨56414632221611764577122517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37609754814407843051415011 56414632221611764577122517)
          ·
            refine ⟨1322217942694025732276309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 56414632221611764577122517 1322217942694025732276309)
            ·
              refine ⟨15494741515945614050113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1322217942694025732276309 15494741515945614050113)
              ·
                rfl

theorem cell20_305531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 8].length) (baseStart_305531 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_305531 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_305531 prefixEnd_305531 := by exact prefixLift 305531
  have htrace : WordTrace (prefixWord ++ tailWord_305531) baseStart_305531 baseEnd_305531 := by
    simpa [prefixWord, tailWord_305531, baseEnd_305531] using wordTrace_append hprefix tailTrace_305531
  have hstable : (prefixWord ++ tailWord_305531).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305531).length < 2 ^ (prefixWord ++ tailWord_305531).sum := by decide
  have hdescent : baseEnd_305531 < baseStart_305531 := by decide
  rcases family_descends (prefixWord ++ tailWord_305531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305548 : List Nat := [2, 2, 1, 2, 1, 5, 2, 5]
def baseStart_305548 : Nat := 118140960795 + 305548 * 2 ^ 59
def prefixEnd_305548 : Nat := 4983230072969 + 3 ^ 40 * 305548 * 2
def baseEnd_305548 : Nat := 46486810968911340961427

theorem tailTrace_305548 : CollatzResearch.WordTrace tailWord_305548 prefixEnd_305548 46486810968911340961427 := by
  unfold tailWord_305548
  simp only [CollatzResearch.WordTrace]
  refine ⟨5572125548529627144486649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7429500731372836192648865 5572125548529627144486649)
  ·
    refine ⟨4179094161397220358364987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5572125548529627144486649 4179094161397220358364987)
    ·
      refine ⟨6268641242095830537547481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4179094161397220358364987 6268641242095830537547481)
      ·
        refine ⟨4701480931571872903160611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6268641242095830537547481 4701480931571872903160611)
        ·
          refine ⟨7052221397357809354740917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4701480931571872903160611 7052221397357809354740917)
          ·
            refine ⟨661145756002294627006961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7052221397357809354740917 661145756002294627006961)
            ·
              refine ⟨495859317001720970255221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 661145756002294627006961 495859317001720970255221)
              ·
                refine ⟨46486810968911340961427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 495859317001720970255221 46486810968911340961427)
                ·
                  rfl

theorem cell20_305548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 2, 5].length) (baseStart_305548 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_305548 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_305548 prefixEnd_305548 := by exact prefixLift 305548
  have htrace : WordTrace (prefixWord ++ tailWord_305548) baseStart_305548 baseEnd_305548 := by
    simpa [prefixWord, tailWord_305548, baseEnd_305548] using wordTrace_append hprefix tailTrace_305548
  have hstable : (prefixWord ++ tailWord_305548).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305548).length < 2 ^ (prefixWord ++ tailWord_305548).sum := by decide
  have hdescent : baseEnd_305548 < baseStart_305548 := by decide
  rcases family_descends (prefixWord ++ tailWord_305548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305588 : List Nat := [2, 5, 2, 2, 1, 2, 2, 2, 2]
def baseStart_305588 : Nat := 118140960795 + 305588 * 2 ^ 59
def prefixEnd_305588 : Nat := 4983230072969 + 3 ^ 40 * 305588 * 2
def baseEnd_305588 : Nat := 139478689996671661550785

theorem tailTrace_305588 : CollatzResearch.WordTrace tailWord_305588 prefixEnd_305588 139478689996671661550785 := by
  unfold tailWord_305588
  simp only [CollatzResearch.WordTrace]
  refine ⟨5572855008457170560214709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7430473344609560746952945 5572855008457170560214709)
  ·
    refine ⟨522455157042859740020129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5572855008457170560214709 522455157042859740020129)
    ·
      refine ⟨391841367782144805015097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 522455157042859740020129 391841367782144805015097)
      ·
        refine ⟨293881025836608603761323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 391841367782144805015097 293881025836608603761323)
        ·
          refine ⟨440821538754912905641985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 293881025836608603761323 440821538754912905641985)
          ·
            refine ⟨330616154066184679231489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 440821538754912905641985 330616154066184679231489)
            ·
              refine ⟨247962115549638509423617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 330616154066184679231489 247962115549638509423617)
              ·
                refine ⟨185971586662228882067713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 247962115549638509423617 185971586662228882067713)
                ·
                  refine ⟨139478689996671661550785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 185971586662228882067713 139478689996671661550785)
                  ·
                    rfl

theorem cell20_305588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 2, 2, 2].length) (baseStart_305588 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_305588 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_305588 prefixEnd_305588 := by exact prefixLift 305588
  have htrace : WordTrace (prefixWord ++ tailWord_305588) baseStart_305588 baseEnd_305588 := by
    simpa [prefixWord, tailWord_305588, baseEnd_305588] using wordTrace_append hprefix tailTrace_305588
  have hstable : (prefixWord ++ tailWord_305588).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305588).length < 2 ^ (prefixWord ++ tailWord_305588).sum := by decide
  have hdescent : baseEnd_305588 < baseStart_305588 := by decide
  rcases family_descends (prefixWord ++ tailWord_305588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305589 : List Nat := [1, 3, 3, 2, 3, 1, 2, 2, 3]
def baseStart_305589 : Nat := 118140960795 + 305589 * 2 ^ 59
def prefixEnd_305589 : Nat := 4983230072969 + 3 ^ 40 * 305589 * 2
def baseEnd_305589 : Nat := 139479146423920102517447

theorem tailTrace_305589 : CollatzResearch.WordTrace tailWord_305589 prefixEnd_305589 139479146423920102517447 := by
  unfold tailWord_305589
  simp only [CollatzResearch.WordTrace]
  refine ⟨11145746489910718291215821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7430497659940478860810547 11145746489910718291215821)
  ·
    refine ⟨4179654933716519359205933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11145746489910718291215821 4179654933716519359205933)
    ·
      refine ⟨1567370600143694759702225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4179654933716519359205933 1567370600143694759702225)
      ·
        refine ⟨1175527950107771069776669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1567370600143694759702225 1175527950107771069776669)
        ·
          refine ⟨440822981290414151166251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1175527950107771069776669 440822981290414151166251)
          ·
            refine ⟨661234471935621226749377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 440822981290414151166251 661234471935621226749377)
            ·
              refine ⟨495925853951715920062033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 661234471935621226749377 495925853951715920062033)
              ·
                refine ⟨371944390463786940046525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 495925853951715920062033 371944390463786940046525)
                ·
                  refine ⟨139479146423920102517447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 371944390463786940046525 139479146423920102517447)
                  ·
                    rfl

theorem cell20_305589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 2, 2, 3].length) (baseStart_305589 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_305589 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_305589 prefixEnd_305589 := by exact prefixLift 305589
  have htrace : WordTrace (prefixWord ++ tailWord_305589) baseStart_305589 baseEnd_305589 := by
    simpa [prefixWord, tailWord_305589, baseEnd_305589] using wordTrace_append hprefix tailTrace_305589
  have hstable : (prefixWord ++ tailWord_305589).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305589).length < 2 ^ (prefixWord ++ tailWord_305589).sum := by decide
  have hdescent : baseEnd_305589 < baseStart_305589 := by decide
  rcases family_descends (prefixWord ++ tailWord_305589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305600 : List Nat := [2, 1, 1, 2, 3, 1, 1, 5, 4]
def baseStart_305600 : Nat := 118140960795 + 305600 * 2 ^ 59
def prefixEnd_305600 : Nat := 4983230072969 + 3 ^ 40 * 305600 * 2
def baseEnd_305600 : Nat := 139484167123652953150735

theorem tailTrace_305600 : CollatzResearch.WordTrace tailWord_305600 prefixEnd_305600 139484167123652953150735 := by
  unfold tailWord_305600
  simp only [CollatzResearch.WordTrace]
  refine ⟨5573073846435433584933127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7430765128580578113244169 5573073846435433584933127)
  ·
    refine ⟨8359610769653150377399691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5573073846435433584933127 8359610769653150377399691)
    ·
      refine ⟨12539416154479725566099537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8359610769653150377399691 12539416154479725566099537)
      ·
        refine ⟨9404562115859794174574653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12539416154479725566099537 9404562115859794174574653)
        ·
          refine ⟨3526710793447422815465495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9404562115859794174574653 3526710793447422815465495)
          ·
            refine ⟨5290066190171134223198243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3526710793447422815465495 5290066190171134223198243)
            ·
              refine ⟨7935099285256701334797365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5290066190171134223198243 7935099285256701334797365)
              ·
                refine ⟨743915557992815750137253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7935099285256701334797365 743915557992815750137253)
                ·
                  refine ⟨139484167123652953150735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 743915557992815750137253 139484167123652953150735)
                  ·
                    rfl

theorem cell20_305600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 5, 4].length) (baseStart_305600 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_305600 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_305600 prefixEnd_305600 := by exact prefixLift 305600
  have htrace : WordTrace (prefixWord ++ tailWord_305600) baseStart_305600 baseEnd_305600 := by
    simpa [prefixWord, tailWord_305600, baseEnd_305600] using wordTrace_append hprefix tailTrace_305600
  have hstable : (prefixWord ++ tailWord_305600).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305600).length < 2 ^ (prefixWord ++ tailWord_305600).sum := by decide
  have hdescent : baseEnd_305600 < baseStart_305600 := by decide
  rcases family_descends (prefixWord ++ tailWord_305600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305665 : List Nat := [1, 2, 4, 1, 3, 2, 3, 1, 3]
def baseStart_305665 : Nat := 118140960795 + 305665 * 2 ^ 59
def prefixEnd_305665 : Nat := 4983230072969 + 3 ^ 40 * 305665 * 2
def baseEnd_305665 : Nat := 139513834894801615983803

theorem tailTrace_305665 : CollatzResearch.WordTrace tailWord_305665 prefixEnd_305665 139513834894801615983803 := by
  unfold tailWord_305665
  simp only [CollatzResearch.WordTrace]
  refine ⟨11148518437635383270982449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7432345625090255513988299 11148518437635383270982449)
  ·
    refine ⟨8361388828226537453236837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11148518437635383270982449 8361388828226537453236837)
    ·
      refine ⟨1567760405292475772481907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8361388828226537453236837 1567760405292475772481907)
      ·
        refine ⟨2351640607938713658722861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1567760405292475772481907 2351640607938713658722861)
        ·
          refine ⟨881865227977017622021073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2351640607938713658722861 881865227977017622021073)
          ·
            refine ⟨661398920982763216515805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 881865227977017622021073 661398920982763216515805)
            ·
              refine ⟨248024595368536206193427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 661398920982763216515805 248024595368536206193427)
              ·
                refine ⟨372036893052804309290141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 248024595368536206193427 372036893052804309290141)
                ·
                  refine ⟨139513834894801615983803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 372036893052804309290141 139513834894801615983803)
                  ·
                    rfl

theorem cell20_305665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 3, 1, 3].length) (baseStart_305665 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_305665 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_305665 prefixEnd_305665 := by exact prefixLift 305665
  have htrace : WordTrace (prefixWord ++ tailWord_305665) baseStart_305665 baseEnd_305665 := by
    simpa [prefixWord, tailWord_305665, baseEnd_305665] using wordTrace_append hprefix tailTrace_305665
  have hstable : (prefixWord ++ tailWord_305665).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305665).length < 2 ^ (prefixWord ++ tailWord_305665).sum := by decide
  have hdescent : baseEnd_305665 < baseStart_305665 := by decide
  rcases family_descends (prefixWord ++ tailWord_305665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305669 : List Nat := [1, 3, 1, 1, 2, 2, 2, 5, 3]
def baseStart_305669 : Nat := 118140960795 + 305669 * 2 ^ 59
def prefixEnd_305669 : Nat := 4983230072969 + 3 ^ 40 * 305669 * 2
def baseEnd_305669 : Nat := 139515660603795379850453

theorem tailTrace_305669 : CollatzResearch.WordTrace tailWord_305669 prefixEnd_305669 139515660603795379850453 := by
  unfold tailWord_305669
  simp only [CollatzResearch.WordTrace]
  refine ⟨11148664329620891954128061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7432442886413927969418707 11148664329620891954128061)
  ·
    refine ⟨4180749123607834482798023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11148664329620891954128061 4180749123607834482798023)
    ·
      refine ⟨6271123685411751724197035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4180749123607834482798023 6271123685411751724197035)
      ·
        refine ⟨9406685528117627586295553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6271123685411751724197035 9406685528117627586295553)
        ·
          refine ⟨7055014146088220689721665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9406685528117627586295553 7055014146088220689721665)
          ·
            refine ⟨5291260609566165517291249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7055014146088220689721665 5291260609566165517291249)
            ·
              refine ⟨3968445457174624137968437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5291260609566165517291249 3968445457174624137968437)
              ·
                refine ⟨372041761610121012934541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3968445457174624137968437 372041761610121012934541)
                ·
                  refine ⟨139515660603795379850453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 372041761610121012934541 139515660603795379850453)
                  ·
                    rfl

theorem cell20_305669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 5, 3].length) (baseStart_305669 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_305669 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_305669 prefixEnd_305669 := by exact prefixLift 305669
  have htrace : WordTrace (prefixWord ++ tailWord_305669) baseStart_305669 baseEnd_305669 := by
    simpa [prefixWord, tailWord_305669, baseEnd_305669] using wordTrace_append hprefix tailTrace_305669
  have hstable : (prefixWord ++ tailWord_305669).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305669).length < 2 ^ (prefixWord ++ tailWord_305669).sum := by decide
  have hdescent : baseEnd_305669 < baseStart_305669 := by decide
  rcases family_descends (prefixWord ++ tailWord_305669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305683 : List Nat := [1, 1, 1, 2, 1, 5, 3, 6]
def baseStart_305683 : Nat := 118140960795 + 305683 * 2 ^ 59
def prefixEnd_305683 : Nat := 4983230072969 + 3 ^ 40 * 305683 * 2
def baseEnd_305683 : Nat := 46507350195091184461243

theorem tailTrace_305683 : CollatzResearch.WordTrace tailWord_305683 prefixEnd_305683 46507350195091184461243 := by
  unfold tailWord_305683
  simp only [CollatzResearch.WordTrace]
  refine ⟨11149174951570172345137703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7432783301046781563425135 11149174951570172345137703)
  ·
    refine ⟨16723762427355258517706555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11149174951570172345137703 16723762427355258517706555)
    ·
      refine ⟨25085643641032887776559833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16723762427355258517706555 25085643641032887776559833)
      ·
        refine ⟨18814232730774665832419875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25085643641032887776559833 18814232730774665832419875)
        ·
          refine ⟨28221349096161998748629813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18814232730774665832419875 28221349096161998748629813)
          ·
            refine ⟨2645751477765187382684045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28221349096161998748629813 2645751477765187382684045)
            ·
              refine ⟨992156804161945268506517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2645751477765187382684045 992156804161945268506517)
              ·
                refine ⟨46507350195091184461243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 992156804161945268506517 46507350195091184461243)
                ·
                  rfl

theorem cell20_305683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 6].length) (baseStart_305683 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_305683 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_305683 prefixEnd_305683 := by exact prefixLift 305683
  have htrace : WordTrace (prefixWord ++ tailWord_305683) baseStart_305683 baseEnd_305683 := by
    simpa [prefixWord, tailWord_305683, baseEnd_305683] using wordTrace_append hprefix tailTrace_305683
  have hstable : (prefixWord ++ tailWord_305683).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305683).length < 2 ^ (prefixWord ++ tailWord_305683).sum := by decide
  have hdescent : baseEnd_305683 < baseStart_305683 := by decide
  rcases family_descends (prefixWord ++ tailWord_305683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305716 : List Nat := [2, 5, 1, 3, 2, 1, 2, 1, 3]
def baseStart_305716 : Nat := 118140960795 + 305716 * 2 ^ 59
def prefixEnd_305716 : Nat := 4983230072969 + 3 ^ 40 * 305716 * 2
def baseEnd_305716 : Nat := 139537112684472105283595

theorem tailTrace_305716 : CollatzResearch.WordTrace tailWord_305716 prefixEnd_305716 139537112684472105283595 := by
  unfold tailWord_305716
  simp only [CollatzResearch.WordTrace]
  refine ⟨5575189280225309490544501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7433585706967079320726001 5575189280225309490544501)
  ·
    refine ⟨522673995021122764738547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5575189280225309490544501 522673995021122764738547)
    ·
      refine ⟨784010992531684147107821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 522673995021122764738547 784010992531684147107821)
      ·
        refine ⟨294004122199381555165433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 784010992531684147107821 294004122199381555165433)
        ·
          refine ⟨220503091649536166374075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 294004122199381555165433 220503091649536166374075)
          ·
            refine ⟨330754637474304249561113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 220503091649536166374075 330754637474304249561113)
            ·
              refine ⟨248065978105728187170835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 330754637474304249561113 248065978105728187170835)
              ·
                refine ⟨372098967158592280756253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 248065978105728187170835 372098967158592280756253)
                ·
                  refine ⟨139537112684472105283595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 372098967158592280756253 139537112684472105283595)
                  ·
                    rfl

theorem cell20_305716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 2, 1, 3].length) (baseStart_305716 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_305716 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_305716 prefixEnd_305716 := by exact prefixLift 305716
  have htrace : WordTrace (prefixWord ++ tailWord_305716) baseStart_305716 baseEnd_305716 := by
    simpa [prefixWord, tailWord_305716, baseEnd_305716] using wordTrace_append hprefix tailTrace_305716
  have hstable : (prefixWord ++ tailWord_305716).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305716).length < 2 ^ (prefixWord ++ tailWord_305716).sum := by decide
  have hdescent : baseEnd_305716 < baseStart_305716 := by decide
  rcases family_descends (prefixWord ++ tailWord_305716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305724 : List Nat := [2, 2, 2, 2, 3, 2, 1, 3, 3]
def baseStart_305724 : Nat := 118140960795 + 305724 * 2 ^ 59
def prefixEnd_305724 : Nat := 4983230072969 + 3 ^ 40 * 305724 * 2
def baseEnd_305724 : Nat := 139540764102459633016895

theorem tailTrace_305724 : CollatzResearch.WordTrace tailWord_305724 prefixEnd_305724 139540764102459633016895 := by
  unfold tailWord_305724
  simp only [CollatzResearch.WordTrace]
  refine ⟨5575335172210818173690113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7433780229614424231586817 5575335172210818173690113)
  ·
    refine ⟨4181501379158113630267585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5575335172210818173690113 4181501379158113630267585)
    ·
      refine ⟨3136126034368585222700689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4181501379158113630267585 3136126034368585222700689)
      ·
        refine ⟨2352094525776438917025517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3136126034368585222700689 2352094525776438917025517)
        ·
          refine ⟨882035447166164593884569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2352094525776438917025517 882035447166164593884569)
          ·
            refine ⟨661526585374623445413427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 882035447166164593884569 661526585374623445413427)
            ·
              refine ⟨992289878061935168120141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 661526585374623445413427 992289878061935168120141)
              ·
                refine ⟨372108704273225688045053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 992289878061935168120141 372108704273225688045053)
                ·
                  refine ⟨139540764102459633016895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 372108704273225688045053 139540764102459633016895)
                  ·
                    rfl

theorem cell20_305724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 3, 3].length) (baseStart_305724 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_305724 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_305724 prefixEnd_305724 := by exact prefixLift 305724
  have htrace : WordTrace (prefixWord ++ tailWord_305724) baseStart_305724 baseEnd_305724 := by
    simpa [prefixWord, tailWord_305724, baseEnd_305724] using wordTrace_append hprefix tailTrace_305724
  have hstable : (prefixWord ++ tailWord_305724).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305724).length < 2 ^ (prefixWord ++ tailWord_305724).sum := by decide
  have hdescent : baseEnd_305724 < baseStart_305724 := by decide
  rcases family_descends (prefixWord ++ tailWord_305724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305783 : List Nat := [1, 1, 3, 1, 1, 3, 4, 3, 3]
def baseStart_305783 : Nat := 118140960795 + 305783 * 2 ^ 59
def prefixEnd_305783 : Nat := 4983230072969 + 3 ^ 40 * 305783 * 2
def baseEnd_305783 : Nat := 139567693310117650049987

theorem tailTrace_305783 : CollatzResearch.WordTrace tailWord_305783 prefixEnd_305783 139567693310117650049987 := by
  unfold tailWord_305783
  simp only [CollatzResearch.WordTrace]
  refine ⟨11152822251207889423778003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7435214834138592949185335 11152822251207889423778003)
  ·
    refine ⟨16729233376811834135667005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11152822251207889423778003 16729233376811834135667005)
    ·
      refine ⟨6273462516304437800875127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16729233376811834135667005 6273462516304437800875127)
      ·
        refine ⟨9410193774456656701312691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6273462516304437800875127 9410193774456656701312691)
        ·
          refine ⟨14115290661684985051969037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9410193774456656701312691 14115290661684985051969037)
          ·
            refine ⟨5293233998131869394488389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14115290661684985051969037 5293233998131869394488389)
            ·
              refine ⟨992481374649725511466573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5293233998131869394488389 992481374649725511466573)
              ·
                refine ⟨372180515493647066799965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 992481374649725511466573 372180515493647066799965)
                ·
                  refine ⟨139567693310117650049987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 372180515493647066799965 139567693310117650049987)
                  ·
                    rfl

theorem cell20_305783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 3, 3].length) (baseStart_305783 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_305783 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_305783 prefixEnd_305783 := by exact prefixLift 305783
  have htrace : WordTrace (prefixWord ++ tailWord_305783) baseStart_305783 baseEnd_305783 := by
    simpa [prefixWord, tailWord_305783, baseEnd_305783] using wordTrace_append hprefix tailTrace_305783
  have hstable : (prefixWord ++ tailWord_305783).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305783).length < 2 ^ (prefixWord ++ tailWord_305783).sum := by decide
  have hdescent : baseEnd_305783 < baseStart_305783 := by decide
  rcases family_descends (prefixWord ++ tailWord_305783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305845 : List Nat := [1, 3, 3, 3, 1, 1, 2, 2, 4]
def baseStart_305845 : Nat := 118140960795 + 305845 * 2 ^ 59
def prefixEnd_305845 : Nat := 4983230072969 + 3 ^ 40 * 305845 * 2
def baseEnd_305845 : Nat := 139595991799520989983067

theorem tailTrace_305845 : CollatzResearch.WordTrace tailWord_305845 prefixEnd_305845 139595991799520989983067 := by
  unfold tailWord_305845
  simp only [CollatzResearch.WordTrace]
  refine ⟨11155083576983274012534989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7436722384655516008356659 11155083576983274012534989)
  ·
    refine ⟨4183156341368727754700621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11155083576983274012534989 4183156341368727754700621)
    ·
      refine ⟨1568683628013272908012733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4183156341368727754700621 1568683628013272908012733)
      ·
        refine ⟨588256360504977340504775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1568683628013272908012733 588256360504977340504775)
        ·
          refine ⟨882384540757466010757163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 588256360504977340504775 882384540757466010757163)
          ·
            refine ⟨1323576811136199016135745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 882384540757466010757163 1323576811136199016135745)
            ·
              refine ⟨992682608352149262101809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1323576811136199016135745 992682608352149262101809)
              ·
                refine ⟨744511956264111946576357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 992682608352149262101809 744511956264111946576357)
                ·
                  refine ⟨139595991799520989983067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 744511956264111946576357 139595991799520989983067)
                  ·
                    rfl

theorem cell20_305845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 2, 4].length) (baseStart_305845 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_305845 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_305845 prefixEnd_305845 := by exact prefixLift 305845
  have htrace : WordTrace (prefixWord ++ tailWord_305845) baseStart_305845 baseEnd_305845 := by
    simpa [prefixWord, tailWord_305845, baseEnd_305845] using wordTrace_append hprefix tailTrace_305845
  have hstable : (prefixWord ++ tailWord_305845).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305845).length < 2 ^ (prefixWord ++ tailWord_305845).sum := by decide
  have hdescent : baseEnd_305845 < baseStart_305845 := by decide
  rcases family_descends (prefixWord ++ tailWord_305845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305893 : List Nat := [1, 3, 1, 4, 1, 4, 2, 1, 3]
def baseStart_305893 : Nat := 118140960795 + 305893 * 2 ^ 59
def prefixEnd_305893 : Nat := 4983230072969 + 3 ^ 40 * 305893 * 2
def baseEnd_305893 : Nat := 139617900307446156382871

theorem tailTrace_305893 : CollatzResearch.WordTrace tailWord_305893 prefixEnd_305893 139617900307446156382871 := by
  unfold tailWord_305893
  simp only [CollatzResearch.WordTrace]
  refine ⟨11156834280809378210282333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7437889520539585473521555 11156834280809378210282333)
  ·
    refine ⟨4183812855303516828855875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11156834280809378210282333 4183812855303516828855875)
    ·
      refine ⟨6275719282955275243283813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4183812855303516828855875 6275719282955275243283813)
      ·
        refine ⟨1176697365554114108115715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6275719282955275243283813 1176697365554114108115715)
        ·
          refine ⟨1765046048331171162173573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1176697365554114108115715 1765046048331171162173573)
          ·
            refine ⟨330946134062094592907545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1765046048331171162173573 330946134062094592907545)
            ·
              refine ⟨248209600546570944680659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 330946134062094592907545 248209600546570944680659)
              ·
                refine ⟨372314400819856417020989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 248209600546570944680659 372314400819856417020989)
                ·
                  refine ⟨139617900307446156382871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 372314400819856417020989 139617900307446156382871)
                  ·
                    rfl

theorem cell20_305893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 2, 1, 3].length) (baseStart_305893 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_305893 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_305893 prefixEnd_305893 := by exact prefixLift 305893
  have htrace : WordTrace (prefixWord ++ tailWord_305893) baseStart_305893 baseEnd_305893 := by
    simpa [prefixWord, tailWord_305893, baseEnd_305893] using wordTrace_append hprefix tailTrace_305893
  have hstable : (prefixWord ++ tailWord_305893).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305893).length < 2 ^ (prefixWord ++ tailWord_305893).sum := by decide
  have hdescent : baseEnd_305893 < baseStart_305893 := by decide
  rcases family_descends (prefixWord ++ tailWord_305893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305921 : List Nat := [1, 2, 4, 1, 1, 1, 1, 7, 2]
def baseStart_305921 : Nat := 118140960795 + 305921 * 2 ^ 59
def prefixEnd_305921 : Nat := 4983230072969 + 3 ^ 40 * 305921 * 2
def baseEnd_305921 : Nat := 139630680270402503449423

theorem tailTrace_305921 : CollatzResearch.WordTrace tailWord_305921 prefixEnd_305921 139630680270402503449423 := by
  unfold tailWord_305921
  simp only [CollatzResearch.WordTrace]
  refine ⟨11157855524707938992301617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7438570349805292661534411 11157855524707938992301617)
  ·
    refine ⟨8368391643530954244226213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11157855524707938992301617 8368391643530954244226213)
    ·
      refine ⟨1569073433162053920792415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8368391643530954244226213 1569073433162053920792415)
      ·
        refine ⟨2353610149743080881188623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1569073433162053920792415 2353610149743080881188623)
        ·
          refine ⟨3530415224614621321782935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2353610149743080881188623 3530415224614621321782935)
          ·
            refine ⟨5295622836921931982674403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3530415224614621321782935 5295622836921931982674403)
            ·
              refine ⟨7943434255382897974011605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5295622836921931982674403 7943434255382897974011605)
              ·
                refine ⟨186174240360536671265897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 7943434255382897974011605 186174240360536671265897)
                ·
                  refine ⟨139630680270402503449423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 186174240360536671265897 139630680270402503449423)
                  ·
                    rfl

theorem cell20_305921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 7, 2].length) (baseStart_305921 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_305921 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_305921 prefixEnd_305921 := by exact prefixLift 305921
  have htrace : WordTrace (prefixWord ++ tailWord_305921) baseStart_305921 baseEnd_305921 := by
    simpa [prefixWord, tailWord_305921, baseEnd_305921] using wordTrace_append hprefix tailTrace_305921
  have hstable : (prefixWord ++ tailWord_305921).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305921).length < 2 ^ (prefixWord ++ tailWord_305921).sum := by decide
  have hdescent : baseEnd_305921 < baseStart_305921 := by decide
  rcases family_descends (prefixWord ++ tailWord_305921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305935 : List Nat := [1, 1, 2, 1, 1, 1, 8, 2, 3]
def baseStart_305935 : Nat := 118140960795 + 305935 * 2 ^ 59
def prefixEnd_305935 : Nat := 4983230072969 + 3 ^ 40 * 305935 * 2
def baseEnd_305935 : Nat := 139637070251880676982699

theorem tailTrace_305935 : CollatzResearch.WordTrace tailWord_305935 prefixEnd_305935 139637070251880676982699 := by
  unfold tailWord_305935
  simp only [CollatzResearch.WordTrace]
  refine ⟨11158366146657219383311259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7438910764438146255540839 11158366146657219383311259)
  ·
    refine ⟨16737549219985829074966889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11158366146657219383311259 16737549219985829074966889)
    ·
      refine ⟨12553161914989371806225167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16737549219985829074966889 12553161914989371806225167)
      ·
        refine ⟨18829742872484057709337751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12553161914989371806225167 18829742872484057709337751)
        ·
          refine ⟨28244614308726086564006627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18829742872484057709337751 28244614308726086564006627)
          ·
            refine ⟨42366921463089129846009941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28244614308726086564006627 42366921463089129846009941)
            ·
              refine ⟨496487360895575740382929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 42366921463089129846009941 496487360895575740382929)
              ·
                refine ⟨372365520671681805287197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 496487360895575740382929 372365520671681805287197)
                ·
                  refine ⟨139637070251880676982699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 372365520671681805287197 139637070251880676982699)
                  ·
                    rfl

theorem cell20_305935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 8, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 8, 2, 3].length) (baseStart_305935 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_305935 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_305935 prefixEnd_305935 := by exact prefixLift 305935
  have htrace : WordTrace (prefixWord ++ tailWord_305935) baseStart_305935 baseEnd_305935 := by
    simpa [prefixWord, tailWord_305935, baseEnd_305935] using wordTrace_append hprefix tailTrace_305935
  have hstable : (prefixWord ++ tailWord_305935).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305935).length < 2 ^ (prefixWord ++ tailWord_305935).sum := by decide
  have hdescent : baseEnd_305935 < baseStart_305935 := by decide
  rcases family_descends (prefixWord ++ tailWord_305935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305962 : List Nat := [3, 1, 4, 3, 1, 1, 3, 4]
def baseStart_305962 : Nat := 118140960795 + 305962 * 2 ^ 59
def prefixEnd_305962 : Nat := 4983230072969 + 3 ^ 40 * 305962 * 2
def baseEnd_305962 : Nat := 46549797929196194360863

theorem tailTrace_305962 : CollatzResearch.WordTrace tailWord_305962 prefixEnd_305962 46549797929196194360863 := by
  unfold tailWord_305962
  simp only [CollatzResearch.WordTrace]
  refine ⟨2789837729389850748636035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7439567278372935329696093 2789837729389850748636035)
  ·
    refine ⟨4184756594084776122954053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2789837729389850748636035 4184756594084776122954053)
    ·
      refine ⟨784641861390895523053885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4184756594084776122954053 784641861390895523053885)
      ·
        refine ⟨294240698021585821145207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 784641861390895523053885 294240698021585821145207)
        ·
          refine ⟨441361047032378731717811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 294240698021585821145207 441361047032378731717811)
          ·
            refine ⟨662041570548568097576717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 441361047032378731717811 662041570548568097576717)
            ·
              refine ⟨248265588955713036591269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 662041570548568097576717 248265588955713036591269)
              ·
                refine ⟨46549797929196194360863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 248265588955713036591269 46549797929196194360863)
                ·
                  rfl

theorem cell20_305962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 3, 4].length) (baseStart_305962 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_305962 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_305962 prefixEnd_305962 := by exact prefixLift 305962
  have htrace : WordTrace (prefixWord ++ tailWord_305962) baseStart_305962 baseEnd_305962 := by
    simpa [prefixWord, tailWord_305962, baseEnd_305962] using wordTrace_append hprefix tailTrace_305962
  have hstable : (prefixWord ++ tailWord_305962).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305962).length < 2 ^ (prefixWord ++ tailWord_305962).sum := by decide
  have hdescent : baseEnd_305962 < baseStart_305962 := by decide
  rcases family_descends (prefixWord ++ tailWord_305962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_305963 : List Nat := [1, 1, 1, 1, 2, 1, 2, 5, 6]
def baseStart_305963 : Nat := 118140960795 + 305963 * 2 ^ 59
def prefixEnd_305963 : Nat := 4983230072969 + 3 ^ 40 * 305963 * 2
def baseEnd_305963 : Nat := 139649850214837024049251

theorem tailTrace_305963 : CollatzResearch.WordTrace tailWord_305963 prefixEnd_305963 139649850214837024049251 := by
  unfold tailWord_305963
  simp only [CollatzResearch.WordTrace]
  refine ⟨11159387390555780165330543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7439591593703853443553695 11159387390555780165330543)
  ·
    refine ⟨16739081085833670247995815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11159387390555780165330543 16739081085833670247995815)
    ·
      refine ⟨25108621628750505371993723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16739081085833670247995815 25108621628750505371993723)
      ·
        refine ⟨37662932443125758057990585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25108621628750505371993723 37662932443125758057990585)
        ·
          refine ⟨28247199332344318543492939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37662932443125758057990585 28247199332344318543492939)
          ·
            refine ⟨42370798998516477815239409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28247199332344318543492939 42370798998516477815239409)
            ·
              refine ⟨31778099248887358361429557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42370798998516477815239409 31778099248887358361429557)
              ·
                refine ⟨2979196804583189846384021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31778099248887358361429557 2979196804583189846384021)
                ·
                  refine ⟨139649850214837024049251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2979196804583189846384021 139649850214837024049251)
                  ·
                    rfl

theorem cell20_305963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 5, 6].length) (baseStart_305963 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_305963 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_305963 prefixEnd_305963 := by exact prefixLift 305963
  have htrace : WordTrace (prefixWord ++ tailWord_305963) baseStart_305963 baseEnd_305963 := by
    simpa [prefixWord, tailWord_305963, baseEnd_305963] using wordTrace_append hprefix tailTrace_305963
  have hstable : (prefixWord ++ tailWord_305963).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_305963).length < 2 ^ (prefixWord ++ tailWord_305963).sum := by decide
  have hdescent : baseEnd_305963 < baseStart_305963 := by decide
  rcases family_descends (prefixWord ++ tailWord_305963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306032 : List Nat := [2, 1, 1, 1, 4, 1, 3, 2, 5]
def baseStart_306032 : Nat := 118140960795 + 306032 * 2 ^ 59
def prefixEnd_306032 : Nat := 4983230072969 + 3 ^ 40 * 306032 * 2
def baseEnd_306032 : Nat := 139681343694979450748969

theorem tailTrace_306032 : CollatzResearch.WordTrace tailWord_306032 prefixEnd_306032 139681343694979450748969 := by
  unfold tailWord_306032
  simp only [CollatzResearch.WordTrace]
  refine ⟨5580952013652902474796175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7441269351537203299728233 5580952013652902474796175)
  ·
    refine ⟨8371428020479353712194263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5580952013652902474796175 8371428020479353712194263)
    ·
      refine ⟨12557142030719030568291395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8371428020479353712194263 12557142030719030568291395)
      ·
        refine ⟨18835713046078545852437093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12557142030719030568291395 18835713046078545852437093)
        ·
          refine ⟨3531696196139727347331955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18835713046078545852437093 3531696196139727347331955)
          ·
            refine ⟨5297544294209591020997933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3531696196139727347331955 5297544294209591020997933)
            ·
              refine ⟨1986579110328596632874225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5297544294209591020997933 1986579110328596632874225)
              ·
                refine ⟨1489934332746447474655669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1986579110328596632874225 1489934332746447474655669)
                ·
                  refine ⟨139681343694979450748969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1489934332746447474655669 139681343694979450748969)
                  ·
                    rfl

theorem cell20_306032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 2, 5].length) (baseStart_306032 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_306032 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_306032 prefixEnd_306032 := by exact prefixLift 306032
  have htrace : WordTrace (prefixWord ++ tailWord_306032) baseStart_306032 baseEnd_306032 := by
    simpa [prefixWord, tailWord_306032, baseEnd_306032] using wordTrace_append hprefix tailTrace_306032
  have hstable : (prefixWord ++ tailWord_306032).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306032).length < 2 ^ (prefixWord ++ tailWord_306032).sum := by decide
  have hdescent : baseEnd_306032 < baseStart_306032 := by decide
  rcases family_descends (prefixWord ++ tailWord_306032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306035 : List Nat := [1, 1, 1, 2, 2, 1, 7, 3, 2]
def baseStart_306035 : Nat := 118140960795 + 306035 * 2 ^ 59
def prefixEnd_306035 : Nat := 4983230072969 + 3 ^ 40 * 306035 * 2
def baseEnd_306035 : Nat := 139682712976724773648957

theorem tailTrace_306035 : CollatzResearch.WordTrace tailWord_306035 prefixEnd_306035 139682712976724773648957 := by
  unfold tailWord_306035
  simp only [CollatzResearch.WordTrace]
  refine ⟨11162013446294936461951559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7441342297529957641301039 11162013446294936461951559)
  ·
    refine ⟨16743020169442404692927339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11162013446294936461951559 16743020169442404692927339)
    ·
      refine ⟨25114530254163607039391009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16743020169442404692927339 25114530254163607039391009)
      ·
        refine ⟨18835897690622705279543257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25114530254163607039391009 18835897690622705279543257)
        ·
          refine ⟨14126923267967028959657443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18835897690622705279543257 14126923267967028959657443)
          ·
            refine ⟨21190384901950543439486165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14126923267967028959657443 21190384901950543439486165)
            ·
              refine ⟨496649646139465861862957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 21190384901950543439486165 496649646139465861862957)
              ·
                refine ⟨186243617302299698198609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 496649646139465861862957 186243617302299698198609)
                ·
                  refine ⟨139682712976724773648957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 186243617302299698198609 139682712976724773648957)
                  ·
                    rfl

theorem cell20_306035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 7, 3, 2].length) (baseStart_306035 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_306035 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_306035 prefixEnd_306035 := by exact prefixLift 306035
  have htrace : WordTrace (prefixWord ++ tailWord_306035) baseStart_306035 baseEnd_306035 := by
    simpa [prefixWord, tailWord_306035, baseEnd_306035] using wordTrace_append hprefix tailTrace_306035
  have hstable : (prefixWord ++ tailWord_306035).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306035).length < 2 ^ (prefixWord ++ tailWord_306035).sum := by decide
  have hdescent : baseEnd_306035 < baseStart_306035 := by decide
  rcases family_descends (prefixWord ++ tailWord_306035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306039 : List Nat := [1, 1, 3, 1, 1, 2, 1, 4, 6]
def baseStart_306039 : Nat := 118140960795 + 306039 * 2 ^ 59
def prefixEnd_306039 : Nat := 4983230072969 + 3 ^ 40 * 306039 * 2
def baseEnd_306039 : Nat := 139684538685718537515607

theorem tailTrace_306039 : CollatzResearch.WordTrace tailWord_306039 prefixEnd_306039 139684538685718537515607 := by
  unfold tailWord_306039
  simp only [CollatzResearch.WordTrace]
  refine ⟨11162159338280445145097171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7441439558853630096731447 11162159338280445145097171)
  ·
    refine ⟨16743239007420667717645757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11162159338280445145097171 16743239007420667717645757)
    ·
      refine ⟨6278714627782750394117159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16743239007420667717645757 6278714627782750394117159)
      ·
        refine ⟨9418071941674125591175739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6278714627782750394117159 9418071941674125591175739)
        ·
          refine ⟨14127107912511188386763609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9418071941674125591175739 14127107912511188386763609)
          ·
            refine ⟨10595330934383391290072707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14127107912511188386763609 10595330934383391290072707)
            ·
              refine ⟨15892996401575086935109061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10595330934383391290072707 15892996401575086935109061)
              ·
                refine ⟨2979936825295328800332949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15892996401575086935109061 2979936825295328800332949)
                ·
                  refine ⟨139684538685718537515607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2979936825295328800332949 139684538685718537515607)
                  ·
                    rfl

theorem cell20_306039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 4, 6].length) (baseStart_306039 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_306039 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_306039 prefixEnd_306039 := by exact prefixLift 306039
  have htrace : WordTrace (prefixWord ++ tailWord_306039) baseStart_306039 baseEnd_306039 := by
    simpa [prefixWord, tailWord_306039, baseEnd_306039] using wordTrace_append hprefix tailTrace_306039
  have hstable : (prefixWord ++ tailWord_306039).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306039).length < 2 ^ (prefixWord ++ tailWord_306039).sum := by decide
  have hdescent : baseEnd_306039 < baseStart_306039 := by decide
  rcases family_descends (prefixWord ++ tailWord_306039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306132 : List Nat := [2, 4, 1, 2, 1, 2, 1, 1, 6]
def baseStart_306132 : Nat := 118140960795 + 306132 * 2 ^ 59
def prefixEnd_306132 : Nat := 4983230072969 + 3 ^ 40 * 306132 * 2
def baseEnd_306132 : Nat := 139726986419823547415227

theorem tailTrace_306132 : CollatzResearch.WordTrace tailWord_306132 prefixEnd_306132 139726986419823547415227 := by
  unfold tailWord_306132
  simp only [CollatzResearch.WordTrace]
  refine ⟨5582775663471761014116325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7443700884629014685488433 5582775663471761014116325)
  ·
    refine ⟨1046770436900955190146811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5582775663471761014116325 1046770436900955190146811)
    ·
      refine ⟨1570155655351432785220217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1046770436900955190146811 1570155655351432785220217)
      ·
        refine ⟨1177616741513574588915163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1570155655351432785220217 1177616741513574588915163)
        ·
          refine ⟨1766425112270361883372745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1177616741513574588915163 1766425112270361883372745)
          ·
            refine ⟨1324818834202771412529559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1766425112270361883372745 1324818834202771412529559)
            ·
              refine ⟨1987228251304157118794339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1324818834202771412529559 1987228251304157118794339)
              ·
                refine ⟨2980842376956235678191509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1987228251304157118794339 2980842376956235678191509)
                ·
                  refine ⟨139726986419823547415227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2980842376956235678191509 139726986419823547415227)
                  ·
                    rfl

theorem cell20_306132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_306132 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_306132 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_306132 prefixEnd_306132 := by exact prefixLift 306132
  have htrace : WordTrace (prefixWord ++ tailWord_306132) baseStart_306132 baseEnd_306132 := by
    simpa [prefixWord, tailWord_306132, baseEnd_306132] using wordTrace_append hprefix tailTrace_306132
  have hstable : (prefixWord ++ tailWord_306132).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306132).length < 2 ^ (prefixWord ++ tailWord_306132).sum := by decide
  have hdescent : baseEnd_306132 < baseStart_306132 := by decide
  rcases family_descends (prefixWord ++ tailWord_306132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306166 : List Nat := [5, 1, 1, 1, 3, 1, 2, 4, 2]
def baseStart_306166 : Nat := 118140960795 + 306166 * 2 ^ 59
def prefixEnd_306166 : Nat := 4983230072969 + 3 ^ 40 * 306166 * 2
def baseEnd_306166 : Nat := 139742504946270540281755

theorem tailTrace_306166 : CollatzResearch.WordTrace tailWord_306166 prefixEnd_306166 139742504946270540281755 := by
  unfold tailWord_306166
  simp only [CollatzResearch.WordTrace]
  refine ⟨697924463051271614685647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7444527605880230556646901 697924463051271614685647)
  ·
    refine ⟨1046886694576907422028471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 697924463051271614685647 1046886694576907422028471)
    ·
      refine ⟨1570330041865361133042707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1046886694576907422028471 1570330041865361133042707)
      ·
        refine ⟨2355495062798041699564061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1570330041865361133042707 2355495062798041699564061)
        ·
          refine ⟨883310648549265637336523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2355495062798041699564061 883310648549265637336523)
          ·
            refine ⟨1324965972823898456004785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 883310648549265637336523 1324965972823898456004785)
            ·
              refine ⟨993724479617923842003589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1324965972823898456004785 993724479617923842003589)
              ·
                refine ⟨186323339928360720375673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 993724479617923842003589 186323339928360720375673)
                ·
                  refine ⟨139742504946270540281755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 186323339928360720375673 139742504946270540281755)
                  ·
                    rfl

theorem cell20_306166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 4, 2].length) (baseStart_306166 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_306166 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_306166 prefixEnd_306166 := by exact prefixLift 306166
  have htrace : WordTrace (prefixWord ++ tailWord_306166) baseStart_306166 baseEnd_306166 := by
    simpa [prefixWord, tailWord_306166, baseEnd_306166] using wordTrace_append hprefix tailTrace_306166
  have hstable : (prefixWord ++ tailWord_306166).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306166).length < 2 ^ (prefixWord ++ tailWord_306166).sum := by decide
  have hdescent : baseEnd_306166 < baseStart_306166 := by decide
  rcases family_descends (prefixWord ++ tailWord_306166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306260 : List Nat := [2, 4, 1, 1, 1, 1, 2, 1, 7]
def baseStart_306260 : Nat := 118140960795 + 306260 * 2 ^ 59
def prefixEnd_306260 : Nat := 4983230072969 + 3 ^ 40 * 306260 * 2
def baseEnd_306260 : Nat := 139785409107623991148037

theorem tailTrace_306260 : CollatzResearch.WordTrace tailWord_306260 prefixEnd_306260 139785409107623991148037 := by
  unfold tailWord_306260
  simp only [CollatzResearch.WordTrace]
  refine ⟨5585109935239899944446117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7446813246986533259261489 5585109935239899944446117)
  ·
    refine ⟨1047208112857481239583647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5585109935239899944446117 1047208112857481239583647)
    ·
      refine ⟨1570812169286221859375471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1047208112857481239583647 1570812169286221859375471)
      ·
        refine ⟨2356218253929332789063207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1570812169286221859375471 2356218253929332789063207)
        ·
          refine ⟨3534327380893999183594811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2356218253929332789063207 3534327380893999183594811)
          ·
            refine ⟨5301491071340998775392217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3534327380893999183594811 5301491071340998775392217)
            ·
              refine ⟨3976118303505749081544163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5301491071340998775392217 3976118303505749081544163)
              ·
                refine ⟨5964177455258623622316245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3976118303505749081544163 5964177455258623622316245)
                ·
                  refine ⟨139785409107623991148037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5964177455258623622316245 139785409107623991148037)
                  ·
                    rfl

theorem cell20_306260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_306260 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_306260 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_306260 prefixEnd_306260 := by exact prefixLift 306260
  have htrace : WordTrace (prefixWord ++ tailWord_306260) baseStart_306260 baseEnd_306260 := by
    simpa [prefixWord, tailWord_306260, baseEnd_306260] using wordTrace_append hprefix tailTrace_306260
  have hstable : (prefixWord ++ tailWord_306260).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306260).length < 2 ^ (prefixWord ++ tailWord_306260).sum := by decide
  have hdescent : baseEnd_306260 < baseStart_306260 := by decide
  rcases family_descends (prefixWord ++ tailWord_306260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306277 : List Nat := [1, 3, 1, 3, 2, 1, 4, 2, 3]
def baseStart_306277 : Nat := 118140960795 + 306277 * 2 ^ 59
def prefixEnd_306277 : Nat := 4983230072969 + 3 ^ 40 * 306277 * 2
def baseEnd_306277 : Nat := 139793168370847487581301

theorem tailTrace_306277 : CollatzResearch.WordTrace tailWord_306277 prefixEnd_306277 139793168370847487581301 := by
  unfold tailWord_306277
  simp only [CollatzResearch.WordTrace]
  refine ⟨11170839911418211792261085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7447226607612141194840723 11170839911418211792261085)
  ·
    refine ⟨4189064966781829422097907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11170839911418211792261085 4189064966781829422097907)
    ·
      refine ⟨6283597450172744133146861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4189064966781829422097907 6283597450172744133146861)
      ·
        refine ⟨2356349043814779049930073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6283597450172744133146861 2356349043814779049930073)
        ·
          refine ⟨1767261782861084287447555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2356349043814779049930073 1767261782861084287447555)
          ·
            refine ⟨2650892674291626431171333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1767261782861084287447555 2650892674291626431171333)
            ·
              refine ⟨497042376429679955844625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2650892674291626431171333 497042376429679955844625)
              ·
                refine ⟨372781782322259966883469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 497042376429679955844625 372781782322259966883469)
                ·
                  refine ⟨139793168370847487581301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 372781782322259966883469 139793168370847487581301)
                  ·
                    rfl

theorem cell20_306277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 4, 2, 3].length) (baseStart_306277 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_306277 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_306277 prefixEnd_306277 := by exact prefixLift 306277
  have htrace : WordTrace (prefixWord ++ tailWord_306277) baseStart_306277 baseEnd_306277 := by
    simpa [prefixWord, tailWord_306277, baseEnd_306277] using wordTrace_append hprefix tailTrace_306277
  have hstable : (prefixWord ++ tailWord_306277).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306277).length < 2 ^ (prefixWord ++ tailWord_306277).sum := by decide
  have hdescent : baseEnd_306277 < baseStart_306277 := by decide
  rcases family_descends (prefixWord ++ tailWord_306277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306308 : List Nat := [2, 3, 2, 1, 2, 3, 3, 4]
def baseStart_306308 : Nat := 118140960795 + 306308 * 2 ^ 59
def prefixEnd_306308 : Nat := 4983230072969 + 3 ^ 40 * 306308 * 2
def baseEnd_306308 : Nat := 46602439205183052515947

theorem tailTrace_306308 : CollatzResearch.WordTrace tailWord_306308 prefixEnd_306308 46602439205183052515947 := by
  unfold tailWord_306308
  simp only [CollatzResearch.WordTrace]
  refine ⟨5585985287152952043319789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7447980382870602724426385 5585985287152952043319789)
  ·
    refine ⟨2094744482682357016244921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5585985287152952043319789 2094744482682357016244921)
    ·
      refine ⟨1571058362011767762183691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2094744482682357016244921 1571058362011767762183691)
      ·
        refine ⟨2356587543017651643275537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1571058362011767762183691 2356587543017651643275537)
        ·
          refine ⟨1767440657263238732456653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2356587543017651643275537 1767440657263238732456653)
          ·
            refine ⟨662790246473714524671245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1767440657263238732456653 662790246473714524671245)
            ·
              refine ⟨248546342427642946751717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 662790246473714524671245 248546342427642946751717)
              ·
                refine ⟨46602439205183052515947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 248546342427642946751717 46602439205183052515947)
                ·
                  rfl

theorem cell20_306308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 3, 4].length) (baseStart_306308 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_306308 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_306308 prefixEnd_306308 := by exact prefixLift 306308
  have htrace : WordTrace (prefixWord ++ tailWord_306308) baseStart_306308 baseEnd_306308 := by
    simpa [prefixWord, tailWord_306308, baseEnd_306308] using wordTrace_append hprefix tailTrace_306308
  have hstable : (prefixWord ++ tailWord_306308).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306308).length < 2 ^ (prefixWord ++ tailWord_306308).sum := by decide
  have hdescent : baseEnd_306308 < baseStart_306308 := by decide
  rcases family_descends (prefixWord ++ tailWord_306308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306318 : List Nat := [4, 1, 1, 3, 2, 2, 2, 3, 2]
def baseStart_306318 : Nat := 118140960795 + 306318 * 2 ^ 59
def prefixEnd_306318 : Nat := 4983230072969 + 3 ^ 40 * 306318 * 2
def baseEnd_306318 : Nat := 139811881888033567214467

theorem tailTrace_306318 : CollatzResearch.WordTrace tailWord_306318 prefixEnd_306318 139811881888033567214467 := by
  unfold tailWord_306318
  simp only [CollatzResearch.WordTrace]
  refine ⟨1396541913033709474312951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7448223536179783863002405 1396541913033709474312951)
  ·
    refine ⟨2094812869550564211469427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1396541913033709474312951 2094812869550564211469427)
    ·
      refine ⟨3142219304325846317204141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2094812869550564211469427 3142219304325846317204141)
      ·
        refine ⟨1178332239122192368951553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3142219304325846317204141 1178332239122192368951553)
        ·
          refine ⟨883749179341644276713665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1178332239122192368951553 883749179341644276713665)
          ·
            refine ⟨662811884506233207535249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 883749179341644276713665 662811884506233207535249)
            ·
              refine ⟨497108913379674905651437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 662811884506233207535249 497108913379674905651437)
              ·
                refine ⟨186415842517378089619289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 497108913379674905651437 186415842517378089619289)
                ·
                  refine ⟨139811881888033567214467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 186415842517378089619289 139811881888033567214467)
                  ·
                    rfl

theorem cell20_306318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 2, 3, 2].length) (baseStart_306318 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_306318 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_306318 prefixEnd_306318 := by exact prefixLift 306318
  have htrace : WordTrace (prefixWord ++ tailWord_306318) baseStart_306318 baseEnd_306318 := by
    simpa [prefixWord, tailWord_306318, baseEnd_306318] using wordTrace_append hprefix tailTrace_306318
  have hstable : (prefixWord ++ tailWord_306318).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306318).length < 2 ^ (prefixWord ++ tailWord_306318).sum := by decide
  have hdescent : baseEnd_306318 < baseStart_306318 := by decide
  rcases family_descends (prefixWord ++ tailWord_306318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306332 : List Nat := [2, 2, 3, 2, 1, 4, 1, 2, 3]
def baseStart_306332 : Nat := 118140960795 + 306332 * 2 ^ 59
def prefixEnd_306332 : Nat := 4983230072969 + 3 ^ 40 * 306332 * 2
def baseEnd_306332 : Nat := 139818271869511740747743

theorem tailTrace_306332 : CollatzResearch.WordTrace tailWord_306332 prefixEnd_306332 139818271869511740747743 := by
  unfold tailWord_306332
  simp only [CollatzResearch.WordTrace]
  refine ⟨5586422963109478092756625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7448563950812637457008833 5586422963109478092756625)
  ·
    refine ⟨4189817222332108569567469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5586422963109478092756625 4189817222332108569567469)
    ·
      refine ⟨1571181458374540713587801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4189817222332108569567469 1571181458374540713587801)
      ·
        refine ⟨1178386093780905535190851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1571181458374540713587801 1178386093780905535190851)
        ·
          refine ⟨1767579140671358302786277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1178386093780905535190851 1767579140671358302786277)
          ·
            refine ⟨331421088875879681772427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1767579140671358302786277 331421088875879681772427)
            ·
              refine ⟨497131633313819522658641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 331421088875879681772427 497131633313819522658641)
              ·
                refine ⟨372848724985364641993981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 497131633313819522658641 372848724985364641993981)
                ·
                  refine ⟨139818271869511740747743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 372848724985364641993981 139818271869511740747743)
                  ·
                    rfl

theorem cell20_306332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 1, 2, 3].length) (baseStart_306332 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_306332 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_306332 prefixEnd_306332 := by exact prefixLift 306332
  have htrace : WordTrace (prefixWord ++ tailWord_306332) baseStart_306332 baseEnd_306332 := by
    simpa [prefixWord, tailWord_306332, baseEnd_306332] using wordTrace_append hprefix tailTrace_306332
  have hstable : (prefixWord ++ tailWord_306332).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306332).length < 2 ^ (prefixWord ++ tailWord_306332).sum := by decide
  have hdescent : baseEnd_306332 < baseStart_306332 := by decide
  rcases family_descends (prefixWord ++ tailWord_306332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306336 : List Nat := [2, 1, 1, 4, 2, 1, 3, 1, 5]
def baseStart_306336 : Nat := 118140960795 + 306336 * 2 ^ 59
def prefixEnd_306336 : Nat := 4983230072969 + 3 ^ 40 * 306336 * 2
def baseEnd_306336 : Nat := 139820097578505504614393

theorem tailTrace_306336 : CollatzResearch.WordTrace tailWord_306336 prefixEnd_306336 139820097578505504614393 := by
  unfold tailWord_306336
  simp only [CollatzResearch.WordTrace]
  refine ⟨5586495909102232434329431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7448661212136309912439241 5586495909102232434329431)
  ·
    refine ⟨8379743863653348651494147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5586495909102232434329431 8379743863653348651494147)
    ·
      refine ⟨12569615795480022977241221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8379743863653348651494147 12569615795480022977241221)
      ·
        refine ⟨2356802961652504308232729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12569615795480022977241221 2356802961652504308232729)
        ·
          refine ⟨1767602221239378231174547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2356802961652504308232729 1767602221239378231174547)
          ·
            refine ⟨2651403331859067346761821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1767602221239378231174547 2651403331859067346761821)
            ·
              refine ⟨994276249447150255035683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2651403331859067346761821 994276249447150255035683)
              ·
                refine ⟨1491414374170725382553525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 994276249447150255035683 1491414374170725382553525)
                ·
                  refine ⟨139820097578505504614393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1491414374170725382553525 139820097578505504614393)
                  ·
                    rfl

theorem cell20_306336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 1, 5].length) (baseStart_306336 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_306336 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_306336 prefixEnd_306336 := by exact prefixLift 306336
  have htrace : WordTrace (prefixWord ++ tailWord_306336) baseStart_306336 baseEnd_306336 := by
    simpa [prefixWord, tailWord_306336, baseEnd_306336] using wordTrace_append hprefix tailTrace_306336
  have hstable : (prefixWord ++ tailWord_306336).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306336).length < 2 ^ (prefixWord ++ tailWord_306336).sum := by decide
  have hdescent : baseEnd_306336 < baseStart_306336 := by decide
  rcases family_descends (prefixWord ++ tailWord_306336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306349 : List Nat := [1, 5, 2, 1, 3, 1, 3, 1, 3]
def baseStart_306349 : Nat := 118140960795 + 306349 * 2 ^ 59
def prefixEnd_306349 : Nat := 4983230072969 + 3 ^ 40 * 306349 * 2
def baseEnd_306349 : Nat := 139826031132735237181007

theorem tailTrace_306349 : CollatzResearch.WordTrace tailWord_306349 prefixEnd_306349 139826031132735237181007 := by
  unfold tailWord_306349
  simp only [CollatzResearch.WordTrace]
  refine ⟨11173465967157368088882101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7448977311438245392588067 11173465967157368088882101)
  ·
    refine ⟨1047512434421003258332697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11173465967157368088882101 1047512434421003258332697)
    ·
      refine ⟨785634325815752443749523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1047512434421003258332697 785634325815752443749523)
      ·
        refine ⟨1178451488723628665624285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 785634325815752443749523 1178451488723628665624285)
        ·
          refine ⟨441919308271360749609107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1178451488723628665624285 441919308271360749609107)
          ·
            refine ⟨662878962407041124413661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 441919308271360749609107 662878962407041124413661)
            ·
              refine ⟨248579610902640421655123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 662878962407041124413661 248579610902640421655123)
              ·
                refine ⟨372869416353960632482685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 248579610902640421655123 372869416353960632482685)
                ·
                  refine ⟨139826031132735237181007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 372869416353960632482685 139826031132735237181007)
                  ·
                    rfl

theorem cell20_306349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 3, 1, 3].length) (baseStart_306349 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_306349 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_306349 prefixEnd_306349 := by exact prefixLift 306349
  have htrace : WordTrace (prefixWord ++ tailWord_306349) baseStart_306349 baseEnd_306349 := by
    simpa [prefixWord, tailWord_306349, baseEnd_306349] using wordTrace_append hprefix tailTrace_306349
  have hstable : (prefixWord ++ tailWord_306349).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306349).length < 2 ^ (prefixWord ++ tailWord_306349).sum := by decide
  have hdescent : baseEnd_306349 < baseStart_306349 := by decide
  rcases family_descends (prefixWord ++ tailWord_306349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306367 : List Nat := [1, 1, 2, 2, 2, 2, 6, 4]
def baseStart_306367 : Nat := 118140960795 + 306367 * 2 ^ 59
def prefixEnd_306367 : Nat := 4983230072969 + 3 ^ 40 * 306367 * 2
def baseEnd_306367 : Nat := 46611415607735724860311

theorem tailTrace_306367 : CollatzResearch.WordTrace tailWord_306367 prefixEnd_306367 46611415607735724860311 := by
  unfold tailWord_306367
  simp only [CollatzResearch.WordTrace]
  refine ⟨11174122481092157163037355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7449414987394771442024903 11174122481092157163037355)
  ·
    refine ⟨16761183721638235744556033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11174122481092157163037355 16761183721638235744556033)
    ·
      refine ⟨12570887791228676808417025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16761183721638235744556033 12570887791228676808417025)
      ·
        refine ⟨9428165843421507606312769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12570887791228676808417025 9428165843421507606312769)
        ·
          refine ⟨7071124382566130704734577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9428165843421507606312769 7071124382566130704734577)
          ·
            refine ⟨5303343286924598028550933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7071124382566130704734577 5303343286924598028550933)
            ·
              refine ⟨248594216574590532588325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 5303343286924598028550933 248594216574590532588325)
              ·
                refine ⟨46611415607735724860311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 248594216574590532588325 46611415607735724860311)
                ·
                  rfl

theorem cell20_306367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 6, 4].length) (baseStart_306367 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_306367 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_306367 prefixEnd_306367 := by exact prefixLift 306367
  have htrace : WordTrace (prefixWord ++ tailWord_306367) baseStart_306367 baseEnd_306367 := by
    simpa [prefixWord, tailWord_306367, baseEnd_306367] using wordTrace_append hprefix tailTrace_306367
  have hstable : (prefixWord ++ tailWord_306367).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306367).length < 2 ^ (prefixWord ++ tailWord_306367).sum := by decide
  have hdescent : baseEnd_306367 < baseStart_306367 := by decide
  rcases family_descends (prefixWord ++ tailWord_306367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306390 : List Nat := [5, 2, 1, 2, 2, 1, 3, 2, 2]
def baseStart_306390 : Nat := 118140960795 + 306390 * 2 ^ 59
def prefixEnd_306390 : Nat := 4983230072969 + 3 ^ 40 * 306390 * 2
def baseEnd_306390 : Nat := 139844744649921316814173

theorem tailTrace_306390 : CollatzResearch.WordTrace tailWord_306390 prefixEnd_306390 139844744649921316814173 := by
  unfold tailWord_306390
  simp only [CollatzResearch.WordTrace]
  refine ⟨698435085000552005695289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7449974240005888060749749 698435085000552005695289)
  ·
    refine ⟨523826313750414004271467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 698435085000552005695289 523826313750414004271467)
    ·
      refine ⟨785739470625621006407201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 523826313750414004271467 785739470625621006407201)
      ·
        refine ⟨589304602969215754805401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 785739470625621006407201 589304602969215754805401)
        ·
          refine ⟨441978452226911816104051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 589304602969215754805401 441978452226911816104051)
          ·
            refine ⟨662967678340367724156077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 441978452226911816104051 662967678340367724156077)
            ·
              refine ⟨248612879377637896558529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 662967678340367724156077 248612879377637896558529)
              ·
                refine ⟨186459659533228422418897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 248612879377637896558529 186459659533228422418897)
                ·
                  refine ⟨139844744649921316814173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 186459659533228422418897 139844744649921316814173)
                  ·
                    rfl

theorem cell20_306390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 3, 2, 2].length) (baseStart_306390 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_306390 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_306390 prefixEnd_306390 := by exact prefixLift 306390
  have htrace : WordTrace (prefixWord ++ tailWord_306390) baseStart_306390 baseEnd_306390 := by
    simpa [prefixWord, tailWord_306390, baseEnd_306390] using wordTrace_append hprefix tailTrace_306390
  have hstable : (prefixWord ++ tailWord_306390).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306390).length < 2 ^ (prefixWord ++ tailWord_306390).sum := by decide
  have hdescent : baseEnd_306390 < baseStart_306390 := by decide
  rcases family_descends (prefixWord ++ tailWord_306390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306395 : List Nat := [1, 1, 1, 1, 1, 1, 1, 4, 9]
def baseStart_306395 : Nat := 118140960795 + 306395 * 2 ^ 59
def prefixEnd_306395 : Nat := 4983230072969 + 3 ^ 40 * 306395 * 2
def baseEnd_306395 : Nat := 139847026786163521647485

theorem tailTrace_306395 : CollatzResearch.WordTrace tailWord_306395 prefixEnd_306395 139847026786163521647485 := by
  unfold tailWord_306395
  simp only [CollatzResearch.WordTrace]
  refine ⟨11175143724990717945056639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7450095816660478630037759 11175143724990717945056639)
  ·
    refine ⟨16762715587486076917584959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11175143724990717945056639 16762715587486076917584959)
    ·
      refine ⟨25144073381229115376377439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16762715587486076917584959 25144073381229115376377439)
      ·
        refine ⟨37716110071843673064566159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25144073381229115376377439 37716110071843673064566159)
        ·
          refine ⟨56574165107765509596849239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37716110071843673064566159 56574165107765509596849239)
          ·
            refine ⟨84861247661648264395273859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56574165107765509596849239 84861247661648264395273859)
            ·
              refine ⟨127291871492472396592910789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84861247661648264395273859 127291871492472396592910789)
              ·
                refine ⟨23867225904838574361170773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 127291871492472396592910789 23867225904838574361170773)
                ·
                  refine ⟨139847026786163521647485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 23867225904838574361170773 139847026786163521647485)
                  ·
                    rfl

theorem cell20_306395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 9].length) (baseStart_306395 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_306395 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_306395 prefixEnd_306395 := by exact prefixLift 306395
  have htrace : WordTrace (prefixWord ++ tailWord_306395) baseStart_306395 baseEnd_306395 := by
    simpa [prefixWord, tailWord_306395, baseEnd_306395] using wordTrace_append hprefix tailTrace_306395
  have hstable : (prefixWord ++ tailWord_306395).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306395).length < 2 ^ (prefixWord ++ tailWord_306395).sum := by decide
  have hdescent : baseEnd_306395 < baseStart_306395 := by decide
  rcases family_descends (prefixWord ++ tailWord_306395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306426 : List Nat := [3, 1, 1, 1, 1, 4, 1, 8]
def baseStart_306426 : Nat := 118140960795 + 306426 * 2 ^ 59
def prefixEnd_306426 : Nat := 4983230072969 + 3 ^ 40 * 306426 * 2
def baseEnd_306426 : Nat := 46620392010288397204675

theorem tailTrace_306426 : CollatzResearch.WordTrace tailWord_306426 prefixEnd_306426 46620392010288397204675 := by
  unfold tailWord_306426
  simp only [CollatzResearch.WordTrace]
  refine ⟨2794068596969602559858783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7450849591918940159623421 2794068596969602559858783)
  ·
    refine ⟨4191102895454403839788175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2794068596969602559858783 4191102895454403839788175)
    ·
      refine ⟨6286654343181605759682263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4191102895454403839788175 6286654343181605759682263)
      ·
        refine ⟨9429981514772408639523395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6286654343181605759682263 9429981514772408639523395)
        ·
          refine ⟨14144972272158612959285093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9429981514772408639523395 14144972272158612959285093)
          ·
            refine ⟨2652182301029739929865955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14144972272158612959285093 2652182301029739929865955)
            ·
              refine ⟨3978273451544609894798933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2652182301029739929865955 3978273451544609894798933)
              ·
                refine ⟨46620392010288397204675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3978273451544609894798933 46620392010288397204675)
                ·
                  rfl

theorem cell20_306426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 8].length) (baseStart_306426 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_306426 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_306426 prefixEnd_306426 := by exact prefixLift 306426
  have htrace : WordTrace (prefixWord ++ tailWord_306426) baseStart_306426 baseEnd_306426 := by
    simpa [prefixWord, tailWord_306426, baseEnd_306426] using wordTrace_append hprefix tailTrace_306426
  have hstable : (prefixWord ++ tailWord_306426).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306426).length < 2 ^ (prefixWord ++ tailWord_306426).sum := by decide
  have hdescent : baseEnd_306426 < baseStart_306426 := by decide
  rcases family_descends (prefixWord ++ tailWord_306426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306474 : List Nat := [3, 1, 4, 2, 1, 1, 1, 1, 6]
def baseStart_306474 : Nat := 118140960795 + 306474 * 2 ^ 59
def prefixEnd_306474 : Nat := 4983230072969 + 3 ^ 40 * 306474 * 2
def baseEnd_306474 : Nat := 139883084538790358013829

theorem tailTrace_306474 : CollatzResearch.WordTrace tailWord_306474 prefixEnd_306474 139883084538790358013829 := by
  unfold tailWord_306474
  simp only [CollatzResearch.WordTrace]
  refine ⟨2794506272926128609295619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7452016727803009624788317 2794506272926128609295619)
  ·
    refine ⟨4191759409389192913943429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2794506272926128609295619 4191759409389192913943429)
    ·
      refine ⟨785954889260473671364393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4191759409389192913943429 785954889260473671364393)
      ·
        refine ⟨589466166945355253523295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 785954889260473671364393 589466166945355253523295)
        ·
          refine ⟨884199250418032880284943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 589466166945355253523295 884199250418032880284943)
          ·
            refine ⟨1326298875627049320427415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 884199250418032880284943 1326298875627049320427415)
            ·
              refine ⟨1989448313440573980641123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1326298875627049320427415 1989448313440573980641123)
              ·
                refine ⟨2984172470160860970961685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1989448313440573980641123 2984172470160860970961685)
                ·
                  refine ⟨139883084538790358013829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2984172470160860970961685 139883084538790358013829)
                  ·
                    rfl

theorem cell20_306474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 1, 6].length) (baseStart_306474 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_306474 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_306474 prefixEnd_306474 := by exact prefixLift 306474
  have htrace : WordTrace (prefixWord ++ tailWord_306474) baseStart_306474 baseEnd_306474 := by
    simpa [prefixWord, tailWord_306474, baseEnd_306474] using wordTrace_append hprefix tailTrace_306474
  have hstable : (prefixWord ++ tailWord_306474).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306474).length < 2 ^ (prefixWord ++ tailWord_306474).sum := by decide
  have hdescent : baseEnd_306474 < baseStart_306474 := by decide
  rcases family_descends (prefixWord ++ tailWord_306474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306477 : List Nat := [1, 5, 3, 1, 1, 2, 3, 4]
def baseStart_306477 : Nat := 118140960795 + 306477 * 2 ^ 59
def prefixEnd_306477 : Nat := 4983230072969 + 3 ^ 40 * 306477 * 2
def baseEnd_306477 : Nat := 46628151273511893637939

theorem tailTrace_306477 : CollatzResearch.WordTrace tailWord_306477 prefixEnd_306477 46628151273511893637939 := by
  unfold tailWord_306477
  simp only [CollatzResearch.WordTrace]
  refine ⟨11178134510693645949541685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7452089673795763966361123 11178134510693645949541685)
  ·
    refine ⟨1047950110377529307769533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11178134510693645949541685 1047950110377529307769533)
    ·
      refine ⟨392981291391573490413575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1047950110377529307769533 392981291391573490413575)
      ·
        refine ⟨589471937087360235620363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 392981291391573490413575 589471937087360235620363)
        ·
          refine ⟨884207905631040353430545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 589471937087360235620363 884207905631040353430545)
          ·
            refine ⟨663155929223280265072909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 884207905631040353430545 663155929223280265072909)
            ·
              refine ⟨248683473458730099402341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 663155929223280265072909 248683473458730099402341)
              ·
                refine ⟨46628151273511893637939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 248683473458730099402341 46628151273511893637939)
                ·
                  rfl

theorem cell20_306477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 3, 4].length) (baseStart_306477 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_306477 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_306477 prefixEnd_306477 := by exact prefixLift 306477
  have htrace : WordTrace (prefixWord ++ tailWord_306477) baseStart_306477 baseEnd_306477 := by
    simpa [prefixWord, tailWord_306477, baseEnd_306477] using wordTrace_append hprefix tailTrace_306477
  have hstable : (prefixWord ++ tailWord_306477).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306477).length < 2 ^ (prefixWord ++ tailWord_306477).sum := by decide
  have hdescent : baseEnd_306477 < baseStart_306477 := by decide
  rcases family_descends (prefixWord ++ tailWord_306477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306512 : List Nat := [2, 1, 1, 1, 1, 5, 1, 6, 2]
def baseStart_306512 : Nat := 118140960795 + 306512 * 2 ^ 59
def prefixEnd_306512 : Nat := 4983230072969 + 3 ^ 40 * 306512 * 2
def baseEnd_306512 : Nat := 139900428774231114747007

theorem tailTrace_306512 : CollatzResearch.WordTrace tailWord_306512 prefixEnd_306512 139900428774231114747007 := by
  unfold tailWord_306512
  simp only [CollatzResearch.WordTrace]
  refine ⟨5589705532783423463532895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7452940710377897951377193 5589705532783423463532895)
  ·
    refine ⟨8384558299175135195299343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5589705532783423463532895 8384558299175135195299343)
    ·
      refine ⟨12576837448762702792949015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8384558299175135195299343 12576837448762702792949015)
      ·
        refine ⟨18865256173144054189423523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12576837448762702792949015 18865256173144054189423523)
        ·
          refine ⟨28297884259716081284135285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18865256173144054189423523 28297884259716081284135285)
          ·
            refine ⟨2652926649348382620387683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28297884259716081284135285 2652926649348382620387683)
            ·
              refine ⟨3979389974022573930581525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2652926649348382620387683 3979389974022573930581525)
              ·
                refine ⟨186533905032308152996009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3979389974022573930581525 186533905032308152996009)
                ·
                  refine ⟨139900428774231114747007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 186533905032308152996009 139900428774231114747007)
                  ·
                    rfl

theorem cell20_306512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 6, 2].length) (baseStart_306512 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_306512 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_306512 prefixEnd_306512 := by exact prefixLift 306512
  have htrace : WordTrace (prefixWord ++ tailWord_306512) baseStart_306512 baseEnd_306512 := by
    simpa [prefixWord, tailWord_306512, baseEnd_306512] using wordTrace_append hprefix tailTrace_306512
  have hstable : (prefixWord ++ tailWord_306512).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306512).length < 2 ^ (prefixWord ++ tailWord_306512).sum := by decide
  have hdescent : baseEnd_306512 < baseStart_306512 := by decide
  rcases family_descends (prefixWord ++ tailWord_306512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306533 : List Nat := [1, 3, 1, 3, 1, 2, 1, 4, 4]
def baseStart_306533 : Nat := 118140960795 + 306533 * 2 ^ 59
def prefixEnd_306533 : Nat := 4983230072969 + 3 ^ 40 * 306533 * 2
def baseEnd_306533 : Nat := 139910013746448375046921

theorem tailTrace_306533 : CollatzResearch.WordTrace tailWord_306533 prefixEnd_306533 139910013746448375046921 := by
  unfold tailWord_306533
  simp only [CollatzResearch.WordTrace]
  refine ⟨11180176998490767513580253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7453451332327178342386835 11180176998490767513580253)
  ·
    refine ⟨4192566374434037817592595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11180176998490767513580253 4192566374434037817592595)
    ·
      refine ⟨6288849561651056726388893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4192566374434037817592595 6288849561651056726388893)
      ·
        refine ⟨2358318585619146272395835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6288849561651056726388893 2358318585619146272395835)
        ·
          refine ⟨3537477878428719408593753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2358318585619146272395835 3537477878428719408593753)
          ·
            refine ⟨2653108408821539556445315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3537477878428719408593753 2653108408821539556445315)
            ·
              refine ⟨3979662613232309334667973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2653108408821539556445315 3979662613232309334667973)
              ·
                refine ⟨746186739981058000250245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3979662613232309334667973 746186739981058000250245)
                ·
                  refine ⟨139910013746448375046921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 746186739981058000250245 139910013746448375046921)
                  ·
                    rfl

theorem cell20_306533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 4, 4].length) (baseStart_306533 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_306533 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_306533 prefixEnd_306533 := by exact prefixLift 306533
  have htrace : WordTrace (prefixWord ++ tailWord_306533) baseStart_306533 baseEnd_306533 := by
    simpa [prefixWord, tailWord_306533, baseEnd_306533] using wordTrace_append hprefix tailTrace_306533
  have hstable : (prefixWord ++ tailWord_306533).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306533).length < 2 ^ (prefixWord ++ tailWord_306533).sum := by decide
  have hdescent : baseEnd_306533 < baseStart_306533 := by decide
  rcases family_descends (prefixWord ++ tailWord_306533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306542 : List Nat := [4, 1, 2, 4, 2, 1, 1, 3, 2]
def baseStart_306542 : Nat := 118140960795 + 306542 * 2 ^ 59
def prefixEnd_306542 : Nat := 4983230072969 + 3 ^ 40 * 306542 * 2
def baseEnd_306542 : Nat := 139914121591684343746885

theorem tailTrace_306542 : CollatzResearch.WordTrace tailWord_306542 prefixEnd_306542 139914121591684343746885 := by
  unfold tailWord_306542
  simp only [CollatzResearch.WordTrace]
  refine ⟨1397563156932270256332235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7453670170305441367105253 1397563156932270256332235)
  ·
    refine ⟨2096344735398405384498353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1397563156932270256332235 2096344735398405384498353)
    ·
      refine ⟨1572258551548804038373765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2096344735398405384498353 1572258551548804038373765)
      ·
        refine ⟨294798478415400757195081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1572258551548804038373765 294798478415400757195081)
        ·
          refine ⟨221098858811550567896311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 294798478415400757195081 221098858811550567896311)
          ·
            refine ⟨331648288217325851844467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 221098858811550567896311 331648288217325851844467)
            ·
              refine ⟨497472432325988777766701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 331648288217325851844467 497472432325988777766701)
              ·
                refine ⟨186552162122245791662513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 497472432325988777766701 186552162122245791662513)
                ·
                  refine ⟨139914121591684343746885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 186552162122245791662513 139914121591684343746885)
                  ·
                    rfl

theorem cell20_306542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 1, 3, 2].length) (baseStart_306542 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_306542 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_306542 prefixEnd_306542 := by exact prefixLift 306542
  have htrace : WordTrace (prefixWord ++ tailWord_306542) baseStart_306542 baseEnd_306542 := by
    simpa [prefixWord, tailWord_306542, baseEnd_306542] using wordTrace_append hprefix tailTrace_306542
  have hstable : (prefixWord ++ tailWord_306542).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306542).length < 2 ^ (prefixWord ++ tailWord_306542).sum := by decide
  have hdescent : baseEnd_306542 < baseStart_306542 := by decide
  rcases family_descends (prefixWord ++ tailWord_306542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306564 : List Nat := [2, 3, 2, 1, 1, 3, 2, 1, 5]
def baseStart_306564 : Nat := 118140960795 + 306564 * 2 ^ 59
def prefixEnd_306564 : Nat := 4983230072969 + 3 ^ 40 * 306564 * 2
def baseEnd_306564 : Nat := 139924162991150045013461

theorem tailTrace_306564 : CollatzResearch.WordTrace tailWord_306564 prefixEnd_306564 139924162991150045013461 := by
  unfold tailWord_306564
  simp only [CollatzResearch.WordTrace]
  refine ⟨5590653830689229903979373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7454205107585639871972497 5590653830689229903979373)
  ·
    refine ⟨2096495186508461213992265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5590653830689229903979373 2096495186508461213992265)
    ·
      refine ⟨1572371389881345910494199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2096495186508461213992265 1572371389881345910494199)
      ·
        refine ⟨2358557084822018865741299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1572371389881345910494199 2358557084822018865741299)
        ·
          refine ⟨3537835627233028298611949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2358557084822018865741299 3537835627233028298611949)
          ·
            refine ⟨1326688360212385611979481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3537835627233028298611949 1326688360212385611979481)
            ·
              refine ⟨995016270159289208984611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1326688360212385611979481 995016270159289208984611)
              ·
                refine ⟨1492524405238933813476917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 995016270159289208984611 1492524405238933813476917)
                ·
                  refine ⟨139924162991150045013461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1492524405238933813476917 139924162991150045013461)
                  ·
                    rfl

theorem cell20_306564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 1, 5].length) (baseStart_306564 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_306564 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_306564 prefixEnd_306564 := by exact prefixLift 306564
  have htrace : WordTrace (prefixWord ++ tailWord_306564) baseStart_306564 baseEnd_306564 := by
    simpa [prefixWord, tailWord_306564, baseEnd_306564] using wordTrace_append hprefix tailTrace_306564
  have hstable : (prefixWord ++ tailWord_306564).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306564).length < 2 ^ (prefixWord ++ tailWord_306564).sum := by decide
  have hdescent : baseEnd_306564 < baseStart_306564 := by decide
  rcases family_descends (prefixWord ++ tailWord_306564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306574 : List Nat := [4, 1, 1, 4, 2, 1, 2, 5]
def baseStart_306574 : Nat := 118140960795 + 306574 * 2 ^ 59
def prefixEnd_306574 : Nat := 4983230072969 + 3 ^ 40 * 306574 * 2
def baseEnd_306574 : Nat := 46642909087878151560029

theorem tailTrace_306574 : CollatzResearch.WordTrace tailWord_306574 prefixEnd_306574 46642909087878151560029 := by
  unfold tailWord_306574
  simp only [CollatzResearch.WordTrace]
  refine ⟨1397709048917778939477847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7454448260894821010548517 1397709048917778939477847)
  ·
    refine ⟨2096563573376668409216771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1397709048917778939477847 2096563573376668409216771)
    ·
      refine ⟨3144845360065002613825157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2096563573376668409216771 3144845360065002613825157)
      ·
        refine ⟨589658505012187990092217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3144845360065002613825157 589658505012187990092217)
        ·
          refine ⟨442243878759140992569163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 589658505012187990092217 442243878759140992569163)
          ·
            refine ⟨663365818138711488853745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 442243878759140992569163 663365818138711488853745)
            ·
              refine ⟨497524363604033616640309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 663365818138711488853745 497524363604033616640309)
              ·
                refine ⟨46642909087878151560029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 497524363604033616640309 46642909087878151560029)
                ·
                  rfl

theorem cell20_306574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 2, 5].length) (baseStart_306574 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_306574 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_306574 prefixEnd_306574 := by exact prefixLift 306574
  have htrace : WordTrace (prefixWord ++ tailWord_306574) baseStart_306574 baseEnd_306574 := by
    simpa [prefixWord, tailWord_306574, baseEnd_306574] using wordTrace_append hprefix tailTrace_306574
  have hstable : (prefixWord ++ tailWord_306574).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306574).length < 2 ^ (prefixWord ++ tailWord_306574).sum := by decide
  have hdescent : baseEnd_306574 < baseStart_306574 := by decide
  rcases family_descends (prefixWord ++ tailWord_306574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306581 : List Nat := [1, 3, 2, 1, 1, 2, 6, 1, 3]
def baseStart_306581 : Nat := 118140960795 + 306581 * 2 ^ 59
def prefixEnd_306581 : Nat := 4983230072969 + 3 ^ 40 * 306581 * 2
def baseEnd_306581 : Nat := 139931922254373541446725

theorem tailTrace_306581 : CollatzResearch.WordTrace tailWord_306581 prefixEnd_306581 139931922254373541446725 := by
  unfold tailWord_306581
  simp only [CollatzResearch.WordTrace]
  refine ⟨11181927702316871711327597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7454618468211247807551731 11181927702316871711327597)
  ·
    refine ⟨4193222888368826891747849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11181927702316871711327597 4193222888368826891747849)
    ·
      refine ⟨3144917166276620168810887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4193222888368826891747849 3144917166276620168810887)
      ·
        refine ⟨4717375749414930253216331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3144917166276620168810887 4717375749414930253216331)
        ·
          refine ⟨7076063624122395379824497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4717375749414930253216331 7076063624122395379824497)
          ·
            refine ⟨5307047718091796534868373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7076063624122395379824497 5307047718091796534868373)
            ·
              refine ⟨248767861785552962571955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 5307047718091796534868373 248767861785552962571955)
              ·
                refine ⟨373151792678329443857933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 248767861785552962571955 373151792678329443857933)
                ·
                  refine ⟨139931922254373541446725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 373151792678329443857933 139931922254373541446725)
                  ·
                    rfl

theorem cell20_306581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 6, 1, 3].length) (baseStart_306581 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_306581 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_306581 prefixEnd_306581 := by exact prefixLift 306581
  have htrace : WordTrace (prefixWord ++ tailWord_306581) baseStart_306581 baseEnd_306581 := by
    simpa [prefixWord, tailWord_306581, baseEnd_306581] using wordTrace_append hprefix tailTrace_306581
  have hstable : (prefixWord ++ tailWord_306581).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306581).length < 2 ^ (prefixWord ++ tailWord_306581).sum := by decide
  have hdescent : baseEnd_306581 < baseStart_306581 := by decide
  rcases family_descends (prefixWord ++ tailWord_306581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306623 : List Nat := [1, 1, 2, 2, 2, 1, 1, 5, 5]
def baseStart_306623 : Nat := 118140960795 + 306623 * 2 ^ 59
def prefixEnd_306623 : Nat := 4983230072969 + 3 ^ 40 * 306623 * 2
def baseEnd_306623 : Nat := 139951092198808062046553

theorem tailTrace_306623 : CollatzResearch.WordTrace tailWord_306623 prefixEnd_306623 139951092198808062046553 := by
  unfold tailWord_306623
  simp only [CollatzResearch.WordTrace]
  refine ⟨11183459568164712884356523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7455639712109808589571015 11183459568164712884356523)
  ·
    refine ⟨16775189352247069326534785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11183459568164712884356523 16775189352247069326534785)
    ·
      refine ⟨12581392014185301994901089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16775189352247069326534785 12581392014185301994901089)
      ·
        refine ⟨9436044010638976496175817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12581392014185301994901089 9436044010638976496175817)
        ·
          refine ⟨7077033007979232372131863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9436044010638976496175817 7077033007979232372131863)
          ·
            refine ⟨10615549511968848558197795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7077033007979232372131863 10615549511968848558197795)
            ·
              refine ⟨15923324267953272837296693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10615549511968848558197795 15923324267953272837296693)
              ·
                refine ⟨1492811650120619328496565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15923324267953272837296693 1492811650120619328496565)
                ·
                  refine ⟨139951092198808062046553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1492811650120619328496565 139951092198808062046553)
                  ·
                    rfl

theorem cell20_306623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 5, 5].length) (baseStart_306623 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_306623 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_306623 prefixEnd_306623 := by exact prefixLift 306623
  have htrace : WordTrace (prefixWord ++ tailWord_306623) baseStart_306623 baseEnd_306623 := by
    simpa [prefixWord, tailWord_306623, baseEnd_306623] using wordTrace_append hprefix tailTrace_306623
  have hstable : (prefixWord ++ tailWord_306623).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306623).length < 2 ^ (prefixWord ++ tailWord_306623).sum := by decide
  have hdescent : baseEnd_306623 < baseStart_306623 := by decide
  rcases family_descends (prefixWord ++ tailWord_306623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306674 : List Nat := [3, 2, 1, 4, 1, 3, 1, 2, 3]
def baseStart_306674 : Nat := 118140960795 + 306674 * 2 ^ 59
def prefixEnd_306674 : Nat := 4983230072969 + 3 ^ 40 * 306674 * 2
def baseEnd_306674 : Nat := 139974369988478551346345

theorem tailTrace_306674 : CollatzResearch.WordTrace tailWord_306674 prefixEnd_306674 139974369988478551346345 := by
  unfold tailWord_306674
  simp only [CollatzResearch.WordTrace]
  refine ⟨2796329922744987148615769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7456879793986632396308717 2796329922744987148615769)
  ·
    refine ⟨2097247442058740361461827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2796329922744987148615769 2097247442058740361461827)
    ·
      refine ⟨3145871163088110542192741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2097247442058740361461827 3145871163088110542192741)
      ·
        refine ⟨589850843079020726661139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3145871163088110542192741 589850843079020726661139)
        ·
          refine ⟨884776264618531089991709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 589850843079020726661139 884776264618531089991709)
          ·
            refine ⟨331791099231949158746891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 884776264618531089991709 331791099231949158746891)
            ·
              refine ⟨497686648847923738120337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 331791099231949158746891 497686648847923738120337)
              ·
                refine ⟨373264986635942803590253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 497686648847923738120337 373264986635942803590253)
                ·
                  refine ⟨139974369988478551346345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 373264986635942803590253 139974369988478551346345)
                  ·
                    rfl

theorem cell20_306674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 1, 2, 3].length) (baseStart_306674 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_306674 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_306674 prefixEnd_306674 := by exact prefixLift 306674
  have htrace : WordTrace (prefixWord ++ tailWord_306674) baseStart_306674 baseEnd_306674 := by
    simpa [prefixWord, tailWord_306674, baseEnd_306674] using wordTrace_append hprefix tailTrace_306674
  have hstable : (prefixWord ++ tailWord_306674).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306674).length < 2 ^ (prefixWord ++ tailWord_306674).sum := by decide
  have hdescent : baseEnd_306674 < baseStart_306674 := by decide
  rcases family_descends (prefixWord ++ tailWord_306674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306685 : List Nat := [1, 4, 1, 1, 1, 4, 1, 3, 4]
def baseStart_306685 : Nat := 118140960795 + 306685 * 2 ^ 59
def prefixEnd_306685 : Nat := 4983230072969 + 3 ^ 40 * 306685 * 2
def baseEnd_306685 : Nat := 139979390688211401979633

theorem tailTrace_306685 : CollatzResearch.WordTrace tailWord_306685 prefixEnd_306685 139979390688211401979633 := by
  unfold tailWord_306685
  simp only [CollatzResearch.WordTrace]
  refine ⟨11185720893940097473113509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7457147262626731648742339 11185720893940097473113509)
  ·
    refine ⟨2097322667613768276208783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11185720893940097473113509 2097322667613768276208783)
    ·
      refine ⟨3145984001420652414313175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2097322667613768276208783 3145984001420652414313175)
      ·
        refine ⟨4718976002130978621469763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3145984001420652414313175 4718976002130978621469763)
        ·
          refine ⟨7078464003196467932204645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4718976002130978621469763 7078464003196467932204645)
          ·
            refine ⟨1327212000599337737288371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7078464003196467932204645 1327212000599337737288371)
            ·
              refine ⟨1990818000899006605932557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1327212000599337737288371 1990818000899006605932557)
              ·
                refine ⟨746556750337127477224709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1990818000899006605932557 746556750337127477224709)
                ·
                  refine ⟨139979390688211401979633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 746556750337127477224709 139979390688211401979633)
                  ·
                    rfl

theorem cell20_306685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 3, 4].length) (baseStart_306685 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_306685 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_306685 prefixEnd_306685 := by exact prefixLift 306685
  have htrace : WordTrace (prefixWord ++ tailWord_306685) baseStart_306685 baseEnd_306685 := by
    simpa [prefixWord, tailWord_306685, baseEnd_306685] using wordTrace_append hprefix tailTrace_306685
  have hstable : (prefixWord ++ tailWord_306685).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306685).length < 2 ^ (prefixWord ++ tailWord_306685).sum := by decide
  have hdescent : baseEnd_306685 < baseStart_306685 := by decide
  rcases family_descends (prefixWord ++ tailWord_306685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306701 : List Nat := [1, 7, 1, 1, 3, 1, 2, 4]
def baseStart_306701 : Nat := 118140960795 + 306701 * 2 ^ 59
def prefixEnd_306701 : Nat := 4983230072969 + 3 ^ 40 * 306701 * 2
def baseEnd_306701 : Nat := 46662231174728819148745

theorem tailTrace_306701 : CollatzResearch.WordTrace tailWord_306701 prefixEnd_306701 46662231174728819148745 := by
  unfold tailWord_306701
  simp only [CollatzResearch.WordTrace]
  refine ⟨11186304461882132205695957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7457536307921421470463971 11186304461882132205695957)
  ·
    refine ⟨262179010825362473570999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 11186304461882132205695957 262179010825362473570999)
    ·
      refine ⟨393268516238043710356499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 262179010825362473570999 393268516238043710356499)
      ·
        refine ⟨589902774357065565534749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 393268516238043710356499 589902774357065565534749)
        ·
          refine ⟨221213540383899587075531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 589902774357065565534749 221213540383899587075531)
          ·
            refine ⟨331820310575849380613297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 221213540383899587075531 331820310575849380613297)
            ·
              refine ⟨248865232931887035459973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 331820310575849380613297 248865232931887035459973)
              ·
                refine ⟨46662231174728819148745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 248865232931887035459973 46662231174728819148745)
                ·
                  rfl

theorem cell20_306701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 2, 4].length) (baseStart_306701 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_306701 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_306701 prefixEnd_306701 := by exact prefixLift 306701
  have htrace : WordTrace (prefixWord ++ tailWord_306701) baseStart_306701 baseEnd_306701 := by
    simpa [prefixWord, tailWord_306701, baseEnd_306701] using wordTrace_append hprefix tailTrace_306701
  have hstable : (prefixWord ++ tailWord_306701).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306701).length < 2 ^ (prefixWord ++ tailWord_306701).sum := by decide
  have hdescent : baseEnd_306701 < baseStart_306701 := by decide
  rcases family_descends (prefixWord ++ tailWord_306701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306709 : List Nat := [1, 3, 2, 1, 3, 2, 4, 4]
def baseStart_306709 : Nat := 118140960795 + 306709 * 2 ^ 59
def prefixEnd_306709 : Nat := 4983230072969 + 3 ^ 40 * 306709 * 2
def baseEnd_306709 : Nat := 46663448314057995059845

theorem tailTrace_306709 : CollatzResearch.WordTrace tailWord_306709 prefixEnd_306709 46663448314057995059845 := by
  unfold tailWord_306709
  simp only [CollatzResearch.WordTrace]
  refine ⟨11186596245853149571987181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7457730830568766381324787 11186596245853149571987181)
  ·
    refine ⟨4194973592194931089495193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11186596245853149571987181 4194973592194931089495193)
    ·
      refine ⟨3146230194146198317121395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4194973592194931089495193 3146230194146198317121395)
      ·
        refine ⟨4719345291219297475682093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3146230194146198317121395 4719345291219297475682093)
        ·
          refine ⟨1769754484207236553380785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4719345291219297475682093 1769754484207236553380785)
          ·
            refine ⟨1327315863155427415035589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1769754484207236553380785 1327315863155427415035589)
            ·
              refine ⟨248871724341642640319173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1327315863155427415035589 248871724341642640319173)
              ·
                refine ⟨46663448314057995059845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 248871724341642640319173 46663448314057995059845)
                ·
                  rfl

theorem cell20_306709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 4, 4].length) (baseStart_306709 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_306709 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_306709 prefixEnd_306709 := by exact prefixLift 306709
  have htrace : WordTrace (prefixWord ++ tailWord_306709) baseStart_306709 baseEnd_306709 := by
    simpa [prefixWord, tailWord_306709, baseEnd_306709] using wordTrace_append hprefix tailTrace_306709
  have hstable : (prefixWord ++ tailWord_306709).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306709).length < 2 ^ (prefixWord ++ tailWord_306709).sum := by decide
  have hdescent : baseEnd_306709 < baseStart_306709 := by decide
  rcases family_descends (prefixWord ++ tailWord_306709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306823 : List Nat := [1, 1, 4, 2, 1, 4, 3, 4]
def baseStart_306823 : Nat := 118140960795 + 306823 * 2 ^ 59
def prefixEnd_306823 : Nat := 4983230072969 + 3 ^ 40 * 306823 * 2
def baseEnd_306823 : Nat := 46680792549498751793023

theorem tailTrace_306823 : CollatzResearch.WordTrace tailWord_306823 prefixEnd_306823 46680792549498751793023 := by
  unfold tailWord_306823
  simp only [CollatzResearch.WordTrace]
  refine ⟨11190754167440147041637123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7460502778293431361091415 11190754167440147041637123)
  ·
    refine ⟨16786131251160220562455685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11190754167440147041637123 16786131251160220562455685)
    ·
      refine ⟨3147399609592541355460441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16786131251160220562455685 3147399609592541355460441)
      ·
        refine ⟨2360549707194406016595331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3147399609592541355460441 2360549707194406016595331)
        ·
          refine ⟨3540824560791609024892997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2360549707194406016595331 3540824560791609024892997)
          ·
            refine ⟨663904605148426692167437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3540824560791609024892997 663904605148426692167437)
            ·
              refine ⟨248964226930660009562789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 663904605148426692167437 248964226930660009562789)
              ·
                refine ⟨46680792549498751793023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 248964226930660009562789 46680792549498751793023)
                ·
                  rfl

theorem cell20_306823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 3, 4].length) (baseStart_306823 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_306823 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_306823 prefixEnd_306823 := by exact prefixLift 306823
  have htrace : WordTrace (prefixWord ++ tailWord_306823) baseStart_306823 baseEnd_306823 := by
    simpa [prefixWord, tailWord_306823, baseEnd_306823] using wordTrace_append hprefix tailTrace_306823
  have hstable : (prefixWord ++ tailWord_306823).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306823).length < 2 ^ (prefixWord ++ tailWord_306823).sum := by decide
  have hdescent : baseEnd_306823 < baseStart_306823 := by decide
  rcases family_descends (prefixWord ++ tailWord_306823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306847 : List Nat := [1, 1, 2, 7, 1, 1, 1, 1, 5]
def baseStart_306847 : Nat := 118140960795 + 306847 * 2 ^ 59
def prefixEnd_306847 : Nat := 4983230072969 + 3 ^ 40 * 306847 * 2
def baseEnd_306847 : Nat := 140053331902458838578971

theorem tailTrace_306847 : CollatzResearch.WordTrace tailWord_306847 prefixEnd_306847 140053331902458838578971 := by
  unfold tailWord_306847
  simp only [CollatzResearch.WordTrace]
  refine ⟨11191629519353199140510795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7461086346235466093673863 11191629519353199140510795)
  ·
    refine ⟨16787444279029798710766193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11191629519353199140510795 16787444279029798710766193)
    ·
      refine ⟨12590583209272349033074645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16787444279029798710766193 12590583209272349033074645)
      ·
        refine ⟨295091793967320680462687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 12590583209272349033074645 295091793967320680462687)
        ·
          refine ⟨442637690950981020694031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 295091793967320680462687 442637690950981020694031)
          ·
            refine ⟨663956536426471531041047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 442637690950981020694031 663956536426471531041047)
            ·
              refine ⟨995934804639707296561571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 663956536426471531041047 995934804639707296561571)
              ·
                refine ⟨1493902206959560944842357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 995934804639707296561571 1493902206959560944842357)
                ·
                  refine ⟨140053331902458838578971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1493902206959560944842357 140053331902458838578971)
                  ·
                    rfl

theorem cell20_306847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 1, 5].length) (baseStart_306847 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_306847 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_306847 prefixEnd_306847 := by exact prefixLift 306847
  have htrace : WordTrace (prefixWord ++ tailWord_306847) baseStart_306847 baseEnd_306847 := by
    simpa [prefixWord, tailWord_306847, baseEnd_306847] using wordTrace_append hprefix tailTrace_306847
  have hstable : (prefixWord ++ tailWord_306847).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306847).length < 2 ^ (prefixWord ++ tailWord_306847).sum := by decide
  have hdescent : baseEnd_306847 < baseStart_306847 := by decide
  rcases family_descends (prefixWord ++ tailWord_306847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306851 : List Nat := [1, 1, 1, 4, 1, 1, 5, 1, 5]
def baseStart_306851 : Nat := 118140960795 + 306851 * 2 ^ 59
def prefixEnd_306851 : Nat := 4983230072969 + 3 ^ 40 * 306851 * 2
def baseEnd_306851 : Nat := 140055157611452602445621

theorem tailTrace_306851 : CollatzResearch.WordTrace tailWord_306851 prefixEnd_306851 140055157611452602445621 := by
  unfold tailWord_306851
  simp only [CollatzResearch.WordTrace]
  refine ⟨11191775411338707823656407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7461183607559138549104271 11191775411338707823656407)
  ·
    refine ⟨16787663117008061735484611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11191775411338707823656407 16787663117008061735484611)
    ·
      refine ⟨25181494675512092603226917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16787663117008061735484611 25181494675512092603226917)
      ·
        refine ⟨4721530251658517363105047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25181494675512092603226917 4721530251658517363105047)
        ·
          refine ⟨7082295377487776044657571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4721530251658517363105047 7082295377487776044657571)
          ·
            refine ⟨10623443066231664066986357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7082295377487776044657571 10623443066231664066986357)
            ·
              refine ⟨995947787459218506279971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10623443066231664066986357 995947787459218506279971)
              ·
                refine ⟨1493921681188827759419957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 995947787459218506279971 1493921681188827759419957)
                ·
                  refine ⟨140055157611452602445621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1493921681188827759419957 140055157611452602445621)
                  ·
                    rfl

theorem cell20_306851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 1, 5].length) (baseStart_306851 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_306851 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_306851 prefixEnd_306851 := by exact prefixLift 306851
  have htrace : WordTrace (prefixWord ++ tailWord_306851) baseStart_306851 baseEnd_306851 := by
    simpa [prefixWord, tailWord_306851, baseEnd_306851] using wordTrace_append hprefix tailTrace_306851
  have hstable : (prefixWord ++ tailWord_306851).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306851).length < 2 ^ (prefixWord ++ tailWord_306851).sum := by decide
  have hdescent : baseEnd_306851 < baseStart_306851 := by decide
  rcases family_descends (prefixWord ++ tailWord_306851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306878 : List Nat := [4, 2, 1, 1, 2, 4, 2, 4]
def baseStart_306878 : Nat := 118140960795 + 306878 * 2 ^ 59
def prefixEnd_306878 : Nat := 4983230072969 + 3 ^ 40 * 306878 * 2
def baseEnd_306878 : Nat := 46689160382386836181837

theorem tailTrace_306878 : CollatzResearch.WordTrace tailWord_306878 prefixEnd_306878 46689160382386836181837 := by
  unfold tailWord_306878
  simp only [CollatzResearch.WordTrace]
  refine ⟨1399095022780111429361161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7461840121493927623259525 1399095022780111429361161)
  ·
    refine ⟨1049321267085083572020871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1399095022780111429361161 1049321267085083572020871)
    ·
      refine ⟨1573981900627625358031307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1049321267085083572020871 1573981900627625358031307)
      ·
        refine ⟨2360972850941438037046961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1573981900627625358031307 2360972850941438037046961)
        ·
          refine ⟨1770729638206078527785221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2360972850941438037046961 1770729638206078527785221)
          ·
            refine ⟨332011807163639723959729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1770729638206078527785221 332011807163639723959729)
            ·
              refine ⟨249008855372729792969797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 332011807163639723959729 249008855372729792969797)
              ·
                refine ⟨46689160382386836181837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 249008855372729792969797 46689160382386836181837)
                ·
                  rfl

theorem cell20_306878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 2, 4].length) (baseStart_306878 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_306878 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_306878 prefixEnd_306878 := by exact prefixLift 306878
  have htrace : WordTrace (prefixWord ++ tailWord_306878) baseStart_306878 baseEnd_306878 := by
    simpa [prefixWord, tailWord_306878, baseEnd_306878] using wordTrace_append hprefix tailTrace_306878
  have hstable : (prefixWord ++ tailWord_306878).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306878).length < 2 ^ (prefixWord ++ tailWord_306878).sum := by decide
  have hdescent : baseEnd_306878 < baseStart_306878 := by decide
  rcases family_descends (prefixWord ++ tailWord_306878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306919 : List Nat := [1, 1, 5, 4, 1, 2, 2, 1, 3]
def baseStart_306919 : Nat := 118140960795 + 306919 * 2 ^ 59
def prefixEnd_306919 : Nat := 4983230072969 + 3 ^ 40 * 306919 * 2
def baseEnd_306919 : Nat := 140086194664346588178677

theorem tailTrace_306919 : CollatzResearch.WordTrace tailWord_306919 prefixEnd_306919 140086194664346588178677 := by
  unfold tailWord_306919
  simp only [CollatzResearch.WordTrace]
  refine ⟨11194255575092355437131811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7462837050061570291421207 11194255575092355437131811)
  ·
    refine ⟨16791383362638533155697717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11194255575092355437131811 16791383362638533155697717)
    ·
      refine ⟨1574192190247362483346661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16791383362638533155697717 1574192190247362483346661)
      ·
        refine ⟨295161035671380465627499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1574192190247362483346661 295161035671380465627499)
        ·
          refine ⟨442741553507070698441249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 295161035671380465627499 442741553507070698441249)
          ·
            refine ⟨332056165130303023830937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 442741553507070698441249 332056165130303023830937)
            ·
              refine ⟨249042123847727267873203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 332056165130303023830937 249042123847727267873203)
              ·
                refine ⟨373563185771590901809805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 249042123847727267873203 373563185771590901809805)
                ·
                  refine ⟨140086194664346588178677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 373563185771590901809805 140086194664346588178677)
                  ·
                    rfl

theorem cell20_306919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 2, 1, 3].length) (baseStart_306919 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_306919 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_306919 prefixEnd_306919 := by exact prefixLift 306919
  have htrace : WordTrace (prefixWord ++ tailWord_306919) baseStart_306919 baseEnd_306919 := by
    simpa [prefixWord, tailWord_306919, baseEnd_306919] using wordTrace_append hprefix tailTrace_306919
  have hstable : (prefixWord ++ tailWord_306919).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306919).length < 2 ^ (prefixWord ++ tailWord_306919).sum := by decide
  have hdescent : baseEnd_306919 < baseStart_306919 := by decide
  rcases family_descends (prefixWord ++ tailWord_306919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306920 : List Nat := [2, 1, 4, 1, 3, 1, 1, 7]
def baseStart_306920 : Nat := 118140960795 + 306920 * 2 ^ 59
def prefixEnd_306920 : Nat := 4983230072969 + 3 ^ 40 * 306920 * 2
def baseEnd_306920 : Nat := 46695550363865009715113

theorem tailTrace_306920 : CollatzResearch.WordTrace tailWord_306920 prefixEnd_306920 46695550363865009715113 := by
  unfold tailWord_306920
  simp only [CollatzResearch.WordTrace]
  refine ⟨5597146024044366303959107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7462861365392488405278809 5597146024044366303959107)
  ·
    refine ⟨8395719036066549455938661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5597146024044366303959107 8395719036066549455938661)
    ·
      refine ⟨1574197319262478022988499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8395719036066549455938661 1574197319262478022988499)
      ·
        refine ⟨2361295978893717034482749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1574197319262478022988499 2361295978893717034482749)
        ·
          refine ⟨885485992085143887931031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2361295978893717034482749 885485992085143887931031)
          ·
            refine ⟨1328228988127715831896547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 885485992085143887931031 1328228988127715831896547)
            ·
              refine ⟨1992343482191573747844821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1328228988127715831896547 1992343482191573747844821)
              ·
                refine ⟨46695550363865009715113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1992343482191573747844821 46695550363865009715113)
                ·
                  rfl

theorem cell20_306920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 7].length) (baseStart_306920 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_306920 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_306920 prefixEnd_306920 := by exact prefixLift 306920
  have htrace : WordTrace (prefixWord ++ tailWord_306920) baseStart_306920 baseEnd_306920 := by
    simpa [prefixWord, tailWord_306920, baseEnd_306920] using wordTrace_append hprefix tailTrace_306920
  have hstable : (prefixWord ++ tailWord_306920).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306920).length < 2 ^ (prefixWord ++ tailWord_306920).sum := by decide
  have hdescent : baseEnd_306920 < baseStart_306920 := by decide
  rcases family_descends (prefixWord ++ tailWord_306920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_306950 : List Nat := [6, 2, 2, 1, 1, 8]
def baseStart_306950 : Nat := 118140960795 + 306950 * 2 ^ 59
def prefixEnd_306950 : Nat := 4983230072969 + 3 ^ 40 * 306950 * 2
def baseEnd_306950 : Nat := 5188901626261046597971

theorem tailTrace_306950 : CollatzResearch.WordTrace tailWord_306950 prefixEnd_306950 5188901626261046597971 := by
  unfold tailWord_306950
  simp only [CollatzResearch.WordTrace]
  refine ⟨349855819936876491609697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 7463590825320031821006869 349855819936876491609697)
  ·
    refine ⟨262391864952657368707273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 349855819936876491609697 262391864952657368707273)
    ·
      refine ⟨196793898714493026530455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 262391864952657368707273 196793898714493026530455)
      ·
        refine ⟨295190848071739539795683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196793898714493026530455 295190848071739539795683)
        ·
          refine ⟨442786272107609309693525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 295190848071739539795683 442786272107609309693525)
          ·
            refine ⟨5188901626261046597971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 442786272107609309693525 5188901626261046597971)
            ·
              rfl

theorem cell20_306950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 8].length) (baseStart_306950 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_306950 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_306950 prefixEnd_306950 := by exact prefixLift 306950
  have htrace : WordTrace (prefixWord ++ tailWord_306950) baseStart_306950 baseEnd_306950 := by
    simpa [prefixWord, tailWord_306950, baseEnd_306950] using wordTrace_append hprefix tailTrace_306950
  have hstable : (prefixWord ++ tailWord_306950).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_306950).length < 2 ^ (prefixWord ++ tailWord_306950).sum := by decide
  have hdescent : baseEnd_306950 < baseStart_306950 := by decide
  rcases family_descends (prefixWord ++ tailWord_306950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307017 : List Nat := [1, 2, 1, 1, 2, 4, 9]
def baseStart_307017 : Nat := 118140960795 + 307017 * 2 ^ 59
def prefixEnd_307017 : Nat := 4983230072969 + 3 ^ 40 * 307017 * 2
def baseEnd_307017 : Nat := 15570102726077089212401

theorem tailTrace_307017 : CollatzResearch.WordTrace tailWord_307017 prefixEnd_307017 15570102726077089212401 := by
  unfold tailWord_307017
  simp only [CollatzResearch.WordTrace]
  refine ⟨11197829928737318174199305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7465219952491545449466203 11197829928737318174199305)
  ·
    refine ⟨8398372446552988630649479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11197829928737318174199305 8398372446552988630649479)
    ·
      refine ⟨12597558669829482945974219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8398372446552988630649479 12597558669829482945974219)
      ·
        refine ⟨18896338004744224418961329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12597558669829482945974219 18896338004744224418961329)
        ·
          refine ⟨14172253503558168314220997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18896338004744224418961329 14172253503558168314220997)
          ·
            refine ⟨2657297531917156558916437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14172253503558168314220997 2657297531917156558916437)
            ·
              refine ⟨15570102726077089212401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2657297531917156558916437 15570102726077089212401)
              ·
                rfl

theorem cell20_307017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 9].length) (baseStart_307017 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_307017 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_307017 prefixEnd_307017 := by exact prefixLift 307017
  have htrace : WordTrace (prefixWord ++ tailWord_307017) baseStart_307017 baseEnd_307017 := by
    simpa [prefixWord, tailWord_307017, baseEnd_307017] using wordTrace_append hprefix tailTrace_307017
  have hstable : (prefixWord ++ tailWord_307017).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307017).length < 2 ^ (prefixWord ++ tailWord_307017).sum := by decide
  have hdescent : baseEnd_307017 < baseStart_307017 := by decide
  rcases family_descends (prefixWord ++ tailWord_307017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307020 : List Nat := [2, 2, 1, 3, 4, 1, 1, 1, 5]
def baseStart_307020 : Nat := 118140960795 + 307020 * 2 ^ 59
def prefixEnd_307020 : Nat := 4983230072969 + 3 ^ 40 * 307020 * 2
def baseEnd_307020 : Nat := 140132293816439125811597

theorem tailTrace_307020 : CollatzResearch.WordTrace tailWord_307020 prefixEnd_307020 140132293816439125811597 := by
  unfold tailWord_307020
  simp only [CollatzResearch.WordTrace]
  refine ⟨5598969673863224843279257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7465292898484299791039009 5598969673863224843279257)
  ·
    refine ⟨4199227255397418632459443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5598969673863224843279257 4199227255397418632459443)
    ·
      refine ⟨6298840883096127948689165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4199227255397418632459443 6298840883096127948689165)
      ·
        refine ⟨2362065331161047980758437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6298840883096127948689165 2362065331161047980758437)
        ·
          refine ⟨442887249592696496392207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2362065331161047980758437 442887249592696496392207)
          ·
            refine ⟨664330874389044744588311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 442887249592696496392207 664330874389044744588311)
            ·
              refine ⟨996496311583567116882467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 664330874389044744588311 996496311583567116882467)
              ·
                refine ⟨1494744467375350675323701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 996496311583567116882467 1494744467375350675323701)
                ·
                  refine ⟨140132293816439125811597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1494744467375350675323701 140132293816439125811597)
                  ·
                    rfl

theorem cell20_307020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 1, 5].length) (baseStart_307020 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_307020 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_307020 prefixEnd_307020 := by exact prefixLift 307020
  have htrace : WordTrace (prefixWord ++ tailWord_307020) baseStart_307020 baseEnd_307020 := by
    simpa [prefixWord, tailWord_307020, baseEnd_307020] using wordTrace_append hprefix tailTrace_307020
  have hstable : (prefixWord ++ tailWord_307020).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307020).length < 2 ^ (prefixWord ++ tailWord_307020).sum := by decide
  have hdescent : baseEnd_307020 < baseStart_307020 := by decide
  rcases family_descends (prefixWord ++ tailWord_307020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307092 : List Nat := [2, 4, 2, 1, 1, 4, 2, 1, 3]
def baseStart_307092 : Nat := 118140960795 + 307092 * 2 ^ 59
def prefixEnd_307092 : Nat := 4983230072969 + 3 ^ 40 * 307092 * 2
def baseEnd_307092 : Nat := 140165156578326875411303

theorem tailTrace_307092 : CollatzResearch.WordTrace tailWord_307092 prefixEnd_307092 140165156578326875411303 := by
  unfold tailWord_307092
  simp only [CollatzResearch.WordTrace]
  refine ⟨5600282701732802991589765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7467043602310403988786353 5600282701732802991589765)
  ·
    refine ⟨1050053006574900560923081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5600282701732802991589765 1050053006574900560923081)
    ·
      refine ⟨787539754931175420692311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1050053006574900560923081 787539754931175420692311)
      ·
        refine ⟨1181309632396763131038467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 787539754931175420692311 1181309632396763131038467)
        ·
          refine ⟨1771964448595144696557701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1181309632396763131038467 1771964448595144696557701)
          ·
            refine ⟨332243334111589630604569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1771964448595144696557701 332243334111589630604569)
            ·
              refine ⟨249182500583692222953427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 332243334111589630604569 249182500583692222953427)
              ·
                refine ⟨373773750875538334430141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 249182500583692222953427 373773750875538334430141)
                ·
                  refine ⟨140165156578326875411303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 373773750875538334430141 140165156578326875411303)
                  ·
                    rfl

theorem cell20_307092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 2, 1, 3].length) (baseStart_307092 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_307092 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_307092 prefixEnd_307092 := by exact prefixLift 307092
  have htrace : WordTrace (prefixWord ++ tailWord_307092) baseStart_307092 baseEnd_307092 := by
    simpa [prefixWord, tailWord_307092, baseEnd_307092] using wordTrace_append hprefix tailTrace_307092
  have hstable : (prefixWord ++ tailWord_307092).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307092).length < 2 ^ (prefixWord ++ tailWord_307092).sum := by decide
  have hdescent : baseEnd_307092 < baseStart_307092 := by decide
  rcases family_descends (prefixWord ++ tailWord_307092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307134 : List Nat := [4, 2, 1, 1, 1, 3, 1, 4, 3]
def baseStart_307134 : Nat := 118140960795 + 307134 * 2 ^ 59
def prefixEnd_307134 : Nat := 4983230072969 + 3 ^ 40 * 307134 * 2
def baseEnd_307134 : Nat := 140184326522761396011131

theorem tailTrace_307134 : CollatzResearch.WordTrace tailWord_307134 prefixEnd_307134 140184326522761396011131 := by
  unfold tailWord_307134
  simp only [CollatzResearch.WordTrace]
  refine ⟨1400262158664180894526057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7468064846208964770805637 1400262158664180894526057)
  ·
    refine ⟨1050196618998135670894543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1400262158664180894526057 1050196618998135670894543)
    ·
      refine ⟨1575294928497203506341815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1050196618998135670894543 1575294928497203506341815)
      ·
        refine ⟨2362942392745805259512723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1575294928497203506341815 2362942392745805259512723)
        ·
          refine ⟨3544413589118707889269085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2362942392745805259512723 3544413589118707889269085)
          ·
            refine ⟨1329155095919515458475907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3544413589118707889269085 1329155095919515458475907)
            ·
              refine ⟨1993732643879273187713861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1329155095919515458475907 1993732643879273187713861)
              ·
                refine ⟨373824870727363722696349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1993732643879273187713861 373824870727363722696349)
                ·
                  refine ⟨140184326522761396011131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 373824870727363722696349 140184326522761396011131)
                  ·
                    rfl

theorem cell20_307134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 4, 3].length) (baseStart_307134 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_307134 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_307134 prefixEnd_307134 := by exact prefixLift 307134
  have htrace : WordTrace (prefixWord ++ tailWord_307134) baseStart_307134 baseEnd_307134 := by
    simpa [prefixWord, tailWord_307134, baseEnd_307134] using wordTrace_append hprefix tailTrace_307134
  have hstable : (prefixWord ++ tailWord_307134).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307134).length < 2 ^ (prefixWord ++ tailWord_307134).sum := by decide
  have hdescent : baseEnd_307134 < baseStart_307134 := by decide
  rcases family_descends (prefixWord ++ tailWord_307134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307148 : List Nat := [2, 2, 1, 4, 1, 2, 3, 5]
def baseStart_307148 : Nat := 118140960795 + 307148 * 2 ^ 59
def prefixEnd_307148 : Nat := 4983230072969 + 3 ^ 40 * 307148 * 2
def baseEnd_307148 : Nat := 46730238834746523181469

theorem tailTrace_307148 : CollatzResearch.WordTrace tailWord_307148 prefixEnd_307148 46730238834746523181469 := by
  unfold tailWord_307148
  simp only [CollatzResearch.WordTrace]
  refine ⟨5601303945631363773609049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7468405260841818364812065 5601303945631363773609049)
  ·
    refine ⟨4200977959223522830206787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5601303945631363773609049 4200977959223522830206787)
    ·
      refine ⟨6301466938835284245310181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4200977959223522830206787 6301466938835284245310181)
      ·
        refine ⟨1181525051031615795995659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6301466938835284245310181 1181525051031615795995659)
        ·
          refine ⟨1772287576547423693993489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1181525051031615795995659 1772287576547423693993489)
          ·
            refine ⟨1329215682410567770495117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1772287576547423693993489 1329215682410567770495117)
            ·
              refine ⟨498455880903962913935669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1329215682410567770495117 498455880903962913935669)
              ·
                refine ⟨46730238834746523181469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 498455880903962913935669 46730238834746523181469)
                ·
                  rfl

theorem cell20_307148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 3, 5].length) (baseStart_307148 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_307148 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_307148 prefixEnd_307148 := by exact prefixLift 307148
  have htrace : WordTrace (prefixWord ++ tailWord_307148) baseStart_307148 baseEnd_307148 := by
    simpa [prefixWord, tailWord_307148, baseEnd_307148] using wordTrace_append hprefix tailTrace_307148
  have hstable : (prefixWord ++ tailWord_307148).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307148).length < 2 ^ (prefixWord ++ tailWord_307148).sum := by decide
  have hdescent : baseEnd_307148 < baseStart_307148 := by decide
  rcases family_descends (prefixWord ++ tailWord_307148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307169 : List Nat := [1, 2, 3, 1, 2, 1, 2, 8]
def baseStart_307169 : Nat := 118140960795 + 307169 * 2 ^ 59
def prefixEnd_307169 : Nat := 4983230072969 + 3 ^ 40 * 307169 * 2
def baseEnd_307169 : Nat := 46733433825485609948107

theorem tailTrace_307169 : CollatzResearch.WordTrace tailWord_307169 prefixEnd_307169 46733433825485609948107 := by
  unfold tailWord_307169
  simp only [CollatzResearch.WordTrace]
  refine ⟨11203373824186648133732561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7468915882791098755821707 11203373824186648133732561)
  ·
    refine ⟨8402530368139986100299421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11203373824186648133732561 8402530368139986100299421)
    ·
      refine ⟨3150948888052494787612283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8402530368139986100299421 3150948888052494787612283)
      ·
        refine ⟨4726423332078742181418425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3150948888052494787612283 4726423332078742181418425)
        ·
          refine ⟨3544817499059056636063819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4726423332078742181418425 3544817499059056636063819)
          ·
            refine ⟨5317226248588584954095729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3544817499059056636063819 5317226248588584954095729)
            ·
              refine ⟨3987919686441438715571797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5317226248588584954095729 3987919686441438715571797)
              ·
                refine ⟨46733433825485609948107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3987919686441438715571797 46733433825485609948107)
                ·
                  rfl

theorem cell20_307169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 8].length) (baseStart_307169 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_307169 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_307169 prefixEnd_307169 := by exact prefixLift 307169
  have htrace : WordTrace (prefixWord ++ tailWord_307169) baseStart_307169 baseEnd_307169 := by
    simpa [prefixWord, tailWord_307169, baseEnd_307169] using wordTrace_append hprefix tailTrace_307169
  have hstable : (prefixWord ++ tailWord_307169).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307169).length < 2 ^ (prefixWord ++ tailWord_307169).sum := by decide
  have hdescent : baseEnd_307169 < baseStart_307169 := by decide
  rcases family_descends (prefixWord ++ tailWord_307169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307175 : List Nat := [1, 1, 5, 2, 3, 1, 2, 3, 2]
def baseStart_307175 : Nat := 118140960795 + 307175 * 2 ^ 59
def prefixEnd_307175 : Nat := 4983230072969 + 3 ^ 40 * 307175 * 2
def baseEnd_307175 : Nat := 140203040039947475644297

theorem tailTrace_307175 : CollatzResearch.WordTrace tailWord_307175 prefixEnd_307175 140203040039947475644297 := by
  unfold tailWord_307175
  simp only [CollatzResearch.WordTrace]
  refine ⟨11203592662164911158450979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7469061774776607438967319 11203592662164911158450979)
  ·
    refine ⟨16805388993247366737676469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11203592662164911158450979 16805388993247366737676469)
    ·
      refine ⟨1575505218116940631657169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16805388993247366737676469 1575505218116940631657169)
      ·
        refine ⟨1181628913587705473742877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1575505218116940631657169 1181628913587705473742877)
        ·
          refine ⟨443110842595389552653579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1181628913587705473742877 443110842595389552653579)
          ·
            refine ⟨664666263893084328980369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 443110842595389552653579 664666263893084328980369)
            ·
              refine ⟨498499697919813246735277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 664666263893084328980369 498499697919813246735277)
              ·
                refine ⟨186937386719929967525729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 498499697919813246735277 186937386719929967525729)
                ·
                  refine ⟨140203040039947475644297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 186937386719929967525729 140203040039947475644297)
                  ·
                    rfl

theorem cell20_307175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 2, 3, 2].length) (baseStart_307175 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_307175 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_307175 prefixEnd_307175 := by exact prefixLift 307175
  have htrace : WordTrace (prefixWord ++ tailWord_307175) baseStart_307175 baseEnd_307175 := by
    simpa [prefixWord, tailWord_307175, baseEnd_307175] using wordTrace_append hprefix tailTrace_307175
  have hstable : (prefixWord ++ tailWord_307175).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307175).length < 2 ^ (prefixWord ++ tailWord_307175).sum := by decide
  have hdescent : baseEnd_307175 < baseStart_307175 := by decide
  rcases family_descends (prefixWord ++ tailWord_307175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307193 : List Nat := [1, 2, 1, 3, 1, 5, 1, 1, 5]
def baseStart_307193 : Nat := 118140960795 + 307193 * 2 ^ 59
def prefixEnd_307193 : Nat := 4983230072969 + 3 ^ 40 * 307193 * 2
def baseEnd_307193 : Nat := 140211255730419413044223

theorem tailTrace_307193 : CollatzResearch.WordTrace tailWord_307193 prefixEnd_307193 140211255730419413044223 := by
  unfold tailWord_307193
  simp only [CollatzResearch.WordTrace]
  refine ⟨11204249176099700232606233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7469499450733133488404155 11204249176099700232606233)
  ·
    refine ⟨8403186882074775174454675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11204249176099700232606233 8403186882074775174454675)
    ·
      refine ⟨12604780323112162761682013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8403186882074775174454675 12604780323112162761682013)
      ·
        refine ⟨4726792621167061035630755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12604780323112162761682013 4726792621167061035630755)
        ·
          refine ⟨7090188931750591553446133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4726792621167061035630755 7090188931750591553446133)
          ·
            refine ⟨664705212351617958135575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7090188931750591553446133 664705212351617958135575)
            ·
              refine ⟨997057818527426937203363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 664705212351617958135575 997057818527426937203363)
              ·
                refine ⟨1495586727791140405805045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 997057818527426937203363 1495586727791140405805045)
                ·
                  refine ⟨140211255730419413044223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1495586727791140405805045 140211255730419413044223)
                  ·
                    rfl

theorem cell20_307193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 1, 5].length) (baseStart_307193 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_307193 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_307193 prefixEnd_307193 := by exact prefixLift 307193
  have htrace : WordTrace (prefixWord ++ tailWord_307193) baseStart_307193 baseEnd_307193 := by
    simpa [prefixWord, tailWord_307193, baseEnd_307193] using wordTrace_append hprefix tailTrace_307193
  have hstable : (prefixWord ++ tailWord_307193).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307193).length < 2 ^ (prefixWord ++ tailWord_307193).sum := by decide
  have hdescent : baseEnd_307193 < baseStart_307193 := by decide
  rcases family_descends (prefixWord ++ tailWord_307193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307220 : List Nat := [2, 4, 3, 2, 1, 1, 1, 6]
def baseStart_307220 : Nat := 118140960795 + 307220 * 2 ^ 59
def prefixEnd_307220 : Nat := 4983230072969 + 3 ^ 40 * 307220 * 2
def baseEnd_307220 : Nat := 46741193088709106381371

theorem tailTrace_307220 : CollatzResearch.WordTrace tailWord_307220 prefixEnd_307220 46741193088709106381371 := by
  unfold tailWord_307220
  simp only [CollatzResearch.WordTrace]
  refine ⟨5602616973500941921919557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7470155964667922562559409 5602616973500941921919557)
  ·
    refine ⟨1050490682531426610359917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5602616973500941921919557 1050490682531426610359917)
    ·
      refine ⟨393934005949284978884969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1050490682531426610359917 393934005949284978884969)
      ·
        refine ⟨295450504461963734163727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 393934005949284978884969 295450504461963734163727)
        ·
          refine ⟨443175756692945601245591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 295450504461963734163727 443175756692945601245591)
          ·
            refine ⟨664763635039418401868387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 443175756692945601245591 664763635039418401868387)
            ·
              refine ⟨997145452559127602802581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 664763635039418401868387 997145452559127602802581)
              ·
                refine ⟨46741193088709106381371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 997145452559127602802581 46741193088709106381371)
                ·
                  rfl

theorem cell20_307220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 6].length) (baseStart_307220 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_307220 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_307220 prefixEnd_307220 := by exact prefixLift 307220
  have htrace : WordTrace (prefixWord ++ tailWord_307220) baseStart_307220 baseEnd_307220 := by
    simpa [prefixWord, tailWord_307220, baseEnd_307220] using wordTrace_append hprefix tailTrace_307220
  have hstable : (prefixWord ++ tailWord_307220).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307220).length < 2 ^ (prefixWord ++ tailWord_307220).sum := by decide
  have hdescent : baseEnd_307220 < baseStart_307220 := by decide
  rcases family_descends (prefixWord ++ tailWord_307220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307255 : List Nat := [1, 1, 3, 1, 2, 2, 2, 6, 2]
def baseStart_307255 : Nat := 118140960795 + 307255 * 2 ^ 59
def prefixEnd_307255 : Nat := 4983230072969 + 3 ^ 40 * 307255 * 2
def baseEnd_307255 : Nat := 140239554219822752977303

theorem tailTrace_307255 : CollatzResearch.WordTrace tailWord_307255 prefixEnd_307255 140239554219822752977303 := by
  unfold tailWord_307255
  simp only [CollatzResearch.WordTrace]
  refine ⟨11206510501875084821363219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7471007001250056547575479 11206510501875084821363219)
  ·
    refine ⟨16809765752812627232044829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11206510501875084821363219 16809765752812627232044829)
    ·
      refine ⟨6303662157304735212016811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16809765752812627232044829 6303662157304735212016811)
      ·
        refine ⟨9455493235957102818025217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6303662157304735212016811 9455493235957102818025217)
        ·
          refine ⟨7091619926967827113518913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9455493235957102818025217 7091619926967827113518913)
          ·
            refine ⟨5318714945225870335139185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7091619926967827113518913 5318714945225870335139185)
            ·
              refine ⟨3989036208919402751354389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5318714945225870335139185 3989036208919402751354389)
              ·
                refine ⟨186986072293097003969737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3989036208919402751354389 186986072293097003969737)
                ·
                  refine ⟨140239554219822752977303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 186986072293097003969737 140239554219822752977303)
                  ·
                    rfl

theorem cell20_307255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 6, 2].length) (baseStart_307255 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_307255 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_307255 prefixEnd_307255 := by exact prefixLift 307255
  have htrace : WordTrace (prefixWord ++ tailWord_307255) baseStart_307255 baseEnd_307255 := by
    simpa [prefixWord, tailWord_307255, baseEnd_307255] using wordTrace_append hprefix tailTrace_307255
  have hstable : (prefixWord ++ tailWord_307255).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307255).length < 2 ^ (prefixWord ++ tailWord_307255).sum := by decide
  have hdescent : baseEnd_307255 < baseStart_307255 := by decide
  rcases family_descends (prefixWord ++ tailWord_307255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307265 : List Nat := [1, 2, 5, 1, 2, 1, 4, 1, 3]
def baseStart_307265 : Nat := 118140960795 + 307265 * 2 ^ 59
def prefixEnd_307265 : Nat := 4983230072969 + 3 ^ 40 * 307265 * 2
def baseEnd_307265 : Nat := 140244118492307162643929

theorem tailTrace_307265 : CollatzResearch.WordTrace tailWord_307265 prefixEnd_307265 140244118492307162643929 := by
  unfold tailWord_307265
  simp only [CollatzResearch.WordTrace]
  refine ⟨11206875231838856529227249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7471250154559237686151499 11206875231838856529227249)
  ·
    refine ⟨8405156423879142396920437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11206875231838856529227249 8405156423879142396920437)
    ·
      refine ⟨787983414738669599711291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8405156423879142396920437 787983414738669599711291)
      ·
        refine ⟨1181975122108004399566937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 787983414738669599711291 1181975122108004399566937)
        ·
          refine ⟨886481341581003299675203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1181975122108004399566937 886481341581003299675203)
          ·
            refine ⟨1329722012371504949512805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 886481341581003299675203 1329722012371504949512805)
            ·
              refine ⟨249322877319657178033651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1329722012371504949512805 249322877319657178033651)
              ·
                refine ⟨373984315979485767050477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 249322877319657178033651 373984315979485767050477)
                ·
                  refine ⟨140244118492307162643929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 373984315979485767050477 140244118492307162643929)
                  ·
                    rfl

theorem cell20_307265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 4, 1, 3].length) (baseStart_307265 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_307265 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_307265 prefixEnd_307265 := by exact prefixLift 307265
  have htrace : WordTrace (prefixWord ++ tailWord_307265) baseStart_307265 baseEnd_307265 := by
    simpa [prefixWord, tailWord_307265, baseEnd_307265] using wordTrace_append hprefix tailTrace_307265
  have hstable : (prefixWord ++ tailWord_307265).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307265).length < 2 ^ (prefixWord ++ tailWord_307265).sum := by decide
  have hdescent : baseEnd_307265 < baseStart_307265 := by decide
  rcases family_descends (prefixWord ++ tailWord_307265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307276 : List Nat := [2, 2, 1, 3, 1, 1, 2, 4, 4]
def baseStart_307276 : Nat := 118140960795 + 307276 * 2 ^ 59
def prefixEnd_307276 : Nat := 4983230072969 + 3 ^ 40 * 307276 * 2
def baseEnd_307276 : Nat := 140249139192040013277217

theorem tailTrace_307276 : CollatzResearch.WordTrace tailWord_307276 prefixEnd_307276 140249139192040013277217 := by
  unfold tailWord_307276
  simp only [CollatzResearch.WordTrace]
  refine ⟨5603638217399502703938841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7471517623199336938585121 5603638217399502703938841)
  ·
    refine ⟨4202728663049627027954131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5603638217399502703938841 4202728663049627027954131)
    ·
      refine ⟨6304092994574440541931197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4202728663049627027954131 6304092994574440541931197)
      ·
        refine ⟨2364034872965415203224199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6304092994574440541931197 2364034872965415203224199)
        ·
          refine ⟨3546052309448122804836299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2364034872965415203224199 3546052309448122804836299)
          ·
            refine ⟨5319078464172184207254449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3546052309448122804836299 5319078464172184207254449)
            ·
              refine ⟨3989308848129138155440837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5319078464172184207254449 3989308848129138155440837)
              ·
                refine ⟨747995409024213404145157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3989308848129138155440837 747995409024213404145157)
                ·
                  refine ⟨140249139192040013277217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 747995409024213404145157 140249139192040013277217)
                  ·
                    rfl

theorem cell20_307276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 4, 4].length) (baseStart_307276 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_307276 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_307276 prefixEnd_307276 := by exact prefixLift 307276
  have htrace : WordTrace (prefixWord ++ tailWord_307276) baseStart_307276 baseEnd_307276 := by
    simpa [prefixWord, tailWord_307276, baseEnd_307276] using wordTrace_append hprefix tailTrace_307276
  have hstable : (prefixWord ++ tailWord_307276).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307276).length < 2 ^ (prefixWord ++ tailWord_307276).sum := by decide
  have hdescent : baseEnd_307276 < baseStart_307276 := by decide
  rcases family_descends (prefixWord ++ tailWord_307276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307306 : List Nat := [3, 1, 3, 2, 3, 2, 2, 2, 2]
def baseStart_307306 : Nat := 118140960795 + 307306 * 2 ^ 59
def prefixEnd_307306 : Nat := 4983230072969 + 3 ^ 40 * 307306 * 2
def baseEnd_307306 : Nat := 140262832009493242277095

theorem tailTrace_307306 : CollatzResearch.WordTrace tailWord_307306 prefixEnd_307306 140262832009493242277095 := by
  unfold tailWord_307306
  simp only [CollatzResearch.WordTrace]
  refine ⟨2802092656172580132867443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7472247083126880354313181 2802092656172580132867443)
  ·
    refine ⟨4203138984258870199301165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2802092656172580132867443 4203138984258870199301165)
    ·
      refine ⟨1576177119097076324737937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4203138984258870199301165 1576177119097076324737937)
      ·
        refine ⟨1182132839322807243553453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1576177119097076324737937 1182132839322807243553453)
        ·
          refine ⟨443299814746052716332545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1182132839322807243553453 443299814746052716332545)
          ·
            refine ⟨332474861059539537249409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 443299814746052716332545 332474861059539537249409)
            ·
              refine ⟨249356145794654652937057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 332474861059539537249409 249356145794654652937057)
              ·
                refine ⟨187017109345990989702793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 249356145794654652937057 187017109345990989702793)
                ·
                  refine ⟨140262832009493242277095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 187017109345990989702793 140262832009493242277095)
                  ·
                    rfl

theorem cell20_307306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 2, 2, 2].length) (baseStart_307306 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_307306 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_307306 prefixEnd_307306 := by exact prefixLift 307306
  have htrace : WordTrace (prefixWord ++ tailWord_307306) baseStart_307306 baseEnd_307306 := by
    simpa [prefixWord, tailWord_307306, baseEnd_307306] using wordTrace_append hprefix tailTrace_307306
  have hstable : (prefixWord ++ tailWord_307306).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307306).length < 2 ^ (prefixWord ++ tailWord_307306).sum := by decide
  have hdescent : baseEnd_307306 < baseStart_307306 := by decide
  rcases family_descends (prefixWord ++ tailWord_307306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307310 : List Nat := [4, 1, 2, 2, 1, 1, 3, 4, 2]
def baseStart_307310 : Nat := 118140960795 + 307310 * 2 ^ 59
def prefixEnd_307310 : Nat := 4983230072969 + 3 ^ 40 * 307310 * 2
def baseEnd_307310 : Nat := 140264657718487006143745

theorem tailTrace_307310 : CollatzResearch.WordTrace tailWord_307310 prefixEnd_307310 140264657718487006143745 := by
  unfold tailWord_307310
  simp only [CollatzResearch.WordTrace]
  refine ⟨1401064564584478651826923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7472344344450552809743589 1401064564584478651826923)
  ·
    refine ⟨2101596846876717977740385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1401064564584478651826923 2101596846876717977740385)
    ·
      refine ⟨1576197635157538483305289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2101596846876717977740385 1576197635157538483305289)
      ·
        refine ⟨1182148226368153862478967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1576197635157538483305289 1182148226368153862478967)
        ·
          refine ⟨1773222339552230793718451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1182148226368153862478967 1773222339552230793718451)
          ·
            refine ⟨2659833509328346190577677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1773222339552230793718451 2659833509328346190577677)
            ·
              refine ⟨997437565998129821466629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2659833509328346190577677 997437565998129821466629)
              ·
                refine ⟨187019543624649341524993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 997437565998129821466629 187019543624649341524993)
                ·
                  refine ⟨140264657718487006143745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 187019543624649341524993 140264657718487006143745)
                  ·
                    rfl

theorem cell20_307310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 4, 2].length) (baseStart_307310 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_307310 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_307310 prefixEnd_307310 := by exact prefixLift 307310
  have htrace : WordTrace (prefixWord ++ tailWord_307310) baseStart_307310 baseEnd_307310 := by
    simpa [prefixWord, tailWord_307310, baseEnd_307310] using wordTrace_append hprefix tailTrace_307310
  have hstable : (prefixWord ++ tailWord_307310).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307310).length < 2 ^ (prefixWord ++ tailWord_307310).sum := by decide
  have hdescent : baseEnd_307310 < baseStart_307310 := by decide
  rcases family_descends (prefixWord ++ tailWord_307310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307328 : List Nat := [2, 1, 1, 2, 1, 3, 1, 2, 7]
def baseStart_307328 : Nat := 118140960795 + 307328 * 2 ^ 59
def prefixEnd_307328 : Nat := 4983230072969 + 3 ^ 40 * 307328 * 2
def baseEnd_307328 : Nat := 140272873408958943543671

theorem tailTrace_307328 : CollatzResearch.WordTrace tailWord_307328 prefixEnd_307328 140272873408958943543671 := by
  unfold tailWord_307328
  simp only [CollatzResearch.WordTrace]
  refine ⟨5604586515305309144385319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7472782020407078859180425 5604586515305309144385319)
  ·
    refine ⟨8406879772957963716577979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5604586515305309144385319 8406879772957963716577979)
    ·
      refine ⟨12610319659436945574866969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8406879772957963716577979 12610319659436945574866969)
      ·
        refine ⟨9457739744577709181150227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12610319659436945574866969 9457739744577709181150227)
        ·
          refine ⟨14186609616866563771725341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9457739744577709181150227 14186609616866563771725341)
          ·
            refine ⟨5319978606324961414397003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14186609616866563771725341 5319978606324961414397003)
            ·
              refine ⟨7979967909487442121595505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5319978606324961414397003 7979967909487442121595505)
              ·
                refine ⟨5984975932115581591196629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7979967909487442121595505 5984975932115581591196629)
                ·
                  refine ⟨140272873408958943543671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5984975932115581591196629 140272873408958943543671)
                  ·
                    rfl

theorem cell20_307328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 7].length) (baseStart_307328 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_307328 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_307328 prefixEnd_307328 := by exact prefixLift 307328
  have htrace : WordTrace (prefixWord ++ tailWord_307328) baseStart_307328 baseEnd_307328 := by
    simpa [prefixWord, tailWord_307328, baseEnd_307328] using wordTrace_append hprefix tailTrace_307328
  have hstable : (prefixWord ++ tailWord_307328).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307328).length < 2 ^ (prefixWord ++ tailWord_307328).sum := by decide
  have hdescent : baseEnd_307328 < baseStart_307328 := by decide
  rcases family_descends (prefixWord ++ tailWord_307328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307358 : List Nat := [4, 3, 1, 1, 3, 2, 1, 2, 3]
def baseStart_307358 : Nat := 118140960795 + 307358 * 2 ^ 59
def prefixEnd_307358 : Nat := 4983230072969 + 3 ^ 40 * 307358 * 2
def baseEnd_307358 : Nat := 140286566226412172543549

theorem tailTrace_307358 : CollatzResearch.WordTrace tailWord_307358 prefixEnd_307358 140286566226412172543549 := by
  unfold tailWord_307358
  simp only [CollatzResearch.WordTrace]
  refine ⟨1401283402562741676545341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7473511480334622274908485 1401283402562741676545341)
  ·
    refine ⟨525481275961028128704503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1401283402562741676545341 525481275961028128704503)
    ·
      refine ⟨788221913941542193056755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 525481275961028128704503 788221913941542193056755)
      ·
        refine ⟨1182332870912313289585133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 788221913941542193056755 1182332870912313289585133)
        ·
          refine ⟨443374826592117483594425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1182332870912313289585133 443374826592117483594425)
          ·
            refine ⟨332531119944088112695819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 443374826592117483594425 332531119944088112695819)
            ·
              refine ⟨498796679916132169043729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 332531119944088112695819 498796679916132169043729)
              ·
                refine ⟨374097509937099126782797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 498796679916132169043729 374097509937099126782797)
                ·
                  refine ⟨140286566226412172543549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 374097509937099126782797 140286566226412172543549)
                  ·
                    rfl

theorem cell20_307358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_307358 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_307358 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_307358 prefixEnd_307358 := by exact prefixLift 307358
  have htrace : WordTrace (prefixWord ++ tailWord_307358) baseStart_307358 baseEnd_307358 := by
    simpa [prefixWord, tailWord_307358, baseEnd_307358] using wordTrace_append hprefix tailTrace_307358
  have hstable : (prefixWord ++ tailWord_307358).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307358).length < 2 ^ (prefixWord ++ tailWord_307358).sum := by decide
  have hdescent : baseEnd_307358 < baseStart_307358 := by decide
  rcases family_descends (prefixWord ++ tailWord_307358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307362 : List Nat := [3, 3, 1, 3, 1, 2, 1, 1, 5]
def baseStart_307362 : Nat := 118140960795 + 307362 * 2 ^ 59
def prefixEnd_307362 : Nat := 4983230072969 + 3 ^ 40 * 307362 * 2
def baseEnd_307362 : Nat := 140288391935405936410199

theorem tailTrace_307362 : CollatzResearch.WordTrace tailWord_307362 prefixEnd_307362 140288391935405936410199 := by
  unfold tailWord_307362
  simp only [CollatzResearch.WordTrace]
  refine ⟨2802603278121860523877085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7473608741658294730338893 2802603278121860523877085)
  ·
    refine ⟨1050976229295697696453907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2802603278121860523877085 1050976229295697696453907)
    ·
      refine ⟨1576464343943546544680861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1050976229295697696453907 1576464343943546544680861)
      ·
        refine ⟨591174128978829954255323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1576464343943546544680861 591174128978829954255323)
        ·
          refine ⟨886761193468244931382985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 591174128978829954255323 886761193468244931382985)
          ·
            refine ⟨665070895101183698537239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 886761193468244931382985 665070895101183698537239)
            ·
              refine ⟨997606342651775547805859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 665070895101183698537239 997606342651775547805859)
              ·
                refine ⟨1496409513977663321708789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 997606342651775547805859 1496409513977663321708789)
                ·
                  refine ⟨140288391935405936410199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1496409513977663321708789 140288391935405936410199)
                  ·
                    rfl

theorem cell20_307362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_307362 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_307362 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_307362 prefixEnd_307362 := by exact prefixLift 307362
  have htrace : WordTrace (prefixWord ++ tailWord_307362) baseStart_307362 baseEnd_307362 := by
    simpa [prefixWord, tailWord_307362, baseEnd_307362] using wordTrace_append hprefix tailTrace_307362
  have hstable : (prefixWord ++ tailWord_307362).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307362).length < 2 ^ (prefixWord ++ tailWord_307362).sum := by decide
  have hdescent : baseEnd_307362 < baseStart_307362 := by decide
  rcases family_descends (prefixWord ++ tailWord_307362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307393 : List Nat := [1, 2, 6, 1, 2, 1, 1, 6]
def baseStart_307393 : Nat := 118140960795 + 307393 * 2 ^ 59
def prefixEnd_307393 : Nat := 4983230072969 + 3 ^ 40 * 307393 * 2
def baseEnd_307393 : Nat := 46767513726702535458913

theorem tailTrace_307393 : CollatzResearch.WordTrace tailWord_307393 prefixEnd_307393 46767513726702535458913 := by
  unfold tailWord_307393
  simp only [CollatzResearch.WordTrace]
  refine ⟨11211543775375134389886833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7474362516916756259924555 11211543775375134389886833)
  ·
    refine ⟨8408657831531350792415125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11211543775375134389886833 8408657831531350792415125)
    ·
      refine ⟨394155835853032068394459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 8408657831531350792415125 394155835853032068394459)
      ·
        refine ⟨591233753779548102591689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 394155835853032068394459 591233753779548102591689)
        ·
          refine ⟨443425315334661076943767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 591233753779548102591689 443425315334661076943767)
          ·
            refine ⟨665137973001991615415651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 443425315334661076943767 665137973001991615415651)
            ·
              refine ⟨997706959502987423123477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 665137973001991615415651 997706959502987423123477)
              ·
                refine ⟨46767513726702535458913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 997706959502987423123477 46767513726702535458913)
                ·
                  rfl

theorem cell20_307393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 6].length) (baseStart_307393 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_307393 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_307393 prefixEnd_307393 := by exact prefixLift 307393
  have htrace : WordTrace (prefixWord ++ tailWord_307393) baseStart_307393 baseEnd_307393 := by
    simpa [prefixWord, tailWord_307393, baseEnd_307393] using wordTrace_append hprefix tailTrace_307393
  have hstable : (prefixWord ++ tailWord_307393).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307393).length < 2 ^ (prefixWord ++ tailWord_307393).sum := by decide
  have hdescent : baseEnd_307393 < baseStart_307393 := by decide
  rcases family_descends (prefixWord ++ tailWord_307393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307420 : List Nat := [2, 2, 5, 2, 2, 1, 1, 1, 4]
def baseStart_307420 : Nat := 118140960795 + 307420 * 2 ^ 59
def prefixEnd_307420 : Nat := 4983230072969 + 3 ^ 40 * 307420 * 2
def baseEnd_307420 : Nat := 140314864715815512476629

theorem tailTrace_307420 : CollatzResearch.WordTrace tailWord_307420 prefixEnd_307420 140314864715815512476629 := by
  unfold tailWord_307420
  simp only [CollatzResearch.WordTrace]
  refine ⟨5606264273138659000559857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7475019030851545334079809 5606264273138659000559857)
  ·
    refine ⟨4204698204853994250419893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5606264273138659000559857 4204698204853994250419893)
    ·
      refine ⟨394190456705061960976865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4204698204853994250419893 394190456705061960976865)
      ·
        refine ⟨295642842528796470732649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 394190456705061960976865 295642842528796470732649)
        ·
          refine ⟨221732131896597353049487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 295642842528796470732649 221732131896597353049487)
          ·
            refine ⟨332598197844896029574231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 221732131896597353049487 332598197844896029574231)
            ·
              refine ⟨498897296767344044361347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 332598197844896029574231 498897296767344044361347)
              ·
                refine ⟨748345945151016066542021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 498897296767344044361347 748345945151016066542021)
                ·
                  refine ⟨140314864715815512476629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 748345945151016066542021 140314864715815512476629)
                  ·
                    rfl

theorem cell20_307420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 1, 1, 4].length) (baseStart_307420 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_307420 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_307420 prefixEnd_307420 := by exact prefixLift 307420
  have htrace : WordTrace (prefixWord ++ tailWord_307420) baseStart_307420 baseEnd_307420 := by
    simpa [prefixWord, tailWord_307420, baseEnd_307420] using wordTrace_append hprefix tailTrace_307420
  have hstable : (prefixWord ++ tailWord_307420).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307420).length < 2 ^ (prefixWord ++ tailWord_307420).sum := by decide
  have hdescent : baseEnd_307420 < baseStart_307420 := by decide
  rcases family_descends (prefixWord ++ tailWord_307420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307424 : List Nat := [2, 1, 1, 3, 1, 3, 5, 2, 2]
def baseStart_307424 : Nat := 118140960795 + 307424 * 2 ^ 59
def prefixEnd_307424 : Nat := 4983230072969 + 3 ^ 40 * 307424 * 2
def baseEnd_307424 : Nat := 140316690424809276343279

theorem tailTrace_307424 : CollatzResearch.WordTrace tailWord_307424 prefixEnd_307424 140316690424809276343279 := by
  unfold tailWord_307424
  simp only [CollatzResearch.WordTrace]
  refine ⟨5606337219131413342132663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7475116292175217789510217 5606337219131413342132663)
  ·
    refine ⟨8409505828697120013198995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5606337219131413342132663 8409505828697120013198995)
    ·
      refine ⟨12614258743045680019798493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8409505828697120013198995 12614258743045680019798493)
      ·
        refine ⟨4730347028642130007424435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12614258743045680019798493 4730347028642130007424435)
        ·
          refine ⟨7095520542963195011136653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4730347028642130007424435 7095520542963195011136653)
          ·
            refine ⟨2660820203611198129176245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7095520542963195011136653 2660820203611198129176245)
            ·
              refine ⟨249451894088549824610273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2660820203611198129176245 249451894088549824610273)
              ·
                refine ⟨187088920566412368457705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 249451894088549824610273 187088920566412368457705)
                ·
                  refine ⟨140316690424809276343279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 187088920566412368457705 140316690424809276343279)
                  ·
                    rfl

theorem cell20_307424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 5, 2, 2].length) (baseStart_307424 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_307424 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_307424 prefixEnd_307424 := by exact prefixLift 307424
  have htrace : WordTrace (prefixWord ++ tailWord_307424) baseStart_307424 baseEnd_307424 := by
    simpa [prefixWord, tailWord_307424, baseEnd_307424] using wordTrace_append hprefix tailTrace_307424
  have hstable : (prefixWord ++ tailWord_307424).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307424).length < 2 ^ (prefixWord ++ tailWord_307424).sum := by decide
  have hdescent : baseEnd_307424 < baseStart_307424 := by decide
  rcases family_descends (prefixWord ++ tailWord_307424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307435 : List Nat := [1, 1, 1, 1, 2, 5, 4, 5]
def baseStart_307435 : Nat := 118140960795 + 307435 * 2 ^ 59
def prefixEnd_307435 : Nat := 4983230072969 + 3 ^ 40 * 307435 * 2
def baseEnd_307435 : Nat := 46773903708180708992189

theorem tailTrace_307435 : CollatzResearch.WordTrace tailWord_307435 prefixEnd_307435 46773903708180708992189 := by
  unfold tailWord_307435
  simp only [CollatzResearch.WordTrace]
  refine ⟨11213075641222975562915759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7475383760815317041943839 11213075641222975562915759)
  ·
    refine ⟨16819613461834463344373639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11213075641222975562915759 16819613461834463344373639)
    ·
      refine ⟨25229420192751695016560459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16819613461834463344373639 25229420192751695016560459)
      ·
        refine ⟨37844130289127542524840689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25229420192751695016560459 37844130289127542524840689)
        ·
          refine ⟨28383097716845656893630517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37844130289127542524840689 28383097716845656893630517)
          ·
            refine ⟨2660915410954280333777861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28383097716845656893630517 2660915410954280333777861)
            ·
              refine ⟨498921639553927562583349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2660915410954280333777861 498921639553927562583349)
              ·
                refine ⟨46773903708180708992189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 498921639553927562583349 46773903708180708992189)
                ·
                  rfl

theorem cell20_307435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 4, 5].length) (baseStart_307435 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_307435 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_307435 prefixEnd_307435 := by exact prefixLift 307435
  have htrace : WordTrace (prefixWord ++ tailWord_307435) baseStart_307435 baseEnd_307435 := by
    simpa [prefixWord, tailWord_307435, baseEnd_307435] using wordTrace_append hprefix tailTrace_307435
  have hstable : (prefixWord ++ tailWord_307435).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307435).length < 2 ^ (prefixWord ++ tailWord_307435).sum := by decide
  have hdescent : baseEnd_307435 < baseStart_307435 := by decide
  rcases family_descends (prefixWord ++ tailWord_307435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307479 : List Nat := [1, 1, 3, 4, 1, 4, 2, 2, 2]
def baseStart_307479 : Nat := 118140960795 + 307479 * 2 ^ 59
def prefixEnd_307479 : Nat := 4983230072969 + 3 ^ 40 * 307479 * 2
def baseEnd_307479 : Nat := 140341793923473529509721

theorem tailTrace_307479 : CollatzResearch.WordTrace tailWord_307479 prefixEnd_307479 140341793923473529509721 := by
  unfold tailWord_307479
  simp only [CollatzResearch.WordTrace]
  refine ⟨11214680453063571077517491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7476453635375714051678327 11214680453063571077517491)
  ·
    refine ⟨16822020679595356616276237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11214680453063571077517491 16822020679595356616276237)
    ·
      refine ⟨6308257754848258731103589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16822020679595356616276237 6308257754848258731103589)
      ·
        refine ⟨1182798329034048512081923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6308257754848258731103589 1182798329034048512081923)
        ·
          refine ⟨1774197493551072768122885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1182798329034048512081923 1774197493551072768122885)
          ·
            refine ⟨332662030040826144023041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1774197493551072768122885 332662030040826144023041)
            ·
              refine ⟨249496522530619608017281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 332662030040826144023041 249496522530619608017281)
              ·
                refine ⟨187122391897964706012961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 249496522530619608017281 187122391897964706012961)
                ·
                  refine ⟨140341793923473529509721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 187122391897964706012961 140341793923473529509721)
                  ·
                    rfl

theorem cell20_307479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 2, 2, 2].length) (baseStart_307479 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_307479 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_307479 prefixEnd_307479 := by exact prefixLift 307479
  have htrace : WordTrace (prefixWord ++ tailWord_307479) baseStart_307479 baseEnd_307479 := by
    simpa [prefixWord, tailWord_307479, baseEnd_307479] using wordTrace_append hprefix tailTrace_307479
  have hstable : (prefixWord ++ tailWord_307479).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307479).length < 2 ^ (prefixWord ++ tailWord_307479).sum := by decide
  have hdescent : baseEnd_307479 < baseStart_307479 := by decide
  rcases family_descends (prefixWord ++ tailWord_307479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307486 : List Nat := [4, 3, 2, 1, 1, 3, 1, 5]
def baseStart_307486 : Nat := 118140960795 + 307486 * 2 ^ 59
def prefixEnd_307486 : Nat := 4983230072969 + 3 ^ 40 * 307486 * 2
def baseEnd_307486 : Nat := 46781662971404205425453

theorem tailTrace_307486 : CollatzResearch.WordTrace tailWord_307486 prefixEnd_307486 46781662971404205425453 := by
  unfold tailWord_307486
  simp only [CollatzResearch.WordTrace]
  refine ⟨1401866970504776409127789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7476623842692140848681541 1401866970504776409127789)
  ·
    refine ⟨525700113939291153422921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1401866970504776409127789 525700113939291153422921)
    ·
      refine ⟨394275085454468365067191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 525700113939291153422921 394275085454468365067191)
      ·
        refine ⟨591412628181702547600787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 394275085454468365067191 591412628181702547600787)
        ·
          refine ⟨887118942272553821401181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 591412628181702547600787 887118942272553821401181)
          ·
            refine ⟨332669603352207683025443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 887118942272553821401181 332669603352207683025443)
            ·
              refine ⟨499004405028311524538165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 332669603352207683025443 499004405028311524538165)
              ·
                refine ⟨46781662971404205425453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 499004405028311524538165 46781662971404205425453)
                ·
                  rfl

theorem cell20_307486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 1, 5].length) (baseStart_307486 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_307486 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_307486 prefixEnd_307486 := by exact prefixLift 307486
  have htrace : WordTrace (prefixWord ++ tailWord_307486) baseStart_307486 baseEnd_307486 := by
    simpa [prefixWord, tailWord_307486, baseEnd_307486] using wordTrace_append hprefix tailTrace_307486
  have hstable : (prefixWord ++ tailWord_307486).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307486).length < 2 ^ (prefixWord ++ tailWord_307486).sum := by decide
  have hdescent : baseEnd_307486 < baseStart_307486 := by decide
  rcases family_descends (prefixWord ++ tailWord_307486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307490 : List Nat := [3, 3, 1, 1, 3, 1, 3, 5]
def baseStart_307490 : Nat := 118140960795 + 307490 * 2 ^ 59
def prefixEnd_307490 : Nat := 4983230072969 + 3 ^ 40 * 307490 * 2
def baseEnd_307490 : Nat := 46782271541068793381003

theorem tailTrace_307490 : CollatzResearch.WordTrace tailWord_307490 prefixEnd_307490 46782271541068793381003 := by
  unfold tailWord_307490
  simp only [CollatzResearch.WordTrace]
  refine ⟨2803770414005929989041981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7476721104015813304111949 2803770414005929989041981)
  ·
    refine ⟨1051413905252223745890743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2803770414005929989041981 1051413905252223745890743)
    ·
      refine ⟨1577120857878335618836115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1051413905252223745890743 1577120857878335618836115)
      ·
        refine ⟨2365681286817503428254173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1577120857878335618836115 2365681286817503428254173)
        ·
          refine ⟨887130482556563785595315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2365681286817503428254173 887130482556563785595315)
          ·
            refine ⟨1330695723834845678392973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 887130482556563785595315 1330695723834845678392973)
            ·
              refine ⟨499010896438067129397365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1330695723834845678392973 499010896438067129397365)
              ·
                refine ⟨46782271541068793381003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 499010896438067129397365 46782271541068793381003)
                ·
                  rfl

theorem cell20_307490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 3, 5].length) (baseStart_307490 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_307490 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_307490 prefixEnd_307490 := by exact prefixLift 307490
  have htrace : WordTrace (prefixWord ++ tailWord_307490) baseStart_307490 baseEnd_307490 := by
    simpa [prefixWord, tailWord_307490, baseEnd_307490] using wordTrace_append hprefix tailTrace_307490
  have hstable : (prefixWord ++ tailWord_307490).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307490).length < 2 ^ (prefixWord ++ tailWord_307490).sum := by decide
  have hdescent : baseEnd_307490 < baseStart_307490 := by decide
  rcases family_descends (prefixWord ++ tailWord_307490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307548 : List Nat := [2, 2, 4, 3, 1, 1, 3, 1, 3]
def baseStart_307548 : Nat := 118140960795 + 307548 * 2 ^ 59
def prefixEnd_307548 : Nat := 4983230072969 + 3 ^ 40 * 307548 * 2
def baseEnd_307548 : Nat := 140373287403615956209439

theorem tailTrace_307548 : CollatzResearch.WordTrace tailWord_307548 prefixEnd_307548 140373287403615956209439 := by
  unfold tailWord_307548
  simp only [CollatzResearch.WordTrace]
  refine ⟨5608598544906797930889649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7478131393209063907852865 5608598544906797930889649)
  ·
    refine ⟨4206448908680098448167237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5608598544906797930889649 4206448908680098448167237)
    ·
      refine ⟨788709170377518459031357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4206448908680098448167237 788709170377518459031357)
      ·
        refine ⟨295765938891569422136759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 788709170377518459031357 295765938891569422136759)
        ·
          refine ⟨443648908337354133205139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 295765938891569422136759 443648908337354133205139)
          ·
            refine ⟨665473362506031199807709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 443648908337354133205139 665473362506031199807709)
            ·
              refine ⟨249552510939761699927891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 665473362506031199807709 249552510939761699927891)
              ·
                refine ⟨374328766409642549891837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 249552510939761699927891 374328766409642549891837)
                ·
                  refine ⟨140373287403615956209439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 374328766409642549891837 140373287403615956209439)
                  ·
                    rfl

theorem cell20_307548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 3, 1, 3].length) (baseStart_307548 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_307548 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_307548 prefixEnd_307548 := by exact prefixLift 307548
  have htrace : WordTrace (prefixWord ++ tailWord_307548) baseStart_307548 baseEnd_307548 := by
    simpa [prefixWord, tailWord_307548, baseEnd_307548] using wordTrace_append hprefix tailTrace_307548
  have hstable : (prefixWord ++ tailWord_307548).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307548).length < 2 ^ (prefixWord ++ tailWord_307548).sum := by decide
  have hdescent : baseEnd_307548 < baseStart_307548 := by decide
  rcases family_descends (prefixWord ++ tailWord_307548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307573 : List Nat := [1, 3, 4, 1, 2, 1, 1, 2, 5]
def baseStart_307573 : Nat := 118140960795 + 307573 * 2 ^ 59
def prefixEnd_307573 : Nat := 4983230072969 + 3 ^ 40 * 307573 * 2
def baseEnd_307573 : Nat := 140384698084826980376003

theorem tailTrace_307573 : CollatzResearch.WordTrace tailWord_307573 prefixEnd_307573 140384698084826980376003 := by
  unfold tailWord_307573
  simp only [CollatzResearch.WordTrace]
  refine ⟨11218108914723025131439373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7478739276482016754292915 11218108914723025131439373)
  ·
    refine ⟨4206790843021134424289765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11218108914723025131439373 4206790843021134424289765)
    ·
      refine ⟨788773283066462704554331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4206790843021134424289765 788773283066462704554331)
      ·
        refine ⟨1183159924599694056831497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 788773283066462704554331 1183159924599694056831497)
        ·
          refine ⟨887369943449770542623623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1183159924599694056831497 887369943449770542623623)
          ·
            refine ⟨1331054915174655813935435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 887369943449770542623623 1331054915174655813935435)
            ·
              refine ⟨1996582372761983720903153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1331054915174655813935435 1996582372761983720903153)
              ·
                refine ⟨1497436779571487790677365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1996582372761983720903153 1497436779571487790677365)
                ·
                  refine ⟨140384698084826980376003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1497436779571487790677365 140384698084826980376003)
                  ·
                    rfl

theorem cell20_307573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 2, 5].length) (baseStart_307573 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_307573 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_307573 prefixEnd_307573 := by exact prefixLift 307573
  have htrace : WordTrace (prefixWord ++ tailWord_307573) baseStart_307573 baseEnd_307573 := by
    simpa [prefixWord, tailWord_307573, baseEnd_307573] using wordTrace_append hprefix tailTrace_307573
  have hstable : (prefixWord ++ tailWord_307573).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307573).length < 2 ^ (prefixWord ++ tailWord_307573).sum := by decide
  have hdescent : baseEnd_307573 < baseStart_307573 := by decide
  rcases family_descends (prefixWord ++ tailWord_307573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307618 : List Nat := [3, 3, 1, 2, 1, 1, 2, 1, 6]
def baseStart_307618 : Nat := 118140960795 + 307618 * 2 ^ 59
def prefixEnd_307618 : Nat := 4983230072969 + 3 ^ 40 * 307618 * 2
def baseEnd_307618 : Nat := 140405237311006823875819

theorem tailTrace_307618 : CollatzResearch.WordTrace tailWord_307618 prefixEnd_307618 140405237311006823875819 := by
  unfold tailWord_307618
  simp only [CollatzResearch.WordTrace]
  refine ⟨2804937549889999454206877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7479833466373331877885005 2804937549889999454206877)
  ·
    refine ⟨1051851581208749795327579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2804937549889999454206877 1051851581208749795327579)
    ·
      refine ⟨1577777371813124692991369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1051851581208749795327579 1577777371813124692991369)
      ·
        refine ⟨1183333028859843519743527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1577777371813124692991369 1183333028859843519743527)
        ·
          refine ⟨1774999543289765279615291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1183333028859843519743527 1774999543289765279615291)
          ·
            refine ⟨2662499314934647919422937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1774999543289765279615291 2662499314934647919422937)
            ·
              refine ⟨1996874486200985939567203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2662499314934647919422937 1996874486200985939567203)
              ·
                refine ⟨2995311729301478909350805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1996874486200985939567203 2995311729301478909350805)
                ·
                  refine ⟨140405237311006823875819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2995311729301478909350805 140405237311006823875819)
                  ·
                    rfl

theorem cell20_307618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_307618 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_307618 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_307618 prefixEnd_307618 := by exact prefixLift 307618
  have htrace : WordTrace (prefixWord ++ tailWord_307618) baseStart_307618 baseEnd_307618 := by
    simpa [prefixWord, tailWord_307618, baseEnd_307618] using wordTrace_append hprefix tailTrace_307618
  have hstable : (prefixWord ++ tailWord_307618).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307618).length < 2 ^ (prefixWord ++ tailWord_307618).sum := by decide
  have hdescent : baseEnd_307618 < baseStart_307618 := by decide
  rcases family_descends (prefixWord ++ tailWord_307618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307690 : List Nat := [3, 1, 3, 1, 3, 2, 2, 3, 2]
def baseStart_307690 : Nat := 118140960795 + 307690 * 2 ^ 59
def prefixEnd_307690 : Nat := 4983230072969 + 3 ^ 40 * 307690 * 2
def baseEnd_307690 : Nat := 140438100072894573475525

theorem tailTrace_307690 : CollatzResearch.WordTrace tailWord_307690 prefixEnd_307690 140438100072894573475525 := by
  unfold tailWord_307690
  simp only [CollatzResearch.WordTrace]
  refine ⟨2805594063824788528362131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7481584170199436075632349 2805594063824788528362131)
  ·
    refine ⟨4208391095737182792543197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2805594063824788528362131 4208391095737182792543197)
    ·
      refine ⟨1578146660901443547203699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4208391095737182792543197 1578146660901443547203699)
      ·
        refine ⟨2367219991352165320805549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1578146660901443547203699 2367219991352165320805549)
        ·
          refine ⟨887707496757061995302081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2367219991352165320805549 887707496757061995302081)
          ·
            refine ⟨665780622567796496476561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 887707496757061995302081 665780622567796496476561)
            ·
              refine ⟨499335466925847372357421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 665780622567796496476561 499335466925847372357421)
              ·
                refine ⟨187250800097192764634033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 499335466925847372357421 187250800097192764634033)
                ·
                  refine ⟨140438100072894573475525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 187250800097192764634033 140438100072894573475525)
                  ·
                    rfl

theorem cell20_307690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 2, 3, 2].length) (baseStart_307690 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_307690 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_307690 prefixEnd_307690 := by exact prefixLift 307690
  have htrace : WordTrace (prefixWord ++ tailWord_307690) baseStart_307690 baseEnd_307690 := by
    simpa [prefixWord, tailWord_307690, baseEnd_307690] using wordTrace_append hprefix tailTrace_307690
  have hstable : (prefixWord ++ tailWord_307690).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307690).length < 2 ^ (prefixWord ++ tailWord_307690).sum := by decide
  have hdescent : baseEnd_307690 < baseStart_307690 := by decide
  rcases family_descends (prefixWord ++ tailWord_307690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307749 : List Nat := [1, 3, 1, 2, 2, 1, 5, 3, 2]
def baseStart_307749 : Nat := 118140960795 + 307749 * 2 ^ 59
def prefixEnd_307749 : Nat := 4983230072969 + 3 ^ 40 * 307749 * 2
def baseEnd_307749 : Nat := 140465029280552590508617

theorem tailTrace_307749 : CollatzResearch.WordTrace tailWord_307749 prefixEnd_307749 140465029280552590508617 := by
  unfold tailWord_307749
  simp only [CollatzResearch.WordTrace]
  refine ⟨11224528162085407189846301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7483018774723604793230867 11224528162085407189846301)
  ·
    refine ⟨4209198060782027696192363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11224528162085407189846301 4209198060782027696192363)
    ·
      refine ⟨6313797091173041544288545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4209198060782027696192363 6313797091173041544288545)
      ·
        refine ⟨4735347818379781158216409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6313797091173041544288545 4735347818379781158216409)
        ·
          refine ⟨3551510863784835868662307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4735347818379781158216409 3551510863784835868662307)
          ·
            refine ⟨5327266295677253802993461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3551510863784835868662307 5327266295677253802993461)
            ·
              refine ⟨499431215219742544030637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5327266295677253802993461 499431215219742544030637)
              ·
                refine ⟨187286705707403454011489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 499431215219742544030637 187286705707403454011489)
                ·
                  refine ⟨140465029280552590508617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 187286705707403454011489 140465029280552590508617)
                  ·
                    rfl

theorem cell20_307749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 5, 3, 2].length) (baseStart_307749 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_307749 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_307749 prefixEnd_307749 := by exact prefixLift 307749
  have htrace : WordTrace (prefixWord ++ tailWord_307749) baseStart_307749 baseEnd_307749 := by
    simpa [prefixWord, tailWord_307749, baseEnd_307749] using wordTrace_append hprefix tailTrace_307749
  have hstable : (prefixWord ++ tailWord_307749).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307749).length < 2 ^ (prefixWord ++ tailWord_307749).sum := by decide
  have hdescent : baseEnd_307749 < baseStart_307749 := by decide
  rcases family_descends (prefixWord ++ tailWord_307749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307760 : List Nat := [2, 1, 1, 1, 2, 3, 10]
def baseStart_307760 : Nat := 118140960795 + 307760 * 2 ^ 59
def prefixEnd_307760 : Nat := 4983230072969 + 3 ^ 40 * 307760 * 2
def baseEnd_307760 : Nat := 15607783331142826793545

theorem tailTrace_307760 : CollatzResearch.WordTrace tailWord_307760 prefixEnd_307760 15607783331142826793545 := by
  unfold tailWord_307760
  simp only [CollatzResearch.WordTrace]
  refine ⟨5612464682522778034248367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7483286243363704045664489 5612464682522778034248367)
  ·
    refine ⟨8418697023784167051372551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5612464682522778034248367 8418697023784167051372551)
    ·
      refine ⟨12628045535676250577058827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8418697023784167051372551 12628045535676250577058827)
      ·
        refine ⟨18942068303514375865588241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12628045535676250577058827 18942068303514375865588241)
        ·
          refine ⟨14206551227635781899191181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18942068303514375865588241 14206551227635781899191181)
          ·
            refine ⟨5327456710363418212196693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14206551227635781899191181 5327456710363418212196693)
            ·
              refine ⟨15607783331142826793545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 5327456710363418212196693 15607783331142826793545)
              ·
                rfl

theorem cell20_307760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 10].length) (baseStart_307760 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_307760 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_307760 prefixEnd_307760 := by exact prefixLift 307760
  have htrace : WordTrace (prefixWord ++ tailWord_307760) baseStart_307760 baseEnd_307760 := by
    simpa [prefixWord, tailWord_307760, baseEnd_307760] using wordTrace_append hprefix tailTrace_307760
  have hstable : (prefixWord ++ tailWord_307760).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307760).length < 2 ^ (prefixWord ++ tailWord_307760).sum := by decide
  have hdescent : baseEnd_307760 < baseStart_307760 := by decide
  rcases family_descends (prefixWord ++ tailWord_307760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307766 : List Nat := [5, 1, 2, 1, 2, 3, 1, 1, 4]
def baseStart_307766 : Nat := 118140960795 + 307766 * 2 ^ 59
def prefixEnd_307766 : Nat := 4983230072969 + 3 ^ 40 * 307766 * 2
def baseEnd_307766 : Nat := 140472788543776086941881

theorem tailTrace_307766 : CollatzResearch.WordTrace tailWord_307766 prefixEnd_307766 140472788543776086941881 := by
  unfold tailWord_307766
  simp only [CollatzResearch.WordTrace]
  refine ⟨701571762688988693325947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7483432135349212728810101 701571762688988693325947)
  ·
    refine ⟨1052357644033483039988921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 701571762688988693325947 1052357644033483039988921)
    ·
      refine ⟨789268233025112279991691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1052357644033483039988921 789268233025112279991691)
      ·
        refine ⟨1183902349537668419987537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 789268233025112279991691 1183902349537668419987537)
        ·
          refine ⟨887926762153251314990653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1183902349537668419987537 887926762153251314990653)
          ·
            refine ⟨332972535807469243121495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 887926762153251314990653 332972535807469243121495)
            ·
              refine ⟨499458803711203864682243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 332972535807469243121495 499458803711203864682243)
              ·
                refine ⟨749188205566805797023365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 499458803711203864682243 749188205566805797023365)
                ·
                  refine ⟨140472788543776086941881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 749188205566805797023365 140472788543776086941881)
                  ·
                    rfl

theorem cell20_307766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 1, 1, 4].length) (baseStart_307766 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_307766 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_307766 prefixEnd_307766 := by exact prefixLift 307766
  have htrace : WordTrace (prefixWord ++ tailWord_307766) baseStart_307766 baseEnd_307766 := by
    simpa [prefixWord, tailWord_307766, baseEnd_307766] using wordTrace_append hprefix tailTrace_307766
  have hstable : (prefixWord ++ tailWord_307766).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307766).length < 2 ^ (prefixWord ++ tailWord_307766).sum := by decide
  have hdescent : baseEnd_307766 < baseStart_307766 := by decide
  rcases family_descends (prefixWord ++ tailWord_307766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307770 : List Nat := [3, 1, 1, 1, 3, 3, 3, 1, 4]
def baseStart_307770 : Nat := 118140960795 + 307770 * 2 ^ 59
def prefixEnd_307770 : Nat := 4983230072969 + 3 ^ 40 * 307770 * 2
def baseEnd_307770 : Nat := 140474614252769850808531

theorem tailTrace_307770 : CollatzResearch.WordTrace tailWord_307770 prefixEnd_307770 140474614252769850808531 := by
  unfold tailWord_307770
  simp only [CollatzResearch.WordTrace]
  refine ⟨2806323523752331944090191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7483529396672885184240509 2806323523752331944090191)
  ·
    refine ⟨4209485285628497916135287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2806323523752331944090191 4209485285628497916135287)
    ·
      refine ⟨6314227928442746874202931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4209485285628497916135287 6314227928442746874202931)
      ·
        refine ⟨9471341892664120311304397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6314227928442746874202931 9471341892664120311304397)
        ·
          refine ⟨3551753209749045116739149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9471341892664120311304397 3551753209749045116739149)
          ·
            refine ⟨1331907453655891918777181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3551753209749045116739149 1331907453655891918777181)
            ·
              refine ⟨499465295120959469541443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1331907453655891918777181 499465295120959469541443)
              ·
                refine ⟨749197942681439204312165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 499465295120959469541443 749197942681439204312165)
                ·
                  refine ⟨140474614252769850808531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 749197942681439204312165 140474614252769850808531)
                  ·
                    rfl

theorem cell20_307770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 3, 1, 4].length) (baseStart_307770 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_307770 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_307770 prefixEnd_307770 := by exact prefixLift 307770
  have htrace : WordTrace (prefixWord ++ tailWord_307770) baseStart_307770 baseEnd_307770 := by
    simpa [prefixWord, tailWord_307770, baseEnd_307770] using wordTrace_append hprefix tailTrace_307770
  have hstable : (prefixWord ++ tailWord_307770).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307770).length < 2 ^ (prefixWord ++ tailWord_307770).sum := by decide
  have hdescent : baseEnd_307770 < baseStart_307770 := by decide
  rcases family_descends (prefixWord ++ tailWord_307770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307777 : List Nat := [1, 2, 5, 1, 1, 2, 1, 7]
def baseStart_307777 : Nat := 118140960795 + 307777 * 2 ^ 59
def prefixEnd_307777 : Nat := 4983230072969 + 3 ^ 40 * 307777 * 2
def baseEnd_307777 : Nat := 46825936414502979191723

theorem tailTrace_307777 : CollatzResearch.WordTrace tailWord_307777 prefixEnd_307777 46825936414502979191723 := by
  unfold tailWord_307777
  simp only [CollatzResearch.WordTrace]
  refine ⟨11225549405983967971865585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7483699603989311981243723 11225549405983967971865585)
  ·
    refine ⟨8419162054487975978899189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11225549405983967971865585 8419162054487975978899189)
    ·
      refine ⟨789296442608247748021799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8419162054487975978899189 789296442608247748021799)
      ·
        refine ⟨1183944663912371622032699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 789296442608247748021799 1183944663912371622032699)
        ·
          refine ⟨1775916995868557433049049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1183944663912371622032699 1775916995868557433049049)
          ·
            refine ⟨1331937746901418074786787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1775916995868557433049049 1331937746901418074786787)
            ·
              refine ⟨1997906620352127112180181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1331937746901418074786787 1997906620352127112180181)
              ·
                refine ⟨46825936414502979191723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1997906620352127112180181 46825936414502979191723)
                ·
                  rfl

theorem cell20_307777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 7].length) (baseStart_307777 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_307777 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_307777 prefixEnd_307777 := by exact prefixLift 307777
  have htrace : WordTrace (prefixWord ++ tailWord_307777) baseStart_307777 baseEnd_307777 := by
    simpa [prefixWord, tailWord_307777, baseEnd_307777] using wordTrace_append hprefix tailTrace_307777
  have hstable : (prefixWord ++ tailWord_307777).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307777).length < 2 ^ (prefixWord ++ tailWord_307777).sum := by decide
  have hdescent : baseEnd_307777 < baseStart_307777 := by decide
  rcases family_descends (prefixWord ++ tailWord_307777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307791 : List Nat := [1, 1, 2, 1, 1, 2, 4, 4, 4]
def baseStart_307791 : Nat := 118140960795 + 307791 * 2 ^ 59
def prefixEnd_307791 : Nat := 4983230072969 + 3 ^ 40 * 307791 * 2
def baseEnd_307791 : Nat := 140484199224987111108445

theorem tailTrace_307791 : CollatzResearch.WordTrace tailWord_307791 prefixEnd_307791 140484199224987111108445 := by
  unfold tailWord_307791
  simp only [CollatzResearch.WordTrace]
  refine ⟨11226060027933248362875227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7484040018622165575250151 11226060027933248362875227)
  ·
    refine ⟨16839090041899872544312841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11226060027933248362875227 16839090041899872544312841)
    ·
      refine ⟨12629317531424904408234631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16839090041899872544312841 12629317531424904408234631)
      ·
        refine ⟨18943976297137356612351947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12629317531424904408234631 18943976297137356612351947)
        ·
          refine ⟨28415964445706034918527921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18943976297137356612351947 28415964445706034918527921)
          ·
            refine ⟨21311973334279526188895941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28415964445706034918527921 21311973334279526188895941)
            ·
              refine ⟨3995995000177411160417989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21311973334279526188895941 3995995000177411160417989)
              ·
                refine ⟨749249062533264592578373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3995995000177411160417989 749249062533264592578373)
                ·
                  refine ⟨140484199224987111108445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 749249062533264592578373 140484199224987111108445)
                  ·
                    rfl

theorem cell20_307791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 4, 4].length) (baseStart_307791 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_307791 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_307791 prefixEnd_307791 := by exact prefixLift 307791
  have htrace : WordTrace (prefixWord ++ tailWord_307791) baseStart_307791 baseEnd_307791 := by
    simpa [prefixWord, tailWord_307791, baseEnd_307791] using wordTrace_append hprefix tailTrace_307791
  have hstable : (prefixWord ++ tailWord_307791).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307791).length < 2 ^ (prefixWord ++ tailWord_307791).sum := by decide
  have hdescent : baseEnd_307791 < baseStart_307791 := by decide
  rcases family_descends (prefixWord ++ tailWord_307791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307821 : List Nat := [1, 5, 1, 1, 3, 3, 2, 2, 2]
def baseStart_307821 : Nat := 118140960795 + 307821 * 2 ^ 59
def prefixEnd_307821 : Nat := 4983230072969 + 3 ^ 40 * 307821 * 2
def baseEnd_307821 : Nat := 140497892042440340108323

theorem tailTrace_307821 : CollatzResearch.WordTrace tailWord_307821 prefixEnd_307821 140497892042440340108323 := by
  unfold tailWord_307821
  simp only [CollatzResearch.WordTrace]
  refine ⟨11227154217824563486467317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7484769478549708990978211 11227154217824563486467317)
  ·
    refine ⟨1052545707921052826856311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11227154217824563486467317 1052545707921052826856311)
    ·
      refine ⟨1578818561881579240284467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1052545707921052826856311 1578818561881579240284467)
      ·
        refine ⟨2368227842822368860426701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1578818561881579240284467 2368227842822368860426701)
        ·
          refine ⟨888085441058388322660013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2368227842822368860426701 888085441058388322660013)
          ·
            refine ⟨333032040396895620997505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 888085441058388322660013 333032040396895620997505)
            ·
              refine ⟨249774030297671715748129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 333032040396895620997505 249774030297671715748129)
              ·
                refine ⟨187330522723253786811097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 249774030297671715748129 187330522723253786811097)
                ·
                  refine ⟨140497892042440340108323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 187330522723253786811097 140497892042440340108323)
                  ·
                    rfl

theorem cell20_307821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 2, 2, 2].length) (baseStart_307821 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_307821 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_307821 prefixEnd_307821 := by exact prefixLift 307821
  have htrace : WordTrace (prefixWord ++ tailWord_307821) baseStart_307821 baseEnd_307821 := by
    simpa [prefixWord, tailWord_307821, baseEnd_307821] using wordTrace_append hprefix tailTrace_307821
  have hstable : (prefixWord ++ tailWord_307821).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307821).length < 2 ^ (prefixWord ++ tailWord_307821).sum := by decide
  have hdescent : baseEnd_307821 < baseStart_307821 := by decide
  rcases family_descends (prefixWord ++ tailWord_307821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307863 : List Nat := [1, 1, 3, 3, 2, 1, 4, 3, 2]
def baseStart_307863 : Nat := 118140960795 + 307863 * 2 ^ 59
def prefixEnd_307863 : Nat := 4983230072969 + 3 ^ 40 * 307863 * 2
def baseEnd_307863 : Nat := 140517061986874860708151

theorem tailTrace_307863 : CollatzResearch.WordTrace tailWord_307863 prefixEnd_307863 140517061986874860708151 := by
  unfold tailWord_307863
  simp only [CollatzResearch.WordTrace]
  refine ⟨11228686083672404659496243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7485790722448269772997495 11228686083672404659496243)
  ·
    refine ⟨16843029125508606989244365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11228686083672404659496243 16843029125508606989244365)
    ·
      refine ⟨6316135922065727620966637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16843029125508606989244365 6316135922065727620966637)
      ·
        refine ⟨2368550970774647857862489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6316135922065727620966637 2368550970774647857862489)
        ·
          refine ⟨1776413228080985893396867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2368550970774647857862489 1776413228080985893396867)
          ·
            refine ⟨2664619842121478840095301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1776413228080985893396867 2664619842121478840095301)
            ·
              refine ⟨499616220397777282517869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2664619842121478840095301 499616220397777282517869)
              ·
                refine ⟨187356082649166480944201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 499616220397777282517869 187356082649166480944201)
                ·
                  refine ⟨140517061986874860708151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 187356082649166480944201 140517061986874860708151)
                  ·
                    rfl

theorem cell20_307863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 4, 3, 2].length) (baseStart_307863 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_307863 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_307863 prefixEnd_307863 := by exact prefixLift 307863
  have htrace : WordTrace (prefixWord ++ tailWord_307863) baseStart_307863 baseEnd_307863 := by
    simpa [prefixWord, tailWord_307863, baseEnd_307863] using wordTrace_append hprefix tailTrace_307863
  have hstable : (prefixWord ++ tailWord_307863).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307863).length < 2 ^ (prefixWord ++ tailWord_307863).sum := by decide
  have hdescent : baseEnd_307863 < baseStart_307863 := by decide
  rcases family_descends (prefixWord ++ tailWord_307863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307873 : List Nat := [1, 2, 3, 3, 4, 1, 1, 2, 3]
def baseStart_307873 : Nat := 118140960795 + 307873 * 2 ^ 59
def prefixEnd_307873 : Nat := 4983230072969 + 3 ^ 40 * 307873 * 2
def baseEnd_307873 : Nat := 140521626259359270374777

theorem tailTrace_307873 : CollatzResearch.WordTrace tailWord_307873 prefixEnd_307873 140521626259359270374777 := by
  unfold tailWord_307873
  simp only [CollatzResearch.WordTrace]
  refine ⟨11229050813636176367360273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7486033875757450911573515 11229050813636176367360273)
  ·
    refine ⟨8421788110227132275520205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11229050813636176367360273 8421788110227132275520205)
    ·
      refine ⟨3158170541335174603320077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8421788110227132275520205 3158170541335174603320077)
      ·
        refine ⟨1184313953000690476245029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3158170541335174603320077 1184313953000690476245029)
        ·
          refine ⟨222058866187629464295943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1184313953000690476245029 222058866187629464295943)
          ·
            refine ⟨333088299281444196443915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 222058866187629464295943 333088299281444196443915)
            ·
              refine ⟨499632448922166294665873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 333088299281444196443915 499632448922166294665873)
              ·
                refine ⟨374724336691624720999405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 499632448922166294665873 374724336691624720999405)
                ·
                  refine ⟨140521626259359270374777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 374724336691624720999405 140521626259359270374777)
                  ·
                    rfl

theorem cell20_307873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 1, 2, 3].length) (baseStart_307873 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_307873 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_307873 prefixEnd_307873 := by exact prefixLift 307873
  have htrace : WordTrace (prefixWord ++ tailWord_307873) baseStart_307873 baseEnd_307873 := by
    simpa [prefixWord, tailWord_307873, baseEnd_307873] using wordTrace_append hprefix tailTrace_307873
  have hstable : (prefixWord ++ tailWord_307873).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307873).length < 2 ^ (prefixWord ++ tailWord_307873).sum := by decide
  have hdescent : baseEnd_307873 < baseStart_307873 := by decide
  rcases family_descends (prefixWord ++ tailWord_307873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307908 : List Nat := [2, 3, 3, 1, 1, 2, 4, 4]
def baseStart_307908 : Nat := 118140960795 + 307908 * 2 ^ 59
def prefixEnd_307908 : Nat := 4983230072969 + 3 ^ 40 * 307908 * 2
def baseEnd_307908 : Nat := 46845867071018234735989

theorem tailTrace_307908 : CollatzResearch.WordTrace tailWord_307908 prefixEnd_307908 46845867071018234735989 := by
  unfold tailWord_307908
  simp only [CollatzResearch.WordTrace]
  refine ⟨5615163684254688672442189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7486884912339584896589585 5615163684254688672442189)
  ·
    refine ⟨2105686381595508252165821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5615163684254688672442189 2105686381595508252165821)
    ·
      refine ⟨789632393098315594562183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2105686381595508252165821 789632393098315594562183)
      ·
        refine ⟨1184448589647473391843275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 789632393098315594562183 1184448589647473391843275)
        ·
          refine ⟨1776672884471210087764913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1184448589647473391843275 1776672884471210087764913)
          ·
            refine ⟨1332504663353407565823685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1776672884471210087764913 1332504663353407565823685)
            ·
              refine ⟨249844624378763918591941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1332504663353407565823685 249844624378763918591941)
              ·
                refine ⟨46845867071018234735989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 249844624378763918591941 46845867071018234735989)
                ·
                  rfl

theorem cell20_307908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 4, 4].length) (baseStart_307908 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_307908 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_307908 prefixEnd_307908 := by exact prefixLift 307908
  have htrace : WordTrace (prefixWord ++ tailWord_307908) baseStart_307908 baseEnd_307908 := by
    simpa [prefixWord, tailWord_307908, baseEnd_307908] using wordTrace_append hprefix tailTrace_307908
  have hstable : (prefixWord ++ tailWord_307908).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307908).length < 2 ^ (prefixWord ++ tailWord_307908).sum := by decide
  have hdescent : baseEnd_307908 < baseStart_307908 := by decide
  rcases family_descends (prefixWord ++ tailWord_307908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307918 : List Nat := [4, 1, 1, 1, 3, 4, 1, 3, 2]
def baseStart_307918 : Nat := 118140960795 + 307918 * 2 ^ 59
def prefixEnd_307918 : Nat := 4983230072969 + 3 ^ 40 * 307918 * 2
def baseEnd_307918 : Nat := 140542165485539113874593

theorem tailTrace_307918 : CollatzResearch.WordTrace tailWord_307918 prefixEnd_307918 140542165485539113874593 := by
  unfold tailWord_307918
  simp only [CollatzResearch.WordTrace]
  refine ⟨1403836512309143631593551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7487128065648766035165605 1403836512309143631593551)
  ·
    refine ⟨2105754768463715447390327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1403836512309143631593551 2105754768463715447390327)
    ·
      refine ⟨3158632152695573171085491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2105754768463715447390327 3158632152695573171085491)
      ·
        refine ⟨4737948229043359756628237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3158632152695573171085491 4737948229043359756628237)
        ·
          refine ⟨1776730585891259908735589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4737948229043359756628237 1776730585891259908735589)
          ·
            refine ⟨333136984854611232887923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1776730585891259908735589 333136984854611232887923)
            ·
              refine ⟨499705477281916849331885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 333136984854611232887923 499705477281916849331885)
              ·
                refine ⟨187389553980718818499457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 499705477281916849331885 187389553980718818499457)
                ·
                  refine ⟨140542165485539113874593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 187389553980718818499457 140542165485539113874593)
                  ·
                    rfl

theorem cell20_307918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 1, 3, 2].length) (baseStart_307918 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_307918 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_307918 prefixEnd_307918 := by exact prefixLift 307918
  have htrace : WordTrace (prefixWord ++ tailWord_307918) baseStart_307918 baseEnd_307918 := by
    simpa [prefixWord, tailWord_307918, baseEnd_307918] using wordTrace_append hprefix tailTrace_307918
  have hstable : (prefixWord ++ tailWord_307918).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307918).length < 2 ^ (prefixWord ++ tailWord_307918).sum := by decide
  have hdescent : baseEnd_307918 < baseStart_307918 := by decide
  rcases family_descends (prefixWord ++ tailWord_307918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307925 : List Nat := [1, 3, 2, 5, 2, 1, 6]
def baseStart_307925 : Nat := 118140960795 + 307925 * 2 ^ 59
def prefixEnd_307925 : Nat := 4983230072969 + 3 ^ 40 * 307925 * 2
def baseEnd_307925 : Nat := 15616151164030911182359

theorem tailTrace_307925 : CollatzResearch.WordTrace tailWord_307925 prefixEnd_307925 15616151164030911182359 := by
  unfold tailWord_307925
  simp only [CollatzResearch.WordTrace]
  refine ⟨11230947409447789248253229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7487298272965192832168819 11230947409447789248253229)
  ·
    refine ⟨4211605278542920968094961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11230947409447789248253229 4211605278542920968094961)
    ·
      refine ⟨3158703958907190726071221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4211605278542920968094961 3158703958907190726071221)
      ·
        refine ⟨296128496147549130569177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3158703958907190726071221 296128496147549130569177)
        ·
          refine ⟨222096372110661847926883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 296128496147549130569177 222096372110661847926883)
          ·
            refine ⟨333144558165992771890325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 222096372110661847926883 333144558165992771890325)
            ·
              refine ⟨15616151164030911182359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 333144558165992771890325 15616151164030911182359)
              ·
                rfl

theorem cell20_307925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 6].length) (baseStart_307925 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_307925 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_307925 prefixEnd_307925 := by exact prefixLift 307925
  have htrace : WordTrace (prefixWord ++ tailWord_307925) baseStart_307925 baseEnd_307925 := by
    simpa [prefixWord, tailWord_307925, baseEnd_307925] using wordTrace_append hprefix tailTrace_307925
  have hstable : (prefixWord ++ tailWord_307925).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307925).length < 2 ^ (prefixWord ++ tailWord_307925).sum := by decide
  have hdescent : baseEnd_307925 < baseStart_307925 := by decide
  rcases family_descends (prefixWord ++ tailWord_307925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307936 : List Nat := [2, 1, 1, 3, 1, 2, 1, 6, 3]
def baseStart_307936 : Nat := 118140960795 + 307936 * 2 ^ 59
def prefixEnd_307936 : Nat := 4983230072969 + 3 ^ 40 * 307936 * 2
def baseEnd_307936 : Nat := 140550381176011051274519

theorem tailTrace_307936 : CollatzResearch.WordTrace tailWord_307936 prefixEnd_307936 140550381176011051274519 := by
  unfold tailWord_307936
  simp only [CollatzResearch.WordTrace]
  refine ⟨5615674306203969063451831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7487565741605292084602441 5615674306203969063451831)
  ·
    refine ⟨8423511459305953595177747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5615674306203969063451831 8423511459305953595177747)
    ·
      refine ⟨12635267188958930392766621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8423511459305953595177747 12635267188958930392766621)
      ·
        refine ⟨4738225195859598897287483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12635267188958930392766621 4738225195859598897287483)
        ·
          refine ⟨7107337793789398345931225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4738225195859598897287483 7107337793789398345931225)
          ·
            refine ⟨5330503345342048759448419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7107337793789398345931225 5330503345342048759448419)
            ·
              refine ⟨7995755018013073139172629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5330503345342048759448419 7995755018013073139172629)
              ·
                refine ⟨374801016469362803398717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7995755018013073139172629 374801016469362803398717)
                ·
                  refine ⟨140550381176011051274519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 374801016469362803398717 140550381176011051274519)
                  ·
                    rfl

theorem cell20_307936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 6, 3].length) (baseStart_307936 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_307936 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_307936 prefixEnd_307936 := by exact prefixLift 307936
  have htrace : WordTrace (prefixWord ++ tailWord_307936) baseStart_307936 baseEnd_307936 := by
    simpa [prefixWord, tailWord_307936, baseEnd_307936] using wordTrace_append hprefix tailTrace_307936
  have hstable : (prefixWord ++ tailWord_307936).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307936).length < 2 ^ (prefixWord ++ tailWord_307936).sum := by decide
  have hdescent : baseEnd_307936 < baseStart_307936 := by decide
  rcases family_descends (prefixWord ++ tailWord_307936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_307939 : List Nat := [1, 1, 1, 7, 1, 3, 1, 1, 4]
def baseStart_307939 : Nat := 118140960795 + 307939 * 2 ^ 59
def prefixEnd_307939 : Nat := 4983230072969 + 3 ^ 40 * 307939 * 2
def baseEnd_307939 : Nat := 140551750457756374174507

theorem tailTrace_307939 : CollatzResearch.WordTrace tailWord_307939 prefixEnd_307939 140551750457756374174507 := by
  unfold tailWord_307939
  simp only [CollatzResearch.WordTrace]
  refine ⟨11231458031397069639262871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7487638687598046426175247 11231458031397069639262871)
  ·
    refine ⟨16847187047095604458894307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11231458031397069639262871 16847187047095604458894307)
    ·
      refine ⟨25270780570643406688341461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16847187047095604458894307 25270780570643406688341461)
      ·
        refine ⟨592283919624454844258003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 25270780570643406688341461 592283919624454844258003)
        ·
          refine ⟨888425879436682266387005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 592283919624454844258003 888425879436682266387005)
          ·
            refine ⟨333159704788755849895127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 888425879436682266387005 333159704788755849895127)
            ·
              refine ⟨499739557183133774842691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 333159704788755849895127 499739557183133774842691)
              ·
                refine ⟨749609335774700662264037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 499739557183133774842691 749609335774700662264037)
                ·
                  refine ⟨140551750457756374174507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 749609335774700662264037 140551750457756374174507)
                  ·
                    rfl

theorem cell20_307939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 1, 1, 4].length) (baseStart_307939 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_307939 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_307939 prefixEnd_307939 := by exact prefixLift 307939
  have htrace : WordTrace (prefixWord ++ tailWord_307939) baseStart_307939 baseEnd_307939 := by
    simpa [prefixWord, tailWord_307939, baseEnd_307939] using wordTrace_append hprefix tailTrace_307939
  have hstable : (prefixWord ++ tailWord_307939).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_307939).length < 2 ^ (prefixWord ++ tailWord_307939).sum := by decide
  have hdescent : baseEnd_307939 < baseStart_307939 := by decide
  rcases family_descends (prefixWord ++ tailWord_307939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308012 : List Nat := [2, 2, 1, 1, 1, 4, 1, 5, 3]
def baseStart_308012 : Nat := 118140960795 + 308012 * 2 ^ 59
def prefixEnd_308012 : Nat := 4983230072969 + 3 ^ 40 * 308012 * 2
def baseEnd_308012 : Nat := 140585069646892564740875

theorem tailTrace_308012 : CollatzResearch.WordTrace tailWord_308012 prefixEnd_308012 140585069646892564740875 := by
  unfold tailWord_308012
  simp only [CollatzResearch.WordTrace]
  refine ⟨5617060280066301553335145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7489413706755068737780193 5617060280066301553335145)
  ·
    refine ⟨4212795210049726165001359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5617060280066301553335145 4212795210049726165001359)
    ·
      refine ⟨6319192815074589247502039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4212795210049726165001359 6319192815074589247502039)
      ·
        refine ⟨9478789222611883871253059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6319192815074589247502039 9478789222611883871253059)
        ·
          refine ⟨14218183833917825806879589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9478789222611883871253059 14218183833917825806879589)
          ·
            refine ⟨2665909468859592338789923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14218183833917825806879589 2665909468859592338789923)
            ·
              refine ⟨3998864203289388508184885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2665909468859592338789923 3998864203289388508184885)
              ·
                refine ⟨374893519058380172642333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3998864203289388508184885 374893519058380172642333)
                ·
                  refine ⟨140585069646892564740875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 374893519058380172642333 140585069646892564740875)
                  ·
                    rfl

theorem cell20_308012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 3].length) (baseStart_308012 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_308012 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_308012 prefixEnd_308012 := by exact prefixLift 308012
  have htrace : WordTrace (prefixWord ++ tailWord_308012) baseStart_308012 baseEnd_308012 := by
    simpa [prefixWord, tailWord_308012, baseEnd_308012] using wordTrace_append hprefix tailTrace_308012
  have hstable : (prefixWord ++ tailWord_308012).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308012).length < 2 ^ (prefixWord ++ tailWord_308012).sum := by decide
  have hdescent : baseEnd_308012 < baseStart_308012 := by decide
  rcases family_descends (prefixWord ++ tailWord_308012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308019 : List Nat := [1, 1, 1, 2, 6, 1, 1, 1, 6]
def baseStart_308019 : Nat := 118140960795 + 308019 * 2 ^ 59
def prefixEnd_308019 : Nat := 4983230072969 + 3 ^ 40 * 308019 * 2
def baseEnd_308019 : Nat := 140588264637631651507513

theorem tailTrace_308019 : CollatzResearch.WordTrace tailWord_308019 prefixEnd_308019 140588264637631651507513 := by
  unfold tailWord_308019
  simp only [CollatzResearch.WordTrace]
  refine ⟨11234375871107243302175111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7489583914071495534783407 11234375871107243302175111)
  ·
    refine ⟨16851563806660864953262667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11234375871107243302175111 16851563806660864953262667)
    ·
      refine ⟨25277345709991297429894001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16851563806660864953262667 25277345709991297429894001)
      ·
        refine ⟨18958009282493473072420501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25277345709991297429894001 18958009282493473072420501)
        ·
          refine ⟨888656685116881550269711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 18958009282493473072420501 888656685116881550269711)
          ·
            refine ⟨1332985027675322325404567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 888656685116881550269711 1332985027675322325404567)
            ·
              refine ⟨1999477541512983488106851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1332985027675322325404567 1999477541512983488106851)
              ·
                refine ⟨2999216312269475232160277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1999477541512983488106851 2999216312269475232160277)
                ·
                  refine ⟨140588264637631651507513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2999216312269475232160277 140588264637631651507513)
                  ·
                    rfl

theorem cell20_308019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 1, 6].length) (baseStart_308019 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_308019 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_308019 prefixEnd_308019 := by exact prefixLift 308019
  have htrace : WordTrace (prefixWord ++ tailWord_308019) baseStart_308019 baseEnd_308019 := by
    simpa [prefixWord, tailWord_308019, baseEnd_308019] using wordTrace_append hprefix tailTrace_308019
  have hstable : (prefixWord ++ tailWord_308019).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308019).length < 2 ^ (prefixWord ++ tailWord_308019).sum := by decide
  have hdescent : baseEnd_308019 < baseStart_308019 := by decide
  rcases family_descends (prefixWord ++ tailWord_308019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308050 : List Nat := [3, 2, 2, 1, 1, 2, 3, 1, 5]
def baseStart_308050 : Nat := 118140960795 + 308050 * 2 ^ 59
def prefixEnd_308050 : Nat := 4983230072969 + 3 ^ 40 * 308050 * 2
def baseEnd_308050 : Nat := 140602413882333321474053

theorem tailTrace_308050 : CollatzResearch.WordTrace tailWord_308050 prefixEnd_308050 140602413882333321474053 := by
  unfold tailWord_308050
  simp only [CollatzResearch.WordTrace]
  refine ⟨2808876633498733899138401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7490337689329957064369069 2808876633498733899138401)
  ·
    refine ⟨2106657475124050424353801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2808876633498733899138401 2106657475124050424353801)
    ·
      refine ⟨1579993106343037818265351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2106657475124050424353801 1579993106343037818265351)
      ·
        refine ⟨2369989659514556727398027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1579993106343037818265351 2369989659514556727398027)
        ·
          refine ⟨3554984489271835091097041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2369989659514556727398027 3554984489271835091097041)
          ·
            refine ⟨2666238366953876318322781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3554984489271835091097041 2666238366953876318322781)
            ·
              refine ⟨999839387607703619371043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2666238366953876318322781 999839387607703619371043)
              ·
                refine ⟨1499759081411555429056565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 999839387607703619371043 1499759081411555429056565)
                ·
                  refine ⟨140602413882333321474053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1499759081411555429056565 140602413882333321474053)
                  ·
                    rfl

theorem cell20_308050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 1, 5].length) (baseStart_308050 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_308050 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_308050 prefixEnd_308050 := by exact prefixLift 308050
  have htrace : WordTrace (prefixWord ++ tailWord_308050) baseStart_308050 baseEnd_308050 := by
    simpa [prefixWord, tailWord_308050, baseEnd_308050] using wordTrace_append hprefix tailTrace_308050
  have hstable : (prefixWord ++ tailWord_308050).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308050).length < 2 ^ (prefixWord ++ tailWord_308050).sum := by decide
  have hdescent : baseEnd_308050 < baseStart_308050 := by decide
  rcases family_descends (prefixWord ++ tailWord_308050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308057 : List Nat := [1, 2, 1, 2, 2, 4, 1, 3, 4]
def baseStart_308057 : Nat := 118140960795 + 308057 * 2 ^ 59
def prefixEnd_308057 : Nat := 4983230072969 + 3 ^ 40 * 308057 * 2
def baseEnd_308057 : Nat := 140605608873072408240691

theorem tailTrace_308057 : CollatzResearch.WordTrace tailWord_308057 prefixEnd_308057 140605608873072408240691 := by
  unfold tailWord_308057
  simp only [CollatzResearch.WordTrace]
  refine ⟨11235761844969575792058425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7490507896646383861372283 11235761844969575792058425)
  ·
    refine ⟨8426821383727181844043819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11235761844969575792058425 8426821383727181844043819)
    ·
      refine ⟨12640232075590772766065729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8426821383727181844043819 12640232075590772766065729)
      ·
        refine ⟨9480174056693079574549297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12640232075590772766065729 9480174056693079574549297)
        ·
          refine ⟨7110130542519809680911973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9480174056693079574549297 7110130542519809680911973)
          ·
            refine ⟨1333149476722464315170995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7110130542519809680911973 1333149476722464315170995)
            ·
              refine ⟨1999724215083696472756493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1333149476722464315170995 1999724215083696472756493)
              ·
                refine ⟨749896580656386177283685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1999724215083696472756493 749896580656386177283685)
                ·
                  refine ⟨140605608873072408240691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 749896580656386177283685 140605608873072408240691)
                  ·
                    rfl

theorem cell20_308057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 3, 4].length) (baseStart_308057 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_308057 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_308057 prefixEnd_308057 := by exact prefixLift 308057
  have htrace : WordTrace (prefixWord ++ tailWord_308057) baseStart_308057 baseEnd_308057 := by
    simpa [prefixWord, tailWord_308057, baseEnd_308057] using wordTrace_append hprefix tailTrace_308057
  have hstable : (prefixWord ++ tailWord_308057).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308057).length < 2 ^ (prefixWord ++ tailWord_308057).sum := by decide
  have hdescent : baseEnd_308057 < baseStart_308057 := by decide
  rcases family_descends (prefixWord ++ tailWord_308057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308064 : List Nat := [2, 1, 1, 3, 3, 1, 2, 7]
def baseStart_308064 : Nat := 118140960795 + 308064 * 2 ^ 59
def prefixEnd_308064 : Nat := 4983230072969 + 3 ^ 40 * 308064 * 2
def baseEnd_308064 : Nat := 46869601287937165002443

theorem tailTrace_308064 : CollatzResearch.WordTrace tailWord_308064 prefixEnd_308064 46869601287937165002443 := by
  unfold tailWord_308064
  simp only [CollatzResearch.WordTrace]
  refine ⟨5618008577972107993781623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7490678103962810658375497 5618008577972107993781623)
  ·
    refine ⟨8427012866958161990672435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5618008577972107993781623 8427012866958161990672435)
    ·
      refine ⟨12640519300437242986008653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8427012866958161990672435 12640519300437242986008653)
      ·
        refine ⟨4740194737663966119753245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12640519300437242986008653 4740194737663966119753245)
        ·
          refine ⟨1777573026623987294907467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4740194737663966119753245 1777573026623987294907467)
          ·
            refine ⟨2666359539935980942361201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1777573026623987294907467 2666359539935980942361201)
            ·
              refine ⟨1999769654951985706770901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2666359539935980942361201 1999769654951985706770901)
              ·
                refine ⟨46869601287937165002443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1999769654951985706770901 46869601287937165002443)
                ·
                  rfl

theorem cell20_308064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 7].length) (baseStart_308064 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_308064 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_308064 prefixEnd_308064 := by exact prefixLift 308064
  have htrace : WordTrace (prefixWord ++ tailWord_308064) baseStart_308064 baseEnd_308064 := by
    simpa [prefixWord, tailWord_308064, baseEnd_308064] using wordTrace_append hprefix tailTrace_308064
  have hstable : (prefixWord ++ tailWord_308064).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308064).length < 2 ^ (prefixWord ++ tailWord_308064).sum := by decide
  have hdescent : baseEnd_308064 < baseStart_308064 := by decide
  rcases family_descends (prefixWord ++ tailWord_308064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308081 : List Nat := [1, 2, 2, 2, 1, 4, 4, 4]
def baseStart_308081 : Nat := 118140960795 + 308081 * 2 ^ 59
def prefixEnd_308081 : Nat := 4983230072969 + 3 ^ 40 * 308081 * 2
def baseEnd_308081 : Nat := 46872187709011663813531

theorem tailTrace_308081 : CollatzResearch.WordTrace tailWord_308081 prefixEnd_308081 46872187709011663813531 := by
  unfold tailWord_308081
  simp only [CollatzResearch.WordTrace]
  refine ⟨11236637196882627890932097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7491091464588418593954731 11236637196882627890932097)
  ·
    refine ⟨8427477897661970918199073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11236637196882627890932097 8427477897661970918199073)
    ·
      refine ⟨6320608423246478188649305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8427477897661970918199073 6320608423246478188649305)
      ·
        refine ⟨4740456317434858641486979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6320608423246478188649305 4740456317434858641486979)
        ·
          refine ⟨7110684476152287962230469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4740456317434858641486979 7110684476152287962230469)
          ·
            refine ⟨1333253339278553992918213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7110684476152287962230469 1333253339278553992918213)
            ·
              refine ⟨249985001114728873672165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1333253339278553992918213 249985001114728873672165)
              ·
                refine ⟨46872187709011663813531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 249985001114728873672165 46872187709011663813531)
                ·
                  rfl

theorem cell20_308081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 4, 4].length) (baseStart_308081 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_308081 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_308081 prefixEnd_308081 := by exact prefixLift 308081
  have htrace : WordTrace (prefixWord ++ tailWord_308081) baseStart_308081 baseEnd_308081 := by
    simpa [prefixWord, tailWord_308081, baseEnd_308081] using wordTrace_append hprefix tailTrace_308081
  have hstable : (prefixWord ++ tailWord_308081).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308081).length < 2 ^ (prefixWord ++ tailWord_308081).sum := by decide
  have hdescent : baseEnd_308081 < baseStart_308081 := by decide
  rcases family_descends (prefixWord ++ tailWord_308081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308118 : List Nat := [5, 3, 1, 1, 1, 1, 4, 1, 3]
def baseStart_308118 : Nat := 118140960795 + 308118 * 2 ^ 59
def prefixEnd_308118 : Nat := 4983230072969 + 3 ^ 40 * 308118 * 2
def baseEnd_308118 : Nat := 140633450935227307207109

theorem tailTrace_308118 : CollatzResearch.WordTrace tailWord_308118 prefixEnd_308118 140633450935227307207109 := by
  unfold tailWord_308118
  simp only [CollatzResearch.WordTrace]
  refine ⟨702374168609286450626813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7491991131832388806686005 702374168609286450626813)
  ·
    refine ⟨263390313228482418985055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 702374168609286450626813 263390313228482418985055)
    ·
      refine ⟨395085469842723628477583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 263390313228482418985055 395085469842723628477583)
      ·
        refine ⟨592628204764085442716375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 395085469842723628477583 592628204764085442716375)
        ·
          refine ⟨888942307146128164074563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 592628204764085442716375 888942307146128164074563)
          ·
            refine ⟨1333413460719192246111845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 888942307146128164074563 1333413460719192246111845)
            ·
              refine ⟨250015023884848546145971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1333413460719192246111845 250015023884848546145971)
              ·
                refine ⟨375022535827272819218957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 250015023884848546145971 375022535827272819218957)
                ·
                  refine ⟨140633450935227307207109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 375022535827272819218957 140633450935227307207109)
                  ·
                    rfl

theorem cell20_308118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_308118 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_308118 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_308118 prefixEnd_308118 := by exact prefixLift 308118
  have htrace : WordTrace (prefixWord ++ tailWord_308118) baseStart_308118 baseEnd_308118 := by
    simpa [prefixWord, tailWord_308118, baseEnd_308118] using wordTrace_append hprefix tailTrace_308118
  have hstable : (prefixWord ++ tailWord_308118).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308118).length < 2 ^ (prefixWord ++ tailWord_308118).sum := by decide
  have hdescent : baseEnd_308118 < baseStart_308118 := by decide
  rcases family_descends (prefixWord ++ tailWord_308118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308147 : List Nat := [1, 1, 1, 2, 3, 1, 2, 4, 5]
def baseStart_308147 : Nat := 118140960795 + 308147 * 2 ^ 59
def prefixEnd_308147 : Nat := 4983230072969 + 3 ^ 40 * 308147 * 2
def baseEnd_308147 : Nat := 140646687325432095240323

theorem tailTrace_308147 : CollatzResearch.WordTrace tailWord_308147 prefixEnd_308147 140646687325432095240323 := by
  unfold tailWord_308147
  simp only [CollatzResearch.WordTrace]
  refine ⟨11239044414643521162834695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7492696276429014108556463 11239044414643521162834695)
  ·
    refine ⟨16858566621965281744252043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11239044414643521162834695 16858566621965281744252043)
    ·
      refine ⟨25287849932947922616378065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16858566621965281744252043 25287849932947922616378065)
      ·
        refine ⟨18965887449710941962283549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25287849932947922616378065 18965887449710941962283549)
        ·
          refine ⟨7112207793641603235856331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18965887449710941962283549 7112207793641603235856331)
          ·
            refine ⟨10668311690462404853784497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7112207793641603235856331 10668311690462404853784497)
            ·
              refine ⟨8001233767846803640338373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10668311690462404853784497 8001233767846803640338373)
              ·
                refine ⟨1500231331471275682563445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8001233767846803640338373 1500231331471275682563445)
                ·
                  refine ⟨140646687325432095240323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1500231331471275682563445 140646687325432095240323)
                  ·
                    rfl

theorem cell20_308147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 4, 5].length) (baseStart_308147 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_308147 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_308147 prefixEnd_308147 := by exact prefixLift 308147
  have htrace : WordTrace (prefixWord ++ tailWord_308147) baseStart_308147 baseEnd_308147 := by
    simpa [prefixWord, tailWord_308147, baseEnd_308147] using wordTrace_append hprefix tailTrace_308147
  have hstable : (prefixWord ++ tailWord_308147).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308147).length < 2 ^ (prefixWord ++ tailWord_308147).sum := by decide
  have hdescent : baseEnd_308147 < baseStart_308147 := by decide
  rcases family_descends (prefixWord ++ tailWord_308147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308157 : List Nat := [1, 4, 1, 2, 5, 7]
def baseStart_308157 : Nat := 118140960795 + 308157 * 2 ^ 59
def prefixEnd_308157 : Nat := 4983230072969 + 3 ^ 40 * 308157 * 2
def baseEnd_308157 : Nat := 5209305614737648329887

theorem tailTrace_308157 : CollatzResearch.WordTrace tailWord_308157 prefixEnd_308157 5209305614737648329887 := by
  unfold tailWord_308157
  simp only [CollatzResearch.WordTrace]
  refine ⟨11239409144607292870698725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7492939429738195247132483 11239409144607292870698725)
  ·
    refine ⟨2107389214613867413256011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11239409144607292870698725 2107389214613867413256011)
    ·
      refine ⟨3161083821920801119884017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2107389214613867413256011 3161083821920801119884017)
      ·
        refine ⟨2370812866440600839913013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3161083821920801119884017 2370812866440600839913013)
        ·
          refine ⟨222263706228806328741845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2370812866440600839913013 222263706228806328741845)
          ·
            refine ⟨5209305614737648329887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 222263706228806328741845 5209305614737648329887)
            ·
              rfl

theorem cell20_308157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 5, 7].length) (baseStart_308157 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_308157 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_308157 prefixEnd_308157 := by exact prefixLift 308157
  have htrace : WordTrace (prefixWord ++ tailWord_308157) baseStart_308157 baseEnd_308157 := by
    simpa [prefixWord, tailWord_308157, baseEnd_308157] using wordTrace_append hprefix tailTrace_308157
  have hstable : (prefixWord ++ tailWord_308157).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308157).length < 2 ^ (prefixWord ++ tailWord_308157).sum := by decide
  have hdescent : baseEnd_308157 < baseStart_308157 := by decide
  rcases family_descends (prefixWord ++ tailWord_308157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308166 : List Nat := [6, 1, 3, 1, 2, 1, 1, 5]
def baseStart_308166 : Nat := 118140960795 + 308166 * 2 ^ 59
def prefixEnd_308166 : Nat := 4983230072969 + 3 ^ 40 * 308166 * 2
def baseEnd_308166 : Nat := 46885119814384157868971

theorem tailTrace_308166 : CollatzResearch.WordTrace tailWord_308166 prefixEnd_308166 46885119814384157868971 := by
  unfold tailWord_308166
  simp only [CollatzResearch.WordTrace]
  refine ⟨351241793799208981493011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 7493158267716458271850901 351241793799208981493011)
  ·
    refine ⟨526862690698813472239517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 351241793799208981493011 526862690698813472239517)
    ·
      refine ⟨197573509012055052089819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 526862690698813472239517 197573509012055052089819)
      ·
        refine ⟨296360263518082578134729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197573509012055052089819 296360263518082578134729)
        ·
          refine ⟨222270197638561933601047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 296360263518082578134729 222270197638561933601047)
          ·
            refine ⟨333405296457842900401571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 222270197638561933601047 333405296457842900401571)
            ·
              refine ⟨500107944686764350602357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 333405296457842900401571 500107944686764350602357)
              ·
                refine ⟨46885119814384157868971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 500107944686764350602357 46885119814384157868971)
                ·
                  rfl

theorem cell20_308166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_308166 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_308166 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_308166 prefixEnd_308166 := by exact prefixLift 308166
  have htrace : WordTrace (prefixWord ++ tailWord_308166) baseStart_308166 baseEnd_308166 := by
    simpa [prefixWord, tailWord_308166, baseEnd_308166] using wordTrace_append hprefix tailTrace_308166
  have hstable : (prefixWord ++ tailWord_308166).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308166).length < 2 ^ (prefixWord ++ tailWord_308166).sum := by decide
  have hdescent : baseEnd_308166 < baseStart_308166 := by decide
  rcases family_descends (prefixWord ++ tailWord_308166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308167 : List Nat := [1, 1, 4, 1, 1, 2, 6, 2, 2]
def baseStart_308167 : Nat := 118140960795 + 308167 * 2 ^ 59
def prefixEnd_308167 : Nat := 4983230072969 + 3 ^ 40 * 308167 * 2
def baseEnd_308167 : Nat := 140655815870400914573575

theorem tailTrace_308167 : CollatzResearch.WordTrace tailWord_308167 prefixEnd_308167 140655815870400914573575 := by
  unfold tailWord_308167
  simp only [CollatzResearch.WordTrace]
  refine ⟨11239773874571064578562755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7493182583047376385708503 11239773874571064578562755)
  ·
    refine ⟨16859660811856596867844133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11239773874571064578562755 16859660811856596867844133)
    ·
      refine ⟨3161186402223111912720775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16859660811856596867844133 3161186402223111912720775)
      ·
        refine ⟨4741779603334667869081163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3161186402223111912720775 4741779603334667869081163)
        ·
          refine ⟨7112669405002001803621745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4741779603334667869081163 7112669405002001803621745)
          ·
            refine ⟨5334502053751501352716309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7112669405002001803621745 5334502053751501352716309)
            ·
              refine ⟨250054783769601625908577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 5334502053751501352716309 250054783769601625908577)
              ·
                refine ⟨187541087827201219431433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 250054783769601625908577 187541087827201219431433)
                ·
                  refine ⟨140655815870400914573575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 187541087827201219431433 140655815870400914573575)
                  ·
                    rfl

theorem cell20_308167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 6, 2, 2].length) (baseStart_308167 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_308167 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_308167 prefixEnd_308167 := by exact prefixLift 308167
  have htrace : WordTrace (prefixWord ++ tailWord_308167) baseStart_308167 baseEnd_308167 := by
    simpa [prefixWord, tailWord_308167, baseEnd_308167] using wordTrace_append hprefix tailTrace_308167
  have hstable : (prefixWord ++ tailWord_308167).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308167).length < 2 ^ (prefixWord ++ tailWord_308167).sum := by decide
  have hdescent : baseEnd_308167 < baseStart_308167 := by decide
  rcases family_descends (prefixWord ++ tailWord_308167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308195 : List Nat := [1, 1, 1, 6, 1, 1, 5, 4]
def baseStart_308195 : Nat := 118140960795 + 308195 * 2 ^ 59
def prefixEnd_308195 : Nat := 4983230072969 + 3 ^ 40 * 308195 * 2
def baseEnd_308195 : Nat := 46889531944452420546709

theorem tailTrace_308195 : CollatzResearch.WordTrace tailWord_308195 prefixEnd_308195 46889531944452420546709 := by
  unfold tailWord_308195
  simp only [CollatzResearch.WordTrace]
  refine ⟨11240795118469625360582039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7493863412313083573721359 11240795118469625360582039)
  ·
    refine ⟨16861192677704438040873059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11240795118469625360582039 16861192677704438040873059)
    ·
      refine ⟨25291789016556657061309589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16861192677704438040873059 25291789016556657061309589)
      ·
        refine ⟨1185552610151093299748887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 25291789016556657061309589 1185552610151093299748887)
        ·
          refine ⟨1778328915226639949623331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1185552610151093299748887 1778328915226639949623331)
          ·
            refine ⟨2667493372839959924434997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1778328915226639949623331 2667493372839959924434997)
            ·
              refine ⟨250077503703746242915781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2667493372839959924434997 250077503703746242915781)
              ·
                refine ⟨46889531944452420546709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 250077503703746242915781 46889531944452420546709)
                ·
                  rfl

theorem cell20_308195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 5, 4].length) (baseStart_308195 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_308195 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_308195 prefixEnd_308195 := by exact prefixLift 308195
  have htrace : WordTrace (prefixWord ++ tailWord_308195) baseStart_308195 baseEnd_308195 := by
    simpa [prefixWord, tailWord_308195, baseEnd_308195] using wordTrace_append hprefix tailTrace_308195
  have hstable : (prefixWord ++ tailWord_308195).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308195).length < 2 ^ (prefixWord ++ tailWord_308195).sum := by decide
  have hdescent : baseEnd_308195 < baseStart_308195 := by decide
  rcases family_descends (prefixWord ++ tailWord_308195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308260 : List Nat := [2, 3, 1, 4, 1, 3, 1, 3, 2]
def baseStart_308260 : Nat := 118140960795 + 308260 * 2 ^ 59
def prefixEnd_308260 : Nat := 4983230072969 + 3 ^ 40 * 308260 * 2
def baseEnd_308260 : Nat := 140698263604505924473195

theorem tailTrace_308260 : CollatzResearch.WordTrace tailWord_308260 prefixEnd_308260 140698263604505924473195 := by
  unfold tailWord_308260
  simp only [CollatzResearch.WordTrace]
  refine ⟨5621582931617070730849117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7495443908822760974465489 5621582931617070730849117)
  ·
    refine ⟨2108093599356401524068419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5621582931617070730849117 2108093599356401524068419)
    ·
      refine ⟨3162140399034602286102629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2108093599356401524068419 3162140399034602286102629)
      ·
        refine ⟨592901324818987928644243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3162140399034602286102629 592901324818987928644243)
        ·
          refine ⟨889351987228481892966365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 592901324818987928644243 889351987228481892966365)
          ·
            refine ⟨333506995210680709862387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 889351987228481892966365 333506995210680709862387)
            ·
              refine ⟨500260492816021064793581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 333506995210680709862387 500260492816021064793581)
              ·
                refine ⟨187597684806007899297593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 500260492816021064793581 187597684806007899297593)
                ·
                  refine ⟨140698263604505924473195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 187597684806007899297593 140698263604505924473195)
                  ·
                    rfl

theorem cell20_308260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 1, 3, 2].length) (baseStart_308260 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_308260 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_308260 prefixEnd_308260 := by exact prefixLift 308260
  have htrace : WordTrace (prefixWord ++ tailWord_308260) baseStart_308260 baseEnd_308260 := by
    simpa [prefixWord, tailWord_308260, baseEnd_308260] using wordTrace_append hprefix tailTrace_308260
  have hstable : (prefixWord ++ tailWord_308260).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308260).length < 2 ^ (prefixWord ++ tailWord_308260).sum := by decide
  have hdescent : baseEnd_308260 < baseStart_308260 := by decide
  rcases family_descends (prefixWord ++ tailWord_308260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308261 : List Nat := [1, 3, 1, 2, 2, 2, 1, 1, 7]
def baseStart_308261 : Nat := 118140960795 + 308261 * 2 ^ 59
def prefixEnd_308261 : Nat := 4983230072969 + 3 ^ 40 * 308261 * 2
def baseEnd_308261 : Nat := 140698720031754365439857

theorem tailTrace_308261 : CollatzResearch.WordTrace tailWord_308261 prefixEnd_308261 140698720031754365439857 := by
  unfold tailWord_308261
  simp only [CollatzResearch.WordTrace]
  refine ⟨11243202336230518632484637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7495468224153679088323091 11243202336230518632484637)
  ·
    refine ⟨4216200876086444487181739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11243202336230518632484637 4216200876086444487181739)
    ·
      refine ⟨6324301314129666730772609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4216200876086444487181739 6324301314129666730772609)
      ·
        refine ⟨4743225985597250048079457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6324301314129666730772609 4743225985597250048079457)
        ·
          refine ⟨3557419489197937536059593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4743225985597250048079457 3557419489197937536059593)
          ·
            refine ⟨2668064616898453152044695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3557419489197937536059593 2668064616898453152044695)
            ·
              refine ⟨4002096925347679728067043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2668064616898453152044695 4002096925347679728067043)
              ·
                refine ⟨6003145388021519592100565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4002096925347679728067043 6003145388021519592100565)
                ·
                  refine ⟨140698720031754365439857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6003145388021519592100565 140698720031754365439857)
                  ·
                    rfl

theorem cell20_308261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 1, 7].length) (baseStart_308261 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_308261 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_308261 prefixEnd_308261 := by exact prefixLift 308261
  have htrace : WordTrace (prefixWord ++ tailWord_308261) baseStart_308261 baseEnd_308261 := by
    simpa [prefixWord, tailWord_308261, baseEnd_308261] using wordTrace_append hprefix tailTrace_308261
  have hstable : (prefixWord ++ tailWord_308261).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308261).length < 2 ^ (prefixWord ++ tailWord_308261).sum := by decide
  have hdescent : baseEnd_308261 < baseStart_308261 := by decide
  rcases family_descends (prefixWord ++ tailWord_308261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308295 : List Nat := [1, 1, 4, 1, 3, 2, 4, 1, 3]
def baseStart_308295 : Nat := 118140960795 + 308295 * 2 ^ 59
def prefixEnd_308295 : Nat := 4983230072969 + 3 ^ 40 * 308295 * 2
def baseEnd_308295 : Nat := 140714238558201358306385

theorem tailTrace_308295 : CollatzResearch.WordTrace tailWord_308295 prefixEnd_308295 140714238558201358306385 := by
  unfold tailWord_308295
  simp only [CollatzResearch.WordTrace]
  refine ⟨11244442418107342439222339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7496294945404894959481559 11244442418107342439222339)
  ·
    refine ⟨16866663627161013658833509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11244442418107342439222339 16866663627161013658833509)
    ·
      refine ⟨3162499430092690061031283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16866663627161013658833509 3162499430092690061031283)
      ·
        refine ⟨4743749145139035091546925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3162499430092690061031283 4743749145139035091546925)
        ·
          refine ⟨1778905929427138159330097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4743749145139035091546925 1778905929427138159330097)
          ·
            refine ⟨1334179447070353619497573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1778905929427138159330097 1334179447070353619497573)
            ·
              refine ⟨250158646325691303655795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1334179447070353619497573 250158646325691303655795)
              ·
                refine ⟨375237969488536955483693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 250158646325691303655795 375237969488536955483693)
                ·
                  refine ⟨140714238558201358306385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 375237969488536955483693 140714238558201358306385)
                  ·
                    rfl

theorem cell20_308295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 4, 1, 3].length) (baseStart_308295 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_308295 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_308295 prefixEnd_308295 := by exact prefixLift 308295
  have htrace : WordTrace (prefixWord ++ tailWord_308295) baseStart_308295 baseEnd_308295 := by
    simpa [prefixWord, tailWord_308295, baseEnd_308295] using wordTrace_append hprefix tailTrace_308295
  have hstable : (prefixWord ++ tailWord_308295).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308295).length < 2 ^ (prefixWord ++ tailWord_308295).sum := by decide
  have hdescent : baseEnd_308295 < baseStart_308295 := by decide
  rcases family_descends (prefixWord ++ tailWord_308295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308330 : List Nat := [3, 1, 3, 2, 2, 9]
def baseStart_308330 : Nat := 118140960795 + 308330 * 2 ^ 59
def prefixEnd_308330 : Nat := 4983230072969 + 3 ^ 40 * 308330 * 2
def baseEnd_308330 : Nat := 5212230130070251560725

theorem tailTrace_308330 : CollatzResearch.WordTrace tailWord_308330 prefixEnd_308330 5212230130070251560725 := by
  unfold tailWord_308330
  simp only [CollatzResearch.WordTrace]
  refine ⟨2811429743245135854186611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7497145981987028944497629 2811429743245135854186611)
  ·
    refine ⟨4217144614867703781279917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2811429743245135854186611 4217144614867703781279917)
    ·
      refine ⟨1581429230575388917979969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4217144614867703781279917 1581429230575388917979969)
      ·
        refine ⟨1186071922931541688484977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1581429230575388917979969 1186071922931541688484977)
        ·
          refine ⟨889553942198656266363733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1186071922931541688484977 889553942198656266363733)
          ·
            refine ⟨5212230130070251560725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 889553942198656266363733 5212230130070251560725)
            ·
              rfl

theorem cell20_308330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 9].length) (baseStart_308330 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_308330 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_308330 prefixEnd_308330 := by exact prefixLift 308330
  have htrace : WordTrace (prefixWord ++ tailWord_308330) baseStart_308330 baseEnd_308330 := by
    simpa [prefixWord, tailWord_308330, baseEnd_308330] using wordTrace_append hprefix tailTrace_308330
  have hstable : (prefixWord ++ tailWord_308330).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308330).length < 2 ^ (prefixWord ++ tailWord_308330).sum := by decide
  have hdescent : baseEnd_308330 < baseStart_308330 := by decide
  rcases family_descends (prefixWord ++ tailWord_308330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308333 : List Nat := [1, 5, 1, 1, 2, 3, 2, 2, 3]
def baseStart_308333 : Nat := 118140960795 + 308333 * 2 ^ 59
def prefixEnd_308333 : Nat := 4983230072969 + 3 ^ 40 * 308333 * 2
def baseEnd_308333 : Nat := 140731582793642115039563

theorem tailTrace_308333 : CollatzResearch.WordTrace tailWord_308333 prefixEnd_308333 140731582793642115039563 := by
  unfold tailWord_308333
  simp only [CollatzResearch.WordTrace]
  refine ⟨11245828391969674929105653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7497218927979783286070435 11245828391969674929105653)
  ·
    refine ⟨1054296411747157024603655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11245828391969674929105653 1054296411747157024603655)
    ·
      refine ⟨1581444617620735536905483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1054296411747157024603655 1581444617620735536905483)
      ·
        refine ⟨2372166926431103305358225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1581444617620735536905483 2372166926431103305358225)
        ·
          refine ⟨1779125194823327479018669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2372166926431103305358225 1779125194823327479018669)
          ·
            refine ⟨667171948058747804632001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1779125194823327479018669 667171948058747804632001)
            ·
              refine ⟨500378961044060853474001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 667171948058747804632001 500378961044060853474001)
              ·
                refine ⟨375284220783045640105501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 500378961044060853474001 375284220783045640105501)
                ·
                  refine ⟨140731582793642115039563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 375284220783045640105501 140731582793642115039563)
                  ·
                    rfl

theorem cell20_308333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 2, 2, 3].length) (baseStart_308333 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_308333 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_308333 prefixEnd_308333 := by exact prefixLift 308333
  have htrace : WordTrace (prefixWord ++ tailWord_308333) baseStart_308333 baseEnd_308333 := by
    simpa [prefixWord, tailWord_308333, baseEnd_308333] using wordTrace_append hprefix tailTrace_308333
  have hstable : (prefixWord ++ tailWord_308333).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308333).length < 2 ^ (prefixWord ++ tailWord_308333).sum := by decide
  have hdescent : baseEnd_308333 < baseStart_308333 := by decide
  rcases family_descends (prefixWord ++ tailWord_308333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308361 : List Nat := [1, 2, 1, 1, 4, 4, 1, 2, 4]
def baseStart_308361 : Nat := 118140960795 + 308361 * 2 ^ 59
def prefixEnd_308361 : Nat := 4983230072969 + 3 ^ 40 * 308361 * 2
def baseEnd_308361 : Nat := 140744362756598462106115

theorem tailTrace_308361 : CollatzResearch.WordTrace tailWord_308361 prefixEnd_308361 140744362756598462106115 := by
  unfold tailWord_308361
  simp only [CollatzResearch.WordTrace]
  refine ⟨11246849635868235711124937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7497899757245490474083291 11246849635868235711124937)
  ·
    refine ⟨8435137226901176783343703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11246849635868235711124937 8435137226901176783343703)
    ·
      refine ⟨12652705840351765175015555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8435137226901176783343703 12652705840351765175015555)
      ·
        refine ⟨18979058760527647762523333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12652705840351765175015555 18979058760527647762523333)
        ·
          refine ⟨3558573517598933955473125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18979058760527647762523333 3558573517598933955473125)
          ·
            refine ⟨667232534549800116651211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3558573517598933955473125 667232534549800116651211)
            ·
              refine ⟨1000848801824700174976817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 667232534549800116651211 1000848801824700174976817)
              ·
                refine ⟨750636601368525131232613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1000848801824700174976817 750636601368525131232613)
                ·
                  refine ⟨140744362756598462106115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 750636601368525131232613 140744362756598462106115)
                  ·
                    rfl

theorem cell20_308361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 2, 4].length) (baseStart_308361 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_308361 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_308361 prefixEnd_308361 := by exact prefixLift 308361
  have htrace : WordTrace (prefixWord ++ tailWord_308361) baseStart_308361 baseEnd_308361 := by
    simpa [prefixWord, tailWord_308361, baseEnd_308361] using wordTrace_append hprefix tailTrace_308361
  have hstable : (prefixWord ++ tailWord_308361).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308361).length < 2 ^ (prefixWord ++ tailWord_308361).sum := by decide
  have hdescent : baseEnd_308361 < baseStart_308361 := by decide
  rcases family_descends (prefixWord ++ tailWord_308361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308409 : List Nat := [1, 2, 1, 4, 1, 4, 3, 1, 3]
def baseStart_308409 : Nat := 118140960795 + 308409 * 2 ^ 59
def prefixEnd_308409 : Nat := 4983230072969 + 3 ^ 40 * 308409 * 2
def baseEnd_308409 : Nat := 140766271264523628505919

theorem tailTrace_308409 : CollatzResearch.WordTrace tailWord_308409 prefixEnd_308409 140766271264523628505919 := by
  unfold tailWord_308409
  simp only [CollatzResearch.WordTrace]
  refine ⟨11248600339694339908872281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7499066893129559939248187 11248600339694339908872281)
  ·
    refine ⟨8436450254770754931654211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11248600339694339908872281 8436450254770754931654211)
    ·
      refine ⟨12654675382156132397481317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8436450254770754931654211 12654675382156132397481317)
      ·
        refine ⟨2372751634154274824527747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12654675382156132397481317 2372751634154274824527747)
        ·
          refine ⟨3559127451231412236791621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2372751634154274824527747 3559127451231412236791621)
          ·
            refine ⟨667336397105889794398429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3559127451231412236791621 667336397105889794398429)
            ·
              refine ⟨250251148914708672899411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 667336397105889794398429 250251148914708672899411)
              ·
                refine ⟨375376723372063009349117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 250251148914708672899411 375376723372063009349117)
                ·
                  refine ⟨140766271264523628505919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 375376723372063009349117 140766271264523628505919)
                  ·
                    rfl

theorem cell20_308409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 3, 1, 3].length) (baseStart_308409 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_308409 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_308409 prefixEnd_308409 := by exact prefixLift 308409
  have htrace : WordTrace (prefixWord ++ tailWord_308409) baseStart_308409 baseEnd_308409 := by
    simpa [prefixWord, tailWord_308409, baseEnd_308409] using wordTrace_append hprefix tailTrace_308409
  have hstable : (prefixWord ++ tailWord_308409).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308409).length < 2 ^ (prefixWord ++ tailWord_308409).sum := by decide
  have hdescent : baseEnd_308409 < baseStart_308409 := by decide
  rcases family_descends (prefixWord ++ tailWord_308409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308461 : List Nat := [1, 5, 1, 2, 2, 2, 2, 5]
def baseStart_308461 : Nat := 118140960795 + 308461 * 2 ^ 59
def prefixEnd_308461 : Nat := 4983230072969 + 3 ^ 40 * 308461 * 2
def baseEnd_308461 : Nat := 46930001827147519590791

theorem tailTrace_308461 : CollatzResearch.WordTrace tailWord_308461 prefixEnd_308461 46930001827147519590791 := by
  unfold tailWord_308461
  simp only [CollatzResearch.WordTrace]
  refine ⟨11250496935505952789765237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7500331290337301859843491 11250496935505952789765237)
  ·
    refine ⟨1054734087703683074040491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11250496935505952789765237 1054734087703683074040491)
    ·
      refine ⟨1582101131555524611060737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1054734087703683074040491 1582101131555524611060737)
      ·
        refine ⟨1186575848666643458295553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1582101131555524611060737 1186575848666643458295553)
        ·
          refine ⟨889931886499982593721665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1186575848666643458295553 889931886499982593721665)
          ·
            refine ⟨667448914874986945291249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 889931886499982593721665 667448914874986945291249)
            ·
              refine ⟨500586686156240208968437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 667448914874986945291249 500586686156240208968437)
              ·
                refine ⟨46930001827147519590791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 500586686156240208968437 46930001827147519590791)
                ·
                  rfl

theorem cell20_308461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 2, 5].length) (baseStart_308461 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_308461 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_308461 prefixEnd_308461 := by exact prefixLift 308461
  have htrace : WordTrace (prefixWord ++ tailWord_308461) baseStart_308461 baseEnd_308461 := by
    simpa [prefixWord, tailWord_308461, baseEnd_308461] using wordTrace_append hprefix tailTrace_308461
  have hstable : (prefixWord ++ tailWord_308461).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308461).length < 2 ^ (prefixWord ++ tailWord_308461).sum := by decide
  have hdescent : baseEnd_308461 < baseStart_308461 := by decide
  rcases family_descends (prefixWord ++ tailWord_308461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308506 : List Nat := [3, 1, 1, 3, 3, 1, 1, 4, 3]
def baseStart_308506 : Nat := 118140960795 + 308506 * 2 ^ 59
def prefixEnd_308506 : Nat := 4983230072969 + 3 ^ 40 * 308506 * 2
def baseEnd_308506 : Nat := 140810544707622402272189

theorem tailTrace_308506 : CollatzResearch.WordTrace tailWord_308506 prefixEnd_308506 140810544707622402272189 := by
  unfold tailWord_308506
  simp only [CollatzResearch.WordTrace]
  refine ⟨2813034555085731368788343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7501425480228616983435581 2813034555085731368788343)
  ·
    refine ⟨4219551832628597053182515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2813034555085731368788343 4219551832628597053182515)
    ·
      refine ⟨6329327748942895579773773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4219551832628597053182515 6329327748942895579773773)
      ·
        refine ⟨2373497905853585842415165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6329327748942895579773773 2373497905853585842415165)
        ·
          refine ⟨890061714695094690905687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2373497905853585842415165 890061714695094690905687)
          ·
            refine ⟨1335092572042642036358531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 890061714695094690905687 1335092572042642036358531)
            ·
              refine ⟨2002638858063963054537797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1335092572042642036358531 2002638858063963054537797)
              ·
                refine ⟨375494785886993072725837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2002638858063963054537797 375494785886993072725837)
                ·
                  refine ⟨140810544707622402272189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 375494785886993072725837 140810544707622402272189)
                  ·
                    rfl

theorem cell20_308506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 4, 3].length) (baseStart_308506 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_308506 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_308506 prefixEnd_308506 := by exact prefixLift 308506
  have htrace : WordTrace (prefixWord ++ tailWord_308506) baseStart_308506 baseEnd_308506 := by
    simpa [prefixWord, tailWord_308506, baseEnd_308506] using wordTrace_append hprefix tailTrace_308506
  have hstable : (prefixWord ++ tailWord_308506).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308506).length < 2 ^ (prefixWord ++ tailWord_308506).sum := by decide
  have hdescent : baseEnd_308506 < baseStart_308506 := by decide
  rcases family_descends (prefixWord ++ tailWord_308506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308509 : List Nat := [1, 4, 2, 3, 1, 2, 1, 4, 2]
def baseStart_308509 : Nat := 118140960795 + 308509 * 2 ^ 59
def prefixEnd_308509 : Nat := 4983230072969 + 3 ^ 40 * 308509 * 2
def baseEnd_308509 : Nat := 140811913989367725172177

theorem tailTrace_308509 : CollatzResearch.WordTrace tailWord_308509 prefixEnd_308509 140811913989367725172177 := by
  unfold tailWord_308509
  simp only [CollatzResearch.WordTrace]
  refine ⟨11252247639332056987512581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7501498426221371325008387 11252247639332056987512581)
  ·
    refine ⟨2109796432374760685158609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11252247639332056987512581 2109796432374760685158609)
    ·
      refine ⟨1582347324281070513868957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2109796432374760685158609 1582347324281070513868957)
      ·
        refine ⟨593380246605401442700859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1582347324281070513868957 593380246605401442700859)
        ·
          refine ⟨890070369908102164051289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 593380246605401442700859 890070369908102164051289)
          ·
            refine ⟨667552777431076623038467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 890070369908102164051289 667552777431076623038467)
            ·
              refine ⟨1001329166146614934557701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 667552777431076623038467 1001329166146614934557701)
              ·
                refine ⟨187749218652490300229569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1001329166146614934557701 187749218652490300229569)
                ·
                  refine ⟨140811913989367725172177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 187749218652490300229569 140811913989367725172177)
                  ·
                    rfl

theorem cell20_308509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 4, 2].length) (baseStart_308509 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_308509 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_308509 prefixEnd_308509 := by exact prefixLift 308509
  have htrace : WordTrace (prefixWord ++ tailWord_308509) baseStart_308509 baseEnd_308509 := by
    simpa [prefixWord, tailWord_308509, baseEnd_308509] using wordTrace_append hprefix tailTrace_308509
  have hstable : (prefixWord ++ tailWord_308509).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308509).length < 2 ^ (prefixWord ++ tailWord_308509).sum := by decide
  have hdescent : baseEnd_308509 < baseStart_308509 := by decide
  rcases family_descends (prefixWord ++ tailWord_308509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308557 : List Nat := [1, 6, 1, 3, 1, 2, 1, 2, 3]
def baseStart_308557 : Nat := 118140960795 + 308557 * 2 ^ 59
def prefixEnd_308557 : Nat := 4983230072969 + 3 ^ 40 * 308557 * 2
def baseEnd_308557 : Nat := 140833822497292891571981

theorem tailTrace_308557 : CollatzResearch.WordTrace tailWord_308557 prefixEnd_308557 140833822497292891571981 := by
  unfold tailWord_308557
  simp only [CollatzResearch.WordTrace]
  refine ⟨11253998343158161185259925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7502665562105440790173283 11253998343158161185259925)
  ·
    refine ⟨527531172335538805559059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 11253998343158161185259925 527531172335538805559059)
    ·
      refine ⟨791296758503308208338589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 527531172335538805559059 791296758503308208338589)
      ·
        refine ⟨296736284438740578126971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 791296758503308208338589 296736284438740578126971)
        ·
          refine ⟨445104426658110867190457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 296736284438740578126971 445104426658110867190457)
          ·
            refine ⟨333828319993583150392843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 445104426658110867190457 333828319993583150392843)
            ·
              refine ⟨500742479990374725589265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 333828319993583150392843 500742479990374725589265)
              ·
                refine ⟨375556859992781044191949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 500742479990374725589265 375556859992781044191949)
                ·
                  refine ⟨140833822497292891571981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 375556859992781044191949 140833822497292891571981)
                  ·
                    rfl

theorem cell20_308557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_308557 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_308557 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_308557 prefixEnd_308557 := by exact prefixLift 308557
  have htrace : WordTrace (prefixWord ++ tailWord_308557) baseStart_308557 baseEnd_308557 := by
    simpa [prefixWord, tailWord_308557, baseEnd_308557] using wordTrace_append hprefix tailTrace_308557
  have hstable : (prefixWord ++ tailWord_308557).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308557).length < 2 ^ (prefixWord ++ tailWord_308557).sum := by decide
  have hdescent : baseEnd_308557 < baseStart_308557 := by decide
  rcases family_descends (prefixWord ++ tailWord_308557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308589 : List Nat := [1, 5, 1, 1, 1, 3, 2, 2, 4]
def baseStart_308589 : Nat := 118140960795 + 308589 * 2 ^ 59
def prefixEnd_308589 : Nat := 4983230072969 + 3 ^ 40 * 308589 * 2
def baseEnd_308589 : Nat := 140848428169243002505183

theorem tailTrace_308589 : CollatzResearch.WordTrace tailWord_308589 prefixEnd_308589 140848428169243002505183 := by
  unfold tailWord_308589
  simp only [CollatzResearch.WordTrace]
  refine ⟨11255165479042230650424821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7503443652694820433616547 11255165479042230650424821)
  ·
    refine ⟨1055171763660209123477327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11255165479042230650424821 1055171763660209123477327)
    ·
      refine ⟨1582757645490313685215991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1055171763660209123477327 1582757645490313685215991)
      ·
        refine ⟨2374136468235470527823987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1582757645490313685215991 2374136468235470527823987)
        ·
          refine ⟨3561204702353205791735981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2374136468235470527823987 3561204702353205791735981)
          ·
            refine ⟨1335451763382452171900993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3561204702353205791735981 1335451763382452171900993)
            ·
              refine ⟨1001588822536839128925745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1335451763382452171900993 1001588822536839128925745)
              ·
                refine ⟨751191616902629346694309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1001588822536839128925745 751191616902629346694309)
                ·
                  refine ⟨140848428169243002505183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 751191616902629346694309 140848428169243002505183)
                  ·
                    rfl

theorem cell20_308589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_308589 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_308589 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_308589 prefixEnd_308589 := by exact prefixLift 308589
  have htrace : WordTrace (prefixWord ++ tailWord_308589) baseStart_308589 baseEnd_308589 := by
    simpa [prefixWord, tailWord_308589, baseEnd_308589] using wordTrace_append hprefix tailTrace_308589
  have hstable : (prefixWord ++ tailWord_308589).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308589).length < 2 ^ (prefixWord ++ tailWord_308589).sum := by decide
  have hdescent : baseEnd_308589 < baseStart_308589 := by decide
  rcases family_descends (prefixWord ++ tailWord_308589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308634 : List Nat := [3, 1, 1, 4, 1, 1, 4, 5]
def baseStart_308634 : Nat := 118140960795 + 308634 * 2 ^ 59
def prefixEnd_308634 : Nat := 4983230072969 + 3 ^ 40 * 308634 * 2
def baseEnd_308634 : Nat := 46956322465140948668333

theorem tailTrace_308634 : CollatzResearch.WordTrace tailWord_308634 prefixEnd_308634 46956322465140948668333 := by
  unfold tailWord_308634
  simp only [CollatzResearch.WordTrace]
  refine ⟨2814201690969800833953239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7504537842586135557208637 2814201690969800833953239)
  ·
    refine ⟨4221302536454701250929859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2814201690969800833953239 4221302536454701250929859)
    ·
      refine ⟨6331953804682051876394789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4221302536454701250929859 6331953804682051876394789)
      ·
        refine ⟨1187241338377884726824023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6331953804682051876394789 1187241338377884726824023)
        ·
          refine ⟨1780862007566827090236035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1187241338377884726824023 1780862007566827090236035)
          ·
            refine ⟨2671293011350240635354053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1780862007566827090236035 2671293011350240635354053)
            ·
              refine ⟨500867439628170119128885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2671293011350240635354053 500867439628170119128885)
              ·
                refine ⟨46956322465140948668333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 500867439628170119128885 46956322465140948668333)
                ·
                  rfl

theorem cell20_308634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 4, 5].length) (baseStart_308634 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_308634 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_308634 prefixEnd_308634 := by exact prefixLift 308634
  have htrace : WordTrace (prefixWord ++ tailWord_308634) baseStart_308634 baseEnd_308634 := by
    simpa [prefixWord, tailWord_308634, baseEnd_308634] using wordTrace_append hprefix tailTrace_308634
  have hstable : (prefixWord ++ tailWord_308634).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308634).length < 2 ^ (prefixWord ++ tailWord_308634).sum := by decide
  have hdescent : baseEnd_308634 < baseStart_308634 := by decide
  rcases family_descends (prefixWord ++ tailWord_308634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308637 : List Nat := [1, 4, 2, 1, 3, 1, 4, 1, 3]
def baseStart_308637 : Nat := 118140960795 + 308637 * 2 ^ 59
def prefixEnd_308637 : Nat := 4983230072969 + 3 ^ 40 * 308637 * 2
def baseEnd_308637 : Nat := 140870336677168168904987

theorem tailTrace_308637 : CollatzResearch.WordTrace tailWord_308637 prefixEnd_308637 140870336677168168904987 := by
  unfold tailWord_308637
  simp only [CollatzResearch.WordTrace]
  refine ⟨11256916182868334848172165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7504610788578889898781443 11256916182868334848172165)
  ·
    refine ⟨2110671784287812784032281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11256916182868334848172165 2110671784287812784032281)
    ·
      refine ⟨1583003838215859588024211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2110671784287812784032281 1583003838215859588024211)
      ·
        refine ⟨2374505757323789382036317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1583003838215859588024211 2374505757323789382036317)
        ·
          refine ⟨890439658996421018263619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2374505757323789382036317 890439658996421018263619)
          ·
            refine ⟨1335659488494631527395429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 890439658996421018263619 1335659488494631527395429)
            ·
              refine ⟨250436154092743411386643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1335659488494631527395429 250436154092743411386643)
              ·
                refine ⟨375654231139115117079965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 250436154092743411386643 375654231139115117079965)
                ·
                  refine ⟨140870336677168168904987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 375654231139115117079965 140870336677168168904987)
                  ·
                    rfl

theorem cell20_308637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 4, 1, 3].length) (baseStart_308637 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_308637 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_308637 prefixEnd_308637 := by exact prefixLift 308637
  have htrace : WordTrace (prefixWord ++ tailWord_308637) baseStart_308637 baseEnd_308637 := by
    simpa [prefixWord, tailWord_308637, baseEnd_308637] using wordTrace_append hprefix tailTrace_308637
  have hstable : (prefixWord ++ tailWord_308637).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308637).length < 2 ^ (prefixWord ++ tailWord_308637).sum := by decide
  have hdescent : baseEnd_308637 < baseStart_308637 := by decide
  rcases family_descends (prefixWord ++ tailWord_308637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308674 : List Nat := [3, 5, 2, 1, 1, 1, 1, 4, 2]
def baseStart_308674 : Nat := 118140960795 + 308674 * 2 ^ 59
def prefixEnd_308674 : Nat := 4983230072969 + 3 ^ 40 * 308674 * 2
def baseEnd_308674 : Nat := 140887224485360484671503

theorem tailTrace_308674 : CollatzResearch.WordTrace tailWord_308674 prefixEnd_308674 140887224485360484671503 := by
  unfold tailWord_308674
  simp only [CollatzResearch.WordTrace]
  refine ⟨2814566420933572541817269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7505510455822860111512717 2814566420933572541817269)
  ·
    refine ⟨263865601962522425795369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2814566420933572541817269 263865601962522425795369)
    ·
      refine ⟨197899201471891819346527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 263865601962522425795369 197899201471891819346527)
      ·
        refine ⟨296848802207837729019791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197899201471891819346527 296848802207837729019791)
        ·
          refine ⟨445273203311756593529687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 296848802207837729019791 445273203311756593529687)
          ·
            refine ⟨667909804967634890294531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 445273203311756593529687 667909804967634890294531)
            ·
              refine ⟨1001864707451452335441797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 667909804967634890294531 1001864707451452335441797)
              ·
                refine ⟨187849632647147312895337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1001864707451452335441797 187849632647147312895337)
                ·
                  refine ⟨140887224485360484671503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 187849632647147312895337 140887224485360484671503)
                  ·
                    rfl

theorem cell20_308674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_308674 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_308674 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_308674 prefixEnd_308674 := by exact prefixLift 308674
  have htrace : WordTrace (prefixWord ++ tailWord_308674) baseStart_308674 baseEnd_308674 := by
    simpa [prefixWord, tailWord_308674, baseEnd_308674] using wordTrace_append hprefix tailTrace_308674
  have hstable : (prefixWord ++ tailWord_308674).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308674).length < 2 ^ (prefixWord ++ tailWord_308674).sum := by decide
  have hdescent : baseEnd_308674 < baseStart_308674 := by decide
  rcases family_descends (prefixWord ++ tailWord_308674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308682 : List Nat := [3, 1, 2, 1, 2, 4, 1, 4, 2]
def baseStart_308682 : Nat := 118140960795 + 308682 * 2 ^ 59
def prefixEnd_308682 : Nat := 4983230072969 + 3 ^ 40 * 308682 * 2
def baseEnd_308682 : Nat := 140890875903348012404803

theorem tailTrace_308682 : CollatzResearch.WordTrace tailWord_308682 prefixEnd_308682 140890875903348012404803 := by
  unfold tailWord_308682
  simp only [CollatzResearch.WordTrace]
  refine ⟨2814639366926326883390075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7505704978470205022373533 2814639366926326883390075)
  ·
    refine ⟨4221959050389490325085113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2814639366926326883390075 4221959050389490325085113)
    ·
      refine ⟨3166469287792117743813835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4221959050389490325085113 3166469287792117743813835)
      ·
        refine ⟨4749703931688176615720753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3166469287792117743813835 4749703931688176615720753)
        ·
          refine ⟨3562277948766132461790565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4749703931688176615720753 3562277948766132461790565)
          ·
            refine ⟨667927115393649836585731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3562277948766132461790565 667927115393649836585731)
            ·
              refine ⟨1001890673090474754878597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 667927115393649836585731 1001890673090474754878597)
              ·
                refine ⟨187854501204464016539737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1001890673090474754878597 187854501204464016539737)
                ·
                  refine ⟨140890875903348012404803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 187854501204464016539737 140890875903348012404803)
                  ·
                    rfl

theorem cell20_308682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 4, 2].length) (baseStart_308682 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_308682 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_308682 prefixEnd_308682 := by exact prefixLift 308682
  have htrace : WordTrace (prefixWord ++ tailWord_308682) baseStart_308682 baseEnd_308682 := by
    simpa [prefixWord, tailWord_308682, baseEnd_308682] using wordTrace_append hprefix tailTrace_308682
  have hstable : (prefixWord ++ tailWord_308682).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308682).length < 2 ^ (prefixWord ++ tailWord_308682).sum := by decide
  have hdescent : baseEnd_308682 < baseStart_308682 := by decide
  rcases family_descends (prefixWord ++ tailWord_308682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308720 : List Nat := [2, 1, 1, 1, 3, 5, 2, 3, 2]
def baseStart_308720 : Nat := 118140960795 + 308720 * 2 ^ 59
def prefixEnd_308720 : Nat := 4983230072969 + 3 ^ 40 * 308720 * 2
def baseEnd_308720 : Nat := 140908220138788769137981

theorem tailTrace_308720 : CollatzResearch.WordTrace tailWord_308720 prefixEnd_308720 140908220138788769137981 := by
  unfold tailWord_308720
  simp only [CollatzResearch.WordTrace]
  refine ⟨5629971720783820011721807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7506628961045093348962409 5629971720783820011721807)
  ·
    refine ⟨8444957581175730017582711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5629971720783820011721807 8444957581175730017582711)
    ·
      refine ⟨12667436371763595026374067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8444957581175730017582711 12667436371763595026374067)
      ·
        refine ⟨19001154557645392539561101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12667436371763595026374067 19001154557645392539561101)
        ·
          refine ⟨7125432959117022202335413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19001154557645392539561101 7125432959117022202335413)
          ·
            refine ⟨668009339917220831468945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7125432959117022202335413 668009339917220831468945)
            ·
              refine ⟨501007004937915623601709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 668009339917220831468945 501007004937915623601709)
              ·
                refine ⟨187877626851718358850641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 501007004937915623601709 187877626851718358850641)
                ·
                  refine ⟨140908220138788769137981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 187877626851718358850641 140908220138788769137981)
                  ·
                    rfl

theorem cell20_308720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 2, 3, 2].length) (baseStart_308720 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_308720 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_308720 prefixEnd_308720 := by exact prefixLift 308720
  have htrace : WordTrace (prefixWord ++ tailWord_308720) baseStart_308720 baseEnd_308720 := by
    simpa [prefixWord, tailWord_308720, baseEnd_308720] using wordTrace_append hprefix tailTrace_308720
  have hstable : (prefixWord ++ tailWord_308720).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308720).length < 2 ^ (prefixWord ++ tailWord_308720).sum := by decide
  have hdescent : baseEnd_308720 < baseStart_308720 := by decide
  rcases family_descends (prefixWord ++ tailWord_308720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308793 : List Nat := [1, 2, 1, 5, 1, 2, 2, 1, 5]
def baseStart_308793 : Nat := 118140960795 + 308793 * 2 ^ 59
def prefixEnd_308793 : Nat := 4983230072969 + 3 ^ 40 * 308793 * 2
def baseEnd_308793 : Nat := 140941539327924959704349

theorem tailTrace_308793 : CollatzResearch.WordTrace tailWord_308793 prefixEnd_308793 140941539327924959704349 := by
  unfold tailWord_308793
  simp only [CollatzResearch.WordTrace]
  refine ⟨11262605970303173490851033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7508403980202115660567355 11262605970303173490851033)
  ·
    refine ⟨8446954477727380118138275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11262605970303173490851033 8446954477727380118138275)
    ·
      refine ⟨12670431716591070177207413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8446954477727380118138275 12670431716591070177207413)
      ·
        refine ⟨1187852973430412829113195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12670431716591070177207413 1187852973430412829113195)
        ·
          refine ⟨1781779460145619243669793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1187852973430412829113195 1781779460145619243669793)
          ·
            refine ⟨1336334595109214432752345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1781779460145619243669793 1336334595109214432752345)
            ·
              refine ⟨1002250946331910824564259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1336334595109214432752345 1002250946331910824564259)
              ·
                refine ⟨1503376419497866236846389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1002250946331910824564259 1503376419497866236846389)
                ·
                  refine ⟨140941539327924959704349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1503376419497866236846389 140941539327924959704349)
                  ·
                    rfl

theorem cell20_308793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 1, 5].length) (baseStart_308793 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_308793 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_308793 prefixEnd_308793 := by exact prefixLift 308793
  have htrace : WordTrace (prefixWord ++ tailWord_308793) baseStart_308793 baseEnd_308793 := by
    simpa [prefixWord, tailWord_308793, baseEnd_308793] using wordTrace_append hprefix tailTrace_308793
  have hstable : (prefixWord ++ tailWord_308793).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308793).length < 2 ^ (prefixWord ++ tailWord_308793).sum := by decide
  have hdescent : baseEnd_308793 < baseStart_308793 := by decide
  rcases family_descends (prefixWord ++ tailWord_308793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308796 : List Nat := [2, 2, 2, 2, 4, 2, 1, 1, 4]
def baseStart_308796 : Nat := 118140960795 + 308796 * 2 ^ 59
def prefixEnd_308796 : Nat := 4983230072969 + 3 ^ 40 * 308796 * 2
def baseEnd_308796 : Nat := 140942908609670282604337

theorem tailTrace_308796 : CollatzResearch.WordTrace tailWord_308796 prefixEnd_308796 140942908609670282604337 := by
  unfold tailWord_308796
  simp only [CollatzResearch.WordTrace]
  refine ⟨5631357694646152501605121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7508476926194870002140161 5631357694646152501605121)
  ·
    refine ⟨4223518270984614376203841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5631357694646152501605121 4223518270984614376203841)
    ·
      refine ⟨3167638703238460782152881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4223518270984614376203841 3167638703238460782152881)
      ·
        refine ⟨2375729027428845586614661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3167638703238460782152881 2375729027428845586614661)
        ·
          refine ⟨445449192642908547490249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2375729027428845586614661 445449192642908547490249)
          ·
            refine ⟨334086894482181410617687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 445449192642908547490249 334086894482181410617687)
            ·
              refine ⟨501130341723272115926531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 334086894482181410617687 501130341723272115926531)
              ·
                refine ⟨751695512584908173889797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 501130341723272115926531 751695512584908173889797)
                ·
                  refine ⟨140942908609670282604337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 751695512584908173889797 140942908609670282604337)
                  ·
                    rfl

theorem cell20_308796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 1, 1, 4].length) (baseStart_308796 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_308796 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_308796 prefixEnd_308796 := by exact prefixLift 308796
  have htrace : WordTrace (prefixWord ++ tailWord_308796) baseStart_308796 baseEnd_308796 := by
    simpa [prefixWord, tailWord_308796, baseEnd_308796] using wordTrace_append hprefix tailTrace_308796
  have hstable : (prefixWord ++ tailWord_308796).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308796).length < 2 ^ (prefixWord ++ tailWord_308796).sum := by decide
  have hdescent : baseEnd_308796 < baseStart_308796 := by decide
  rcases family_descends (prefixWord ++ tailWord_308796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308806 : List Nat := [6, 1, 1, 1, 3, 1, 1, 3, 3]
def baseStart_308806 : Nat := 118140960795 + 308806 * 2 ^ 59
def prefixEnd_308806 : Nat := 4983230072969 + 3 ^ 40 * 308806 * 2
def baseEnd_308806 : Nat := 140947472882154692270963

theorem tailTrace_308806 : CollatzResearch.WordTrace tailWord_308806 prefixEnd_308806 140947472882154692270963 := by
  unfold tailWord_308806
  simp only [CollatzResearch.WordTrace]
  refine ⟨351971253726752397221071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 7508720079504051140716181 351971253726752397221071)
  ·
    refine ⟨527956880590128595831607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 351971253726752397221071 527956880590128595831607)
    ·
      refine ⟨791935320885192893747411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 527956880590128595831607 791935320885192893747411)
      ·
        refine ⟨1187902981327789340621117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 791935320885192893747411 1187902981327789340621117)
        ·
          refine ⟨445463617997921002732919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1187902981327789340621117 445463617997921002732919)
          ·
            refine ⟨668195426996881504099379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 445463617997921002732919 668195426996881504099379)
            ·
              refine ⟨1002293140495322256149069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 668195426996881504099379 1002293140495322256149069)
              ·
                refine ⟨375859927685745846055901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1002293140495322256149069 375859927685745846055901)
                ·
                  refine ⟨140947472882154692270963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 375859927685745846055901 140947472882154692270963)
                  ·
                    rfl

theorem cell20_308806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_308806 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_308806 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_308806 prefixEnd_308806 := by exact prefixLift 308806
  have htrace : WordTrace (prefixWord ++ tailWord_308806) baseStart_308806 baseEnd_308806 := by
    simpa [prefixWord, tailWord_308806, baseEnd_308806] using wordTrace_append hprefix tailTrace_308806
  have hstable : (prefixWord ++ tailWord_308806).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308806).length < 2 ^ (prefixWord ++ tailWord_308806).sum := by decide
  have hdescent : baseEnd_308806 < baseStart_308806 := by decide
  rcases family_descends (prefixWord ++ tailWord_308806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308845 : List Nat := [1, 5, 1, 1, 12]
def baseStart_308845 : Nat := 118140960795 + 308845 * 2 ^ 59
def prefixEnd_308845 : Nat := 4983230072969 + 3 ^ 40 * 308845 * 2
def baseEnd_308845 : Nat := 1740312019072146789763

theorem tailTrace_308845 : CollatzResearch.WordTrace tailWord_308845 prefixEnd_308845 1740312019072146789763 := by
  unfold tailWord_308845
  simp only [CollatzResearch.WordTrace]
  refine ⟨11264502566114786371743989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7509668377409857581162659 11264502566114786371743989)
  ·
    refine ⟨1056047115573261222350999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11264502566114786371743989 1056047115573261222350999)
    ·
      refine ⟨1584070673359891833526499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1056047115573261222350999 1584070673359891833526499)
      ·
        refine ⟨2376106010039837750289749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1584070673359891833526499 2376106010039837750289749)
        ·
          refine ⟨1740312019072146789763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 2376106010039837750289749 1740312019072146789763)
          ·
            rfl

theorem cell20_308845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 12].length) (baseStart_308845 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_308845 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_308845 prefixEnd_308845 := by exact prefixLift 308845
  have htrace : WordTrace (prefixWord ++ tailWord_308845) baseStart_308845 baseEnd_308845 := by
    simpa [prefixWord, tailWord_308845, baseEnd_308845] using wordTrace_append hprefix tailTrace_308845
  have hstable : (prefixWord ++ tailWord_308845).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308845).length < 2 ^ (prefixWord ++ tailWord_308845).sum := by decide
  have hdescent : baseEnd_308845 < baseStart_308845 := by decide
  rcases family_descends (prefixWord ++ tailWord_308845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308848 : List Nat := [2, 1, 1, 1, 6, 2, 2, 2, 3]
def baseStart_308848 : Nat := 118140960795 + 308848 * 2 ^ 59
def prefixEnd_308848 : Nat := 4983230072969 + 3 ^ 40 * 308848 * 2
def baseEnd_308848 : Nat := 140966642826589212870791

theorem tailTrace_308848 : CollatzResearch.WordTrace tailWord_308848 prefixEnd_308848 140966642826589212870791 := by
  unfold tailWord_308848
  simp only [CollatzResearch.WordTrace]
  refine ⟨5632305992551958942051599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7509741323402611922735465 5632305992551958942051599)
  ·
    refine ⟨8448458988827938413077399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5632305992551958942051599 8448458988827938413077399)
    ·
      refine ⟨12672688483241907619616099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8448458988827938413077399 12672688483241907619616099)
      ·
        refine ⟨19009032724862861429424149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12672688483241907619616099 19009032724862861429424149)
        ·
          refine ⟨891048408977946629504257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 19009032724862861429424149 891048408977946629504257)
          ·
            refine ⟨668286306733459972128193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 891048408977946629504257 668286306733459972128193)
            ·
              refine ⟨501214730050094979096145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 668286306733459972128193 501214730050094979096145)
              ·
                refine ⟨375911047537571234322109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 501214730050094979096145 375911047537571234322109)
                ·
                  refine ⟨140966642826589212870791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 375911047537571234322109 140966642826589212870791)
                  ·
                    rfl

theorem cell20_308848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 2, 2, 3].length) (baseStart_308848 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_308848 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_308848 prefixEnd_308848 := by exact prefixLift 308848
  have htrace : WordTrace (prefixWord ++ tailWord_308848) baseStart_308848 baseEnd_308848 := by
    simpa [prefixWord, tailWord_308848, baseEnd_308848] using wordTrace_append hprefix tailTrace_308848
  have hstable : (prefixWord ++ tailWord_308848).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308848).length < 2 ^ (prefixWord ++ tailWord_308848).sum := by decide
  have hdescent : baseEnd_308848 < baseStart_308848 := by decide
  rcases family_descends (prefixWord ++ tailWord_308848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308869 : List Nat := [1, 3, 1, 1, 4, 1, 1, 5, 3]
def baseStart_308869 : Nat := 118140960795 + 308869 * 2 ^ 59
def prefixEnd_308869 : Nat := 4983230072969 + 3 ^ 40 * 308869 * 2
def baseEnd_308869 : Nat := 140976227798806473170705

theorem tailTrace_308869 : CollatzResearch.WordTrace tailWord_308869 prefixEnd_308869 140976227798806473170705 := by
  unfold tailWord_308869
  simp only [CollatzResearch.WordTrace]
  refine ⟨11265377918027838470617661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7510251945351892313745107 11265377918027838470617661)
  ·
    refine ⟨4224516719260439426481623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11265377918027838470617661 4224516719260439426481623)
    ·
      refine ⟨6336775078890659139722435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4224516719260439426481623 6336775078890659139722435)
      ·
        refine ⟨9505162618335988709583653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6336775078890659139722435 9505162618335988709583653)
        ·
          refine ⟨1782217990937997883046935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9505162618335988709583653 1782217990937997883046935)
          ·
            refine ⟨2673326986406996824570403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1782217990937997883046935 2673326986406996824570403)
            ·
              refine ⟨4009990479610495236855605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2673326986406996824570403 4009990479610495236855605)
              ·
                refine ⟨375936607463483928455213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4009990479610495236855605 375936607463483928455213)
                ·
                  refine ⟨140976227798806473170705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 375936607463483928455213 140976227798806473170705)
                  ·
                    rfl

theorem cell20_308869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 5, 3].length) (baseStart_308869 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_308869 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_308869 prefixEnd_308869 := by exact prefixLift 308869
  have htrace : WordTrace (prefixWord ++ tailWord_308869) baseStart_308869 baseEnd_308869 := by
    simpa [prefixWord, tailWord_308869, baseEnd_308869] using wordTrace_append hprefix tailTrace_308869
  have hstable : (prefixWord ++ tailWord_308869).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308869).length < 2 ^ (prefixWord ++ tailWord_308869).sum := by decide
  have hdescent : baseEnd_308869 < baseStart_308869 := by decide
  rcases family_descends (prefixWord ++ tailWord_308869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308872 : List Nat := [2, 1, 3, 5, 1, 1, 1, 2, 4]
def baseStart_308872 : Nat := 118140960795 + 308872 * 2 ^ 59
def prefixEnd_308872 : Nat := 4983230072969 + 3 ^ 40 * 308872 * 2
def baseEnd_308872 : Nat := 140977597080551796070693

theorem tailTrace_308872 : CollatzResearch.WordTrace tailWord_308872 prefixEnd_308872 140977597080551796070693 := by
  unfold tailWord_308872
  simp only [CollatzResearch.WordTrace]
  refine ⟨5632743668508484991488435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7510324891344646655317913 5632743668508484991488435)
  ·
    refine ⟨8449115502762727487232653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5632743668508484991488435 8449115502762727487232653)
    ·
      refine ⟨3168418313536022807712245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8449115502762727487232653 3168418313536022807712245)
      ·
        refine ⟨297039216894002138223023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3168418313536022807712245 297039216894002138223023)
        ·
          refine ⟨445558825341003207334535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 297039216894002138223023 445558825341003207334535)
          ·
            refine ⟨668338238011504811001803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 445558825341003207334535 668338238011504811001803)
            ·
              refine ⟨1002507357017257216502705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 668338238011504811001803 1002507357017257216502705)
              ·
                refine ⟨751880517762942912377029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1002507357017257216502705 751880517762942912377029)
                ·
                  refine ⟨140977597080551796070693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 751880517762942912377029 140977597080551796070693)
                  ·
                    rfl

theorem cell20_308872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 2, 4].length) (baseStart_308872 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_308872 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_308872 prefixEnd_308872 := by exact prefixLift 308872
  have htrace : WordTrace (prefixWord ++ tailWord_308872) baseStart_308872 baseEnd_308872 := by
    simpa [prefixWord, tailWord_308872, baseEnd_308872] using wordTrace_append hprefix tailTrace_308872
  have hstable : (prefixWord ++ tailWord_308872).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308872).length < 2 ^ (prefixWord ++ tailWord_308872).sum := by decide
  have hdescent : baseEnd_308872 < baseStart_308872 := by decide
  rcases family_descends (prefixWord ++ tailWord_308872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308876 : List Nat := [2, 2, 1, 2, 1, 1, 5, 2, 4]
def baseStart_308876 : Nat := 118140960795 + 308876 * 2 ^ 59
def prefixEnd_308876 : Nat := 4983230072969 + 3 ^ 40 * 308876 * 2
def baseEnd_308876 : Nat := 140979422789545559937343

theorem tailTrace_308876 : CollatzResearch.WordTrace tailWord_308876 prefixEnd_308876 140979422789545559937343 := by
  unfold tailWord_308876
  simp only [CollatzResearch.WordTrace]
  refine ⟨5632816614501239333061241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7510422152668319110748321 5632816614501239333061241)
  ·
    refine ⟨4224612460875929499795931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5632816614501239333061241 4224612460875929499795931)
    ·
      refine ⟨6336918691313894249693897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4224612460875929499795931 6336918691313894249693897)
      ·
        refine ⟨4752689018485420687270423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6336918691313894249693897 4752689018485420687270423)
        ·
          refine ⟨7129033527728131030905635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4752689018485420687270423 7129033527728131030905635)
          ·
            refine ⟨10693550291592196546358453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7129033527728131030905635 10693550291592196546358453)
            ·
              refine ⟨1002520339836768426221105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10693550291592196546358453 1002520339836768426221105)
              ·
                refine ⟨751890254877576319665829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1002520339836768426221105 751890254877576319665829)
                ·
                  refine ⟨140979422789545559937343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 751890254877576319665829 140979422789545559937343)
                  ·
                    rfl

theorem cell20_308876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 2, 4].length) (baseStart_308876 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_308876 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_308876 prefixEnd_308876 := by exact prefixLift 308876
  have htrace : WordTrace (prefixWord ++ tailWord_308876) baseStart_308876 baseEnd_308876 := by
    simpa [prefixWord, tailWord_308876, baseEnd_308876] using wordTrace_append hprefix tailTrace_308876
  have hstable : (prefixWord ++ tailWord_308876).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308876).length < 2 ^ (prefixWord ++ tailWord_308876).sum := by decide
  have hdescent : baseEnd_308876 < baseStart_308876 := by decide
  rcases family_descends (prefixWord ++ tailWord_308876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308914 : List Nat := [3, 2, 1, 1, 1, 2, 3, 3, 4]
def baseStart_308914 : Nat := 118140960795 + 308914 * 2 ^ 59
def prefixEnd_308914 : Nat := 4983230072969 + 3 ^ 40 * 308914 * 2
def baseEnd_308914 : Nat := 140996767024986316670521

theorem tailTrace_308914 : CollatzResearch.WordTrace tailWord_308914 prefixEnd_308914 140996767024986316670521 := by
  unfold tailWord_308914
  simp only [CollatzResearch.WordTrace]
  refine ⟨2816754800716202789001449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7511346135243207437337197 2816754800716202789001449)
  ·
    refine ⟨2112566100537152091751087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2816754800716202789001449 2112566100537152091751087)
    ·
      refine ⟨3168849150805728137626631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2112566100537152091751087 3168849150805728137626631)
      ·
        refine ⟨4753273726208592206439947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3168849150805728137626631 4753273726208592206439947)
        ·
          refine ⟨7129910589312888309659921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4753273726208592206439947 7129910589312888309659921)
          ·
            refine ⟨5347432941984666232244941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7129910589312888309659921 5347432941984666232244941)
            ·
              refine ⟨2005287353244249837091853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5347432941984666232244941 2005287353244249837091853)
              ·
                refine ⟨751982757466593688909445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2005287353244249837091853 751982757466593688909445)
                ·
                  refine ⟨140996767024986316670521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 751982757466593688909445 140996767024986316670521)
                  ·
                    rfl

theorem cell20_308914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 3, 4].length) (baseStart_308914 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_308914 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_308914 prefixEnd_308914 := by exact prefixLift 308914
  have htrace : WordTrace (prefixWord ++ tailWord_308914) baseStart_308914 baseEnd_308914 := by
    simpa [prefixWord, tailWord_308914, baseEnd_308914] using wordTrace_append hprefix tailTrace_308914
  have hstable : (prefixWord ++ tailWord_308914).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308914).length < 2 ^ (prefixWord ++ tailWord_308914).sum := by decide
  have hdescent : baseEnd_308914 < baseStart_308914 := by decide
  rcases family_descends (prefixWord ++ tailWord_308914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308930 : List Nat := [3, 5, 1, 2, 1, 2, 2, 4]
def baseStart_308930 : Nat := 118140960795 + 308930 * 2 ^ 59
def prefixEnd_308930 : Nat := 4983230072969 + 3 ^ 40 * 308930 * 2
def baseEnd_308930 : Nat := 47001356620320457379041

theorem tailTrace_308930 : CollatzResearch.WordTrace tailWord_308930 prefixEnd_308930 47001356620320457379041 := by
  unfold tailWord_308930
  simp only [CollatzResearch.WordTrace]
  refine ⟨2816900692701711472147061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7511735180537897259058829 2816900692701711472147061)
  ·
    refine ⟨264084439940785450513787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2816900692701711472147061 264084439940785450513787)
    ·
      refine ⟨396126659911178175770681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 264084439940785450513787 396126659911178175770681)
      ·
        refine ⟨297094994933383631828011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 396126659911178175770681 297094994933383631828011)
        ·
          refine ⟨445642492400075447742017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 297094994933383631828011 445642492400075447742017)
          ·
            refine ⟨334231869300056585806513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 445642492400075447742017 334231869300056585806513)
            ·
              refine ⟨250673901975042439354885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 334231869300056585806513 250673901975042439354885)
              ·
                refine ⟨47001356620320457379041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 250673901975042439354885 47001356620320457379041)
                ·
                  rfl

theorem cell20_308930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 2, 4].length) (baseStart_308930 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_308930 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_308930 prefixEnd_308930 := by exact prefixLift 308930
  have htrace : WordTrace (prefixWord ++ tailWord_308930) baseStart_308930 baseEnd_308930 := by
    simpa [prefixWord, tailWord_308930, baseEnd_308930] using wordTrace_append hprefix tailTrace_308930
  have hstable : (prefixWord ++ tailWord_308930).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308930).length < 2 ^ (prefixWord ++ tailWord_308930).sum := by decide
  have hdescent : baseEnd_308930 < baseStart_308930 := by decide
  rcases family_descends (prefixWord ++ tailWord_308930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308934 : List Nat := [6, 1, 2, 1, 1, 2, 1, 6]
def baseStart_308934 : Nat := 118140960795 + 308934 * 2 ^ 59
def prefixEnd_308934 : Nat := 4983230072969 + 3 ^ 40 * 308934 * 2
def baseEnd_308934 : Nat := 47001965189985045334591

theorem tailTrace_308934 : CollatzResearch.WordTrace tailWord_308934 prefixEnd_308934 47001965189985045334591 := by
  unfold tailWord_308934
  simp only [CollatzResearch.WordTrace]
  refine ⟨352117145712261080366683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 7511832441861569714489237 352117145712261080366683)
  ·
    refine ⟨528175718568391620550025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 352117145712261080366683 528175718568391620550025)
    ·
      refine ⟨396131788926293715412519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 528175718568391620550025 396131788926293715412519)
      ·
        refine ⟨594197683389440573118779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 396131788926293715412519 594197683389440573118779)
        ·
          refine ⟨891296525084160859678169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 594197683389440573118779 891296525084160859678169)
          ·
            refine ⟨668472393813120644758627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 891296525084160859678169 668472393813120644758627)
            ·
              refine ⟨1002708590719680967137941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 668472393813120644758627 1002708590719680967137941)
              ·
                refine ⟨47001965189985045334591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1002708590719680967137941 47001965189985045334591)
                ·
                  rfl

theorem cell20_308934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_308934 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_308934 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_308934 prefixEnd_308934 := by exact prefixLift 308934
  have htrace : WordTrace (prefixWord ++ tailWord_308934) baseStart_308934 baseEnd_308934 := by
    simpa [prefixWord, tailWord_308934, baseEnd_308934] using wordTrace_append hprefix tailTrace_308934
  have hstable : (prefixWord ++ tailWord_308934).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308934).length < 2 ^ (prefixWord ++ tailWord_308934).sum := by decide
  have hdescent : baseEnd_308934 < baseStart_308934 := by decide
  rcases family_descends (prefixWord ++ tailWord_308934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_308938 : List Nat := [3, 1, 2, 1, 5, 1, 1, 6]
def baseStart_308938 : Nat := 118140960795 + 308938 * 2 ^ 59
def prefixEnd_308938 : Nat := 4983230072969 + 3 ^ 40 * 308938 * 2
def baseEnd_308938 : Nat := 47002573759649633290141

theorem tailTrace_308938 : CollatzResearch.WordTrace tailWord_308938 prefixEnd_308938 47002573759649633290141 := by
  unfold tailWord_308938
  simp only [CollatzResearch.WordTrace]
  refine ⟨2816973638694465813719867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7511929703185242169919645 2816973638694465813719867)
  ·
    refine ⟨4225460458041698720579801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2816973638694465813719867 4225460458041698720579801)
    ·
      refine ⟨3169095343531274040434851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4225460458041698720579801 3169095343531274040434851)
      ·
        refine ⟨4753643015296911060652277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3169095343531274040434851 4753643015296911060652277)
        ·
          refine ⟨445654032684085411936151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4753643015296911060652277 445654032684085411936151)
          ·
            refine ⟨668481049026128117904227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 445654032684085411936151 668481049026128117904227)
            ·
              refine ⟨1002721573539192176856341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 668481049026128117904227 1002721573539192176856341)
              ·
                refine ⟨47002573759649633290141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1002721573539192176856341 47002573759649633290141)
                ·
                  rfl

theorem cell20_308938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 6].length) (baseStart_308938 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_308938 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_308938 prefixEnd_308938 := by exact prefixLift 308938
  have htrace : WordTrace (prefixWord ++ tailWord_308938) baseStart_308938 baseEnd_308938 := by
    simpa [prefixWord, tailWord_308938, baseEnd_308938] using wordTrace_append hprefix tailTrace_308938
  have hstable : (prefixWord ++ tailWord_308938).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_308938).length < 2 ^ (prefixWord ++ tailWord_308938).sum := by decide
  have hdescent : baseEnd_308938 < baseStart_308938 := by decide
  rcases family_descends (prefixWord ++ tailWord_308938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309004 : List Nat := [2, 2, 1, 2, 2, 1, 2, 1, 7]
def baseStart_309004 : Nat := 118140960795 + 309004 * 2 ^ 59
def prefixEnd_309004 : Nat := 4983230072969 + 3 ^ 40 * 309004 * 2
def baseEnd_309004 : Nat := 141037845477346003670153

theorem tailTrace_309004 : CollatzResearch.WordTrace tailWord_309004 prefixEnd_309004 141037845477346003670153 := by
  unfold tailWord_309004
  simp only [CollatzResearch.WordTrace]
  refine ⟨5635150886269378263391033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7513534515025837684521377 5635150886269378263391033)
  ·
    refine ⟨4226363164702033697543275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5635150886269378263391033 4226363164702033697543275)
    ·
      refine ⟨6339544747053050546314913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4226363164702033697543275 6339544747053050546314913)
      ·
        refine ⟨4754658560289787909736185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6339544747053050546314913 4754658560289787909736185)
        ·
          refine ⟨3565993920217340932302139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4754658560289787909736185 3565993920217340932302139)
          ·
            refine ⟨5348990880326011398453209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3565993920217340932302139 5348990880326011398453209)
            ·
              refine ⟨4011743160244508548839907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5348990880326011398453209 4011743160244508548839907)
              ·
                refine ⟨6017614740366762823259861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4011743160244508548839907 6017614740366762823259861)
                ·
                  refine ⟨141037845477346003670153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6017614740366762823259861 141037845477346003670153)
                  ·
                    rfl

theorem cell20_309004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 7].length) (baseStart_309004 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_309004 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_309004 prefixEnd_309004 := by exact prefixLift 309004
  have htrace : WordTrace (prefixWord ++ tailWord_309004) baseStart_309004 baseEnd_309004 := by
    simpa [prefixWord, tailWord_309004, baseEnd_309004] using wordTrace_append hprefix tailTrace_309004
  have hstable : (prefixWord ++ tailWord_309004).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309004).length < 2 ^ (prefixWord ++ tailWord_309004).sum := by decide
  have hdescent : baseEnd_309004 < baseStart_309004 := by decide
  rcases family_descends (prefixWord ++ tailWord_309004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309011 : List Nat := [1, 1, 1, 2, 1, 3, 2, 1, 8]
def baseStart_309011 : Nat := 118140960795 + 309011 * 2 ^ 59
def prefixEnd_309011 : Nat := 4983230072969 + 3 ^ 40 * 309011 * 2
def baseEnd_309011 : Nat := 141041040468085090436791

theorem tailTrace_309011 : CollatzResearch.WordTrace tailWord_309011 prefixEnd_309011 141041040468085090436791 := by
  unfold tailWord_309011
  simp only [CollatzResearch.WordTrace]
  refine ⟨11270557083513396722286887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7513704722342264481524591 11270557083513396722286887)
  ·
    refine ⟨16905835625270095083430331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11270557083513396722286887 16905835625270095083430331)
    ·
      refine ⟨25358753437905142625145497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16905835625270095083430331 25358753437905142625145497)
      ·
        refine ⟨19019065078428856968859123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25358753437905142625145497 19019065078428856968859123)
        ·
          refine ⟨28528597617643285453288685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19019065078428856968859123 28528597617643285453288685)
          ·
            refine ⟨10698224106616232044983257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28528597617643285453288685 10698224106616232044983257)
            ·
              refine ⟨8023668079962174033737443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10698224106616232044983257 8023668079962174033737443)
              ·
                refine ⟨12035502119943261050606165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8023668079962174033737443 12035502119943261050606165)
                ·
                  refine ⟨141041040468085090436791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12035502119943261050606165 141041040468085090436791)
                  ·
                    rfl

theorem cell20_309011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 8].length) (baseStart_309011 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_309011 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_309011 prefixEnd_309011 := by exact prefixLift 309011
  have htrace : WordTrace (prefixWord ++ tailWord_309011) baseStart_309011 baseEnd_309011 := by
    simpa [prefixWord, tailWord_309011, baseEnd_309011] using wordTrace_append hprefix tailTrace_309011
  have hstable : (prefixWord ++ tailWord_309011).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309011).length < 2 ^ (prefixWord ++ tailWord_309011).sum := by decide
  have hdescent : baseEnd_309011 < baseStart_309011 := by decide
  rcases family_descends (prefixWord ++ tailWord_309011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309045 : List Nat := [1, 3, 3, 1, 4, 1, 1, 2, 4]
def baseStart_309045 : Nat := 118140960795 + 309045 * 2 ^ 59
def prefixEnd_309045 : Nat := 4983230072969 + 3 ^ 40 * 309045 * 2
def baseEnd_309045 : Nat := 141056558994532083303319

theorem tailTrace_309045 : CollatzResearch.WordTrace tailWord_309045 prefixEnd_309045 141056558994532083303319 := by
  unfold tailWord_309045
  simp only [CollatzResearch.WordTrace]
  refine ⟨11271797165390220529024589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7514531443593480352683059 11271797165390220529024589)
  ·
    refine ⟨4226923937021332698384221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11271797165390220529024589 4226923937021332698384221)
    ·
      refine ⟨1585096476382999761894083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4226923937021332698384221 1585096476382999761894083)
      ·
        refine ⟨2377644714574499642841125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1585096476382999761894083 2377644714574499642841125)
        ·
          refine ⟨445808383982718683032711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2377644714574499642841125 445808383982718683032711)
          ·
            refine ⟨668712575974078024549067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 445808383982718683032711 668712575974078024549067)
            ·
              refine ⟨1003068863961117036823601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 668712575974078024549067 1003068863961117036823601)
              ·
                refine ⟨752301647970837777617701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1003068863961117036823601 752301647970837777617701)
                ·
                  refine ⟨141056558994532083303319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 752301647970837777617701 141056558994532083303319)
                  ·
                    rfl

theorem cell20_309045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 2, 4].length) (baseStart_309045 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_309045 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_309045 prefixEnd_309045 := by exact prefixLift 309045
  have htrace : WordTrace (prefixWord ++ tailWord_309045) baseStart_309045 baseEnd_309045 := by
    simpa [prefixWord, tailWord_309045, baseEnd_309045] using wordTrace_append hprefix tailTrace_309045
  have hstable : (prefixWord ++ tailWord_309045).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309045).length < 2 ^ (prefixWord ++ tailWord_309045).sum := by decide
  have hdescent : baseEnd_309045 < baseStart_309045 := by decide
  rcases family_descends (prefixWord ++ tailWord_309045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309073 : List Nat := [1, 2, 2, 1, 5, 2, 7]
def baseStart_309073 : Nat := 118140960795 + 309073 * 2 ^ 59
def prefixEnd_309073 : Nat := 4983230072969 + 3 ^ 40 * 309073 * 2
def baseEnd_309073 : Nat := 15674370995276492263319

theorem tailTrace_309073 : CollatzResearch.WordTrace tailWord_309073 prefixEnd_309073 15674370995276492263319 := by
  unfold tailWord_309073
  simp only [CollatzResearch.WordTrace]
  refine ⟨11272818409288781311043873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7515212272859187540695915 11272818409288781311043873)
  ·
    refine ⟨8454613806966585983282905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11272818409288781311043873 8454613806966585983282905)
    ·
      refine ⟨6340960355224939487462179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8454613806966585983282905 6340960355224939487462179)
      ·
        refine ⟨9511440532837409231193269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6340960355224939487462179 9511440532837409231193269)
        ·
          refine ⟨891697549953507115424369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9511440532837409231193269 891697549953507115424369)
          ·
            refine ⟨668773162465130336568277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 891697549953507115424369 668773162465130336568277)
            ·
              refine ⟨15674370995276492263319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 668773162465130336568277 15674370995276492263319)
              ·
                rfl

theorem cell20_309073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 7].length) (baseStart_309073 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_309073 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_309073 prefixEnd_309073 := by exact prefixLift 309073
  have htrace : WordTrace (prefixWord ++ tailWord_309073) baseStart_309073 baseEnd_309073 := by
    simpa [prefixWord, tailWord_309073, baseEnd_309073] using wordTrace_append hprefix tailTrace_309073
  have hstable : (prefixWord ++ tailWord_309073).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309073).length < 2 ^ (prefixWord ++ tailWord_309073).sum := by decide
  have hdescent : baseEnd_309073 < baseStart_309073 := by decide
  rcases family_descends (prefixWord ++ tailWord_309073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309076 : List Nat := [2, 4, 1, 1, 3, 1, 3, 2, 3]
def baseStart_309076 : Nat := 118140960795 + 309076 * 2 ^ 59
def prefixEnd_309076 : Nat := 4983230072969 + 3 ^ 40 * 309076 * 2
def baseEnd_309076 : Nat := 141070708239233753269859

theorem tailTrace_309076 : CollatzResearch.WordTrace tailWord_309076 prefixEnd_309076 141070708239233753269859 := by
  unfold tailWord_309076
  simp only [CollatzResearch.WordTrace]
  refine ⟨5636463914138956411701541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7515285218851941882268721 5636463914138956411701541)
  ·
    refine ⟨1056836983901054327194039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5636463914138956411701541 1056836983901054327194039)
    ·
      refine ⟨1585255475851581490791059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1056836983901054327194039 1585255475851581490791059)
      ·
        refine ⟨2377883213777372236186589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1585255475851581490791059 2377883213777372236186589)
        ·
          refine ⟨891706205166514588569971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2377883213777372236186589 891706205166514588569971)
          ·
            refine ⟨1337559307749771882854957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 891706205166514588569971 1337559307749771882854957)
            ·
              refine ⟨501584740406164456070609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1337559307749771882854957 501584740406164456070609)
              ·
                refine ⟨376188555304623342052957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 501584740406164456070609 376188555304623342052957)
                ·
                  refine ⟨141070708239233753269859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 376188555304623342052957 141070708239233753269859)
                  ·
                    rfl

theorem cell20_309076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 3, 2, 3].length) (baseStart_309076 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_309076 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_309076 prefixEnd_309076 := by exact prefixLift 309076
  have htrace : WordTrace (prefixWord ++ tailWord_309076) baseStart_309076 baseEnd_309076 := by
    simpa [prefixWord, tailWord_309076, baseEnd_309076] using wordTrace_append hprefix tailTrace_309076
  have hstable : (prefixWord ++ tailWord_309076).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309076).length < 2 ^ (prefixWord ++ tailWord_309076).sum := by decide
  have hdescent : baseEnd_309076 < baseStart_309076 := by decide
  rcases family_descends (prefixWord ++ tailWord_309076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309128 : List Nat := [2, 1, 3, 3, 3, 2, 6]
def baseStart_309128 : Nat := 118140960795 + 309128 * 2 ^ 59
def prefixEnd_309128 : Nat := 4983230072969 + 3 ^ 40 * 309128 * 2
def baseEnd_309128 : Nat := 15677160272905853726257

theorem tailTrace_309128 : CollatzResearch.WordTrace tailWord_309128 prefixEnd_309128 15677160272905853726257 := by
  unfold tailWord_309128
  simp only [CollatzResearch.WordTrace]
  refine ⟨5637412212044762852148019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7516549616059683802864025 5637412212044762852148019)
  ·
    refine ⟨8456118318067144278222029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5637412212044762852148019 8456118318067144278222029)
    ·
      refine ⟨3171044369275179104333261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8456118318067144278222029 3171044369275179104333261)
      ·
        refine ⟨1189141638478192164124973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3171044369275179104333261 1189141638478192164124973)
        ·
          refine ⟨445928114429322061546865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1189141638478192164124973 445928114429322061546865)
          ·
            refine ⟨334446085821991546160149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 445928114429322061546865 334446085821991546160149)
            ·
              refine ⟨15677160272905853726257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 334446085821991546160149 15677160272905853726257)
              ·
                rfl

theorem cell20_309128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 6].length) (baseStart_309128 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_309128 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_309128 prefixEnd_309128 := by exact prefixLift 309128
  have htrace : WordTrace (prefixWord ++ tailWord_309128) baseStart_309128 baseEnd_309128 := by
    simpa [prefixWord, tailWord_309128, baseEnd_309128] using wordTrace_append hprefix tailTrace_309128
  have hstable : (prefixWord ++ tailWord_309128).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309128).length < 2 ^ (prefixWord ++ tailWord_309128).sum := by decide
  have hdescent : baseEnd_309128 < baseStart_309128 := by decide
  rcases family_descends (prefixWord ++ tailWord_309128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309134 : List Nat := [4, 1, 1, 5, 1, 1, 3, 2, 2]
def baseStart_309134 : Nat := 118140960795 + 309134 * 2 ^ 59
def prefixEnd_309134 : Nat := 4983230072969 + 3 ^ 40 * 309134 * 2
def baseEnd_309134 : Nat := 141097181019643329336289

theorem tailTrace_309134 : CollatzResearch.WordTrace tailWord_309134 prefixEnd_309134 141097181019643329336289 := by
  unfold tailWord_309134
  simp only [CollatzResearch.WordTrace]
  refine ⟨1409380407758473591126807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7516695508045192486009637 1409380407758473591126807)
  ·
    refine ⟨2114070611637710386690211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1409380407758473591126807 2114070611637710386690211)
    ·
      refine ⟨3171105917456565580035317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2114070611637710386690211 3171105917456565580035317)
      ·
        refine ⟨297291179761553023128311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3171105917456565580035317 297291179761553023128311)
        ·
          refine ⟨445936769642329534692467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 297291179761553023128311 445936769642329534692467)
          ·
            refine ⟨668905154463494302038701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 445936769642329534692467 668905154463494302038701)
            ·
              refine ⟨250839432923810363264513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 668905154463494302038701 250839432923810363264513)
              ·
                refine ⟨188129574692857772448385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 250839432923810363264513 188129574692857772448385)
                ·
                  refine ⟨141097181019643329336289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 188129574692857772448385 141097181019643329336289)
                  ·
                    rfl

theorem cell20_309134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 3, 2, 2].length) (baseStart_309134 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_309134 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_309134 prefixEnd_309134 := by exact prefixLift 309134
  have htrace : WordTrace (prefixWord ++ tailWord_309134) baseStart_309134 baseEnd_309134 := by
    simpa [prefixWord, tailWord_309134, baseEnd_309134] using wordTrace_append hprefix tailTrace_309134
  have hstable : (prefixWord ++ tailWord_309134).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309134).length < 2 ^ (prefixWord ++ tailWord_309134).sum := by decide
  have hdescent : baseEnd_309134 < baseStart_309134 := by decide
  rcases family_descends (prefixWord ++ tailWord_309134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309138 : List Nat := [3, 2, 3, 2, 1, 3, 1, 1, 4]
def baseStart_309138 : Nat := 118140960795 + 309138 * 2 ^ 59
def prefixEnd_309138 : Nat := 4983230072969 + 3 ^ 40 * 309138 * 2
def baseEnd_309138 : Nat := 141099006728637093202939

theorem tailTrace_309138 : CollatzResearch.WordTrace tailWord_309138 prefixEnd_309138 141099006728637093202939 := by
  unfold tailWord_309138
  simp only [CollatzResearch.WordTrace]
  refine ⟨2818797288513324353040017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7516792769368864941440045 2818797288513324353040017)
  ·
    refine ⟨2114097966384993264780013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2818797288513324353040017 2114097966384993264780013)
    ·
      refine ⟨792786737394372474292505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2114097966384993264780013 792786737394372474292505)
      ·
        refine ⟨594590053045779355719379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 792786737394372474292505 594590053045779355719379)
        ·
          refine ⟨891885079568669033579069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 594590053045779355719379 891885079568669033579069)
          ·
            refine ⟨334456904838250887592151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 891885079568669033579069 334456904838250887592151)
            ·
              refine ⟨501685357257376331388227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 334456904838250887592151 501685357257376331388227)
              ·
                refine ⟨752528035886064497082341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 501685357257376331388227 752528035886064497082341)
                ·
                  refine ⟨141099006728637093202939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 752528035886064497082341 141099006728637093202939)
                  ·
                    rfl

theorem cell20_309138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 1, 1, 4].length) (baseStart_309138 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_309138 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_309138 prefixEnd_309138 := by exact prefixLift 309138
  have htrace : WordTrace (prefixWord ++ tailWord_309138) baseStart_309138 baseEnd_309138 := by
    simpa [prefixWord, tailWord_309138, baseEnd_309138] using wordTrace_append hprefix tailTrace_309138
  have hstable : (prefixWord ++ tailWord_309138).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309138).length < 2 ^ (prefixWord ++ tailWord_309138).sum := by decide
  have hdescent : baseEnd_309138 < baseStart_309138 := by decide
  rcases family_descends (prefixWord ++ tailWord_309138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309149 : List Nat := [1, 4, 2, 1, 2, 2, 1, 7]
def baseStart_309149 : Nat := 118140960795 + 309149 * 2 ^ 59
def prefixEnd_309149 : Nat := 4983230072969 + 3 ^ 40 * 309149 * 2
def baseEnd_309149 : Nat := 47034675809456647945409

theorem tailTrace_309149 : CollatzResearch.WordTrace tailWord_309149 prefixEnd_309149 47034675809456647945409 := by
  unfold tailWord_309149
  simp only [CollatzResearch.WordTrace]
  refine ⟨11275590357013446290810501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7517060238008964193873667 11275590357013446290810501)
  ·
    refine ⟨2114173191940021179526969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11275590357013446290810501 2114173191940021179526969)
    ·
      refine ⟨1585629893955015884645227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2114173191940021179526969 1585629893955015884645227)
      ·
        refine ⟨2378444840932523826967841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1585629893955015884645227 2378444840932523826967841)
        ·
          refine ⟨1783833630699392870225881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2378444840932523826967841 1783833630699392870225881)
          ·
            refine ⟨1337875223024544652669411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1783833630699392870225881 1337875223024544652669411)
            ·
              refine ⟨2006812834536816979004117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1337875223024544652669411 2006812834536816979004117)
              ·
                refine ⟨47034675809456647945409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2006812834536816979004117 47034675809456647945409)
                ·
                  rfl

theorem cell20_309149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 7].length) (baseStart_309149 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_309149 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_309149 prefixEnd_309149 := by exact prefixLift 309149
  have htrace : WordTrace (prefixWord ++ tailWord_309149) baseStart_309149 baseEnd_309149 := by
    simpa [prefixWord, tailWord_309149, baseEnd_309149] using wordTrace_append hprefix tailTrace_309149
  have hstable : (prefixWord ++ tailWord_309149).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309149).length < 2 ^ (prefixWord ++ tailWord_309149).sum := by decide
  have hdescent : baseEnd_309149 < baseStart_309149 := by decide
  rcases family_descends (prefixWord ++ tailWord_309149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309194 : List Nat := [3, 1, 2, 1, 2, 1, 2, 3, 5]
def baseStart_309194 : Nat := 118140960795 + 309194 * 2 ^ 59
def prefixEnd_309194 : Nat := 4983230072969 + 3 ^ 40 * 309194 * 2
def baseEnd_309194 : Nat := 141124566654549787336043

theorem tailTrace_309194 : CollatzResearch.WordTrace tailWord_309194 prefixEnd_309194 141124566654549787336043 := by
  unfold tailWord_309194
  simp only [CollatzResearch.WordTrace]
  refine ⟨2819307910462604744049659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7518154427900279317465757 2819307910462604744049659)
  ·
    refine ⟨4228961865693907116074489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2819307910462604744049659 4228961865693907116074489)
    ·
      refine ⟨3171721399270430337055867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4228961865693907116074489 3171721399270430337055867)
      ·
        refine ⟨4757582098905645505583801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3171721399270430337055867 4757582098905645505583801)
        ·
          refine ⟨3568186574179234129187851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4757582098905645505583801 3568186574179234129187851)
          ·
            refine ⟨5352279861268851193781777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3568186574179234129187851 5352279861268851193781777)
            ·
              refine ⟨4014209895951638395336333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5352279861268851193781777 4014209895951638395336333)
              ·
                refine ⟨1505328710981864398251125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4014209895951638395336333 1505328710981864398251125)
                ·
                  refine ⟨141124566654549787336043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1505328710981864398251125 141124566654549787336043)
                  ·
                    rfl

theorem cell20_309194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 3, 5].length) (baseStart_309194 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_309194 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_309194 prefixEnd_309194 := by exact prefixLift 309194
  have htrace : WordTrace (prefixWord ++ tailWord_309194) baseStart_309194 baseEnd_309194 := by
    simpa [prefixWord, tailWord_309194, baseEnd_309194] using wordTrace_append hprefix tailTrace_309194
  have hstable : (prefixWord ++ tailWord_309194).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309194).length < 2 ^ (prefixWord ++ tailWord_309194).sum := by decide
  have hdescent : baseEnd_309194 < baseStart_309194 := by decide
  rcases family_descends (prefixWord ++ tailWord_309194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309252 : List Nat := [2, 3, 2, 4, 1, 1, 2, 1, 4]
def baseStart_309252 : Nat := 118140960795 + 309252 * 2 ^ 59
def prefixEnd_309252 : Nat := 4983230072969 + 3 ^ 40 * 309252 * 2
def baseEnd_309252 : Nat := 141151039434959363402473

theorem tailTrace_309252 : CollatzResearch.WordTrace tailWord_309252 prefixEnd_309252 141151039434959363402473 := by
  unfold tailWord_309252
  simp only [CollatzResearch.WordTrace]
  refine ⟨5639673537820147440905005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7519564717093529921206673 5639673537820147440905005)
  ·
    refine ⟨2114877576682555290339377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5639673537820147440905005 2114877576682555290339377)
    ·
      refine ⟨1586158182511916467754533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2114877576682555290339377 1586158182511916467754533)
      ·
        refine ⟨297404659220984337703975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1586158182511916467754533 297404659220984337703975)
        ·
          refine ⟨446106988831476506555963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 297404659220984337703975 446106988831476506555963)
          ·
            refine ⟨669160483247214759833945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 446106988831476506555963 669160483247214759833945)
            ·
              refine ⟨501870362435411069875459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 669160483247214759833945 501870362435411069875459)
              ·
                refine ⟨752805543653116604813189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 501870362435411069875459 752805543653116604813189)
                ·
                  refine ⟨141151039434959363402473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 752805543653116604813189 141151039434959363402473)
                  ·
                    rfl

theorem cell20_309252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 2, 1, 4].length) (baseStart_309252 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_309252 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_309252 prefixEnd_309252 := by exact prefixLift 309252
  have htrace : WordTrace (prefixWord ++ tailWord_309252) baseStart_309252 baseEnd_309252 := by
    simpa [prefixWord, tailWord_309252, baseEnd_309252] using wordTrace_append hprefix tailTrace_309252
  have hstable : (prefixWord ++ tailWord_309252).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309252).length < 2 ^ (prefixWord ++ tailWord_309252).sum := by decide
  have hdescent : baseEnd_309252 < baseStart_309252 := by decide
  rcases family_descends (prefixWord ++ tailWord_309252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309256 : List Nat := [2, 1, 3, 2, 1, 2, 4, 1, 4]
def baseStart_309256 : Nat := 118140960795 + 309256 * 2 ^ 59
def prefixEnd_309256 : Nat := 4983230072969 + 3 ^ 40 * 309256 * 2
def baseEnd_309256 : Nat := 141152865143953127269123

theorem tailTrace_309256 : CollatzResearch.WordTrace tailWord_309256 prefixEnd_309256 141152865143953127269123 := by
  unfold tailWord_309256
  simp only [CollatzResearch.WordTrace]
  refine ⟨5639746483812901782477811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7519661978417202376637081 5639746483812901782477811)
  ·
    refine ⟨8459619725719352673716717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5639746483812901782477811 8459619725719352673716717)
    ·
      refine ⟨3172357397144757252643769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8459619725719352673716717 3172357397144757252643769)
      ·
        refine ⟨2379268047858567939482827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3172357397144757252643769 2379268047858567939482827)
        ·
          refine ⟨3568902071787851909224241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2379268047858567939482827 3568902071787851909224241)
          ·
            refine ⟨2676676553840888931918181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3568902071787851909224241 2676676553840888931918181)
            ·
              refine ⟨501876853845166674734659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2676676553840888931918181 501876853845166674734659)
              ·
                refine ⟨752815280767750012101989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 501876853845166674734659 752815280767750012101989)
                ·
                  refine ⟨141152865143953127269123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 752815280767750012101989 141152865143953127269123)
                  ·
                    rfl

theorem cell20_309256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 4, 1, 4].length) (baseStart_309256 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_309256 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_309256 prefixEnd_309256 := by exact prefixLift 309256
  have htrace : WordTrace (prefixWord ++ tailWord_309256) baseStart_309256 baseEnd_309256 := by
    simpa [prefixWord, tailWord_309256, baseEnd_309256] using wordTrace_append hprefix tailTrace_309256
  have hstable : (prefixWord ++ tailWord_309256).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309256).length < 2 ^ (prefixWord ++ tailWord_309256).sum := by decide
  have hdescent : baseEnd_309256 < baseStart_309256 := by decide
  rcases family_descends (prefixWord ++ tailWord_309256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309290 : List Nat := [3, 1, 4, 1, 2, 1, 3, 3, 2]
def baseStart_309290 : Nat := 118140960795 + 309290 * 2 ^ 59
def prefixEnd_309290 : Nat := 4983230072969 + 3 ^ 40 * 309290 * 2
def baseEnd_309290 : Nat := 141168383670400120135651

theorem tailTrace_309290 : CollatzResearch.WordTrace tailWord_309290 prefixEnd_309290 141168383670400120135651 := by
  unfold tailWord_309290
  simp only [CollatzResearch.WordTrace]
  refine ⟨2820183262375656842923331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7520488699668418247795549 2820183262375656842923331)
  ·
    refine ⟨4230274893563485264384997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2820183262375656842923331 4230274893563485264384997)
    ·
      refine ⟨793176542543153487072187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4230274893563485264384997 793176542543153487072187)
      ·
        refine ⟨1189764813814730230608281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 793176542543153487072187 1189764813814730230608281)
        ·
          refine ⟨892323610361047672956211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1189764813814730230608281 892323610361047672956211)
          ·
            refine ⟨1338485415541571509434317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 892323610361047672956211 1338485415541571509434317)
            ·
              refine ⟨501932030828089316037869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1338485415541571509434317 501932030828089316037869)
              ·
                refine ⟨188224511560533493514201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 501932030828089316037869 188224511560533493514201)
                ·
                  refine ⟨141168383670400120135651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 188224511560533493514201 141168383670400120135651)
                  ·
                    rfl

theorem cell20_309290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 3, 3, 2].length) (baseStart_309290 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_309290 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_309290 prefixEnd_309290 := by exact prefixLift 309290
  have htrace : WordTrace (prefixWord ++ tailWord_309290) baseStart_309290 baseEnd_309290 := by
    simpa [prefixWord, tailWord_309290, baseEnd_309290] using wordTrace_append hprefix tailTrace_309290
  have hstable : (prefixWord ++ tailWord_309290).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309290).length < 2 ^ (prefixWord ++ tailWord_309290).sum := by decide
  have hdescent : baseEnd_309290 < baseStart_309290 := by decide
  rcases family_descends (prefixWord ++ tailWord_309290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309308 : List Nat := [2, 2, 2, 2, 2, 1, 1, 3, 5]
def baseStart_309308 : Nat := 118140960795 + 309308 * 2 ^ 59
def prefixEnd_309308 : Nat := 4983230072969 + 3 ^ 40 * 309308 * 2
def baseEnd_309308 : Nat := 141176599360872057535577

theorem tailTrace_309308 : CollatzResearch.WordTrace tailWord_309308 prefixEnd_309308 141176599360872057535577 := by
  unfold tailWord_309308
  simp only [CollatzResearch.WordTrace]
  refine ⟨5640694781718708222924289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7520926375624944297232385 5640694781718708222924289)
  ·
    refine ⟨4230521086289031167193217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5640694781718708222924289 4230521086289031167193217)
    ·
      refine ⟨3172890814716773375394913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4230521086289031167193217 3172890814716773375394913)
      ·
        refine ⟨2379668111037580031546185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3172890814716773375394913 2379668111037580031546185)
        ·
          refine ⟨1784751083278185023659639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2379668111037580031546185 1784751083278185023659639)
          ·
            refine ⟨2677126624917277535489459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1784751083278185023659639 2677126624917277535489459)
            ·
              refine ⟨4015689937375916303234189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2677126624917277535489459 4015689937375916303234189)
              ·
                refine ⟨1505883726515968613712821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4015689937375916303234189 1505883726515968613712821)
                ·
                  refine ⟨141176599360872057535577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1505883726515968613712821 141176599360872057535577)
                  ·
                    rfl

theorem cell20_309308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 3, 5].length) (baseStart_309308 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_309308 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_309308 prefixEnd_309308 := by exact prefixLift 309308
  have htrace : WordTrace (prefixWord ++ tailWord_309308) baseStart_309308 baseEnd_309308 := by
    simpa [prefixWord, tailWord_309308, baseEnd_309308] using wordTrace_append hprefix tailTrace_309308
  have hstable : (prefixWord ++ tailWord_309308).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309308).length < 2 ^ (prefixWord ++ tailWord_309308).sum := by decide
  have hdescent : baseEnd_309308 < baseStart_309308 := by decide
  rcases family_descends (prefixWord ++ tailWord_309308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309315 : List Nat := [1, 1, 1, 3, 1, 2, 2, 5, 4]
def baseStart_309315 : Nat := 118140960795 + 309315 * 2 ^ 59
def prefixEnd_309315 : Nat := 4983230072969 + 3 ^ 40 * 309315 * 2
def baseEnd_309315 : Nat := 141179794351611144302215

theorem tailTrace_309315 : CollatzResearch.WordTrace tailWord_309315 prefixEnd_309315 141179794351611144302215 := by
  unfold tailWord_309315
  simp only [CollatzResearch.WordTrace]
  refine ⟨11281644874412056641353399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7521096582941371094235599 11281644874412056641353399)
  ·
    refine ⟨16922467311618084962030099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11281644874412056641353399 16922467311618084962030099)
    ·
      refine ⟨25383700967427127443045149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16922467311618084962030099 25383700967427127443045149)
      ·
        refine ⟨9518887862785172791141931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25383700967427127443045149 9518887862785172791141931)
        ·
          refine ⟨14278331794177759186712897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9518887862785172791141931 14278331794177759186712897)
          ·
            refine ⟨10708748845633319390034673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14278331794177759186712897 10708748845633319390034673)
            ·
              refine ⟨8031561634224989542526005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10708748845633319390034673 8031561634224989542526005)
              ·
                refine ⟨752958903208592769611813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8031561634224989542526005 752958903208592769611813)
                ·
                  refine ⟨141179794351611144302215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 752958903208592769611813 141179794351611144302215)
                  ·
                    rfl

theorem cell20_309315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 5, 4].length) (baseStart_309315 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_309315 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_309315 prefixEnd_309315 := by exact prefixLift 309315
  have htrace : WordTrace (prefixWord ++ tailWord_309315) baseStart_309315 baseEnd_309315 := by
    simpa [prefixWord, tailWord_309315, baseEnd_309315] using wordTrace_append hprefix tailTrace_309315
  have hstable : (prefixWord ++ tailWord_309315).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309315).length < 2 ^ (prefixWord ++ tailWord_309315).sum := by decide
  have hdescent : baseEnd_309315 < baseStart_309315 := by decide
  rcases family_descends (prefixWord ++ tailWord_309315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309360 : List Nat := [2, 1, 1, 1, 5, 10]
def baseStart_309360 : Nat := 118140960795 + 309360 * 2 ^ 59
def prefixEnd_309360 : Nat := 4983230072969 + 3 ^ 40 * 309360 * 2
def baseEnd_309360 : Nat := 5229641984362629177853

theorem tailTrace_309360 : CollatzResearch.WordTrace tailWord_309360 prefixEnd_309360 5229641984362629177853 := by
  unfold tailWord_309360
  simp only [CollatzResearch.WordTrace]
  refine ⟨5641643079624514663370767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7522190772832686217827689 5641643079624514663370767)
  ·
    refine ⟨8462464619436771995056151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5641643079624514663370767 8462464619436771995056151)
    ·
      refine ⟨12693696929155157992584227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8462464619436771995056151 12693696929155157992584227)
      ·
        refine ⟨19040545393732736988876341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12693696929155157992584227 19040545393732736988876341)
        ·
          refine ⟨1785051130662444092707157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19040545393732736988876341 1785051130662444092707157)
          ·
            refine ⟨5229641984362629177853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1785051130662444092707157 5229641984362629177853)
            ·
              rfl

theorem cell20_309360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 10].length) (baseStart_309360 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_309360 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_309360 prefixEnd_309360 := by exact prefixLift 309360
  have htrace : WordTrace (prefixWord ++ tailWord_309360) baseStart_309360 baseEnd_309360 := by
    simpa [prefixWord, tailWord_309360, baseEnd_309360] using wordTrace_append hprefix tailTrace_309360
  have hstable : (prefixWord ++ tailWord_309360).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309360).length < 2 ^ (prefixWord ++ tailWord_309360).sum := by decide
  have hdescent : baseEnd_309360 < baseStart_309360 := by decide
  rcases family_descends (prefixWord ++ tailWord_309360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309366 : List Nat := [5, 1, 1, 2, 1, 3, 1, 4, 2]
def baseStart_309366 : Nat := 118140960795 + 309366 * 2 ^ 59
def prefixEnd_309366 : Nat := 4983230072969 + 3 ^ 40 * 309366 * 2
def baseEnd_309366 : Nat := 141203072141281633602007

theorem tailTrace_309366 : CollatzResearch.WordTrace tailWord_309366 prefixEnd_309366 141203072141281633602007 := by
  unfold tailWord_309366
  simp only [CollatzResearch.WordTrace]
  refine ⟨705219062326705771966247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7522336664818194900973301 705219062326705771966247)
  ·
    refine ⟨1057828593490058657949371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 705219062326705771966247 1057828593490058657949371)
    ·
      refine ⟨1586742890235087986924057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1057828593490058657949371 1586742890235087986924057)
      ·
        refine ⟨1190057167676315990193043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1586742890235087986924057 1190057167676315990193043)
        ·
          refine ⟨1785085751514473985289565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1190057167676315990193043 1785085751514473985289565)
          ·
            refine ⟨669407156817927744483587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1785085751514473985289565 669407156817927744483587)
            ·
              refine ⟨1004110735226891616725381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 669407156817927744483587 1004110735226891616725381)
              ·
                refine ⟨188270762855042178136009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1004110735226891616725381 188270762855042178136009)
                ·
                  refine ⟨141203072141281633602007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 188270762855042178136009 141203072141281633602007)
                  ·
                    rfl

theorem cell20_309366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 4, 2].length) (baseStart_309366 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_309366 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_309366 prefixEnd_309366 := by exact prefixLift 309366
  have htrace : WordTrace (prefixWord ++ tailWord_309366) baseStart_309366 baseEnd_309366 := by
    simpa [prefixWord, tailWord_309366, baseEnd_309366] using wordTrace_append hprefix tailTrace_309366
  have hstable : (prefixWord ++ tailWord_309366).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309366).length < 2 ^ (prefixWord ++ tailWord_309366).sum := by decide
  have hdescent : baseEnd_309366 < baseStart_309366 := by decide
  rcases family_descends (prefixWord ++ tailWord_309366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309394 : List Nat := [3, 2, 3, 1, 1, 1, 5, 4]
def baseStart_309394 : Nat := 118140960795 + 309394 * 2 ^ 59
def prefixEnd_309394 : Nat := 4983230072969 + 3 ^ 40 * 309394 * 2
def baseEnd_309394 : Nat := 47071950701412660222853

theorem tailTrace_309394 : CollatzResearch.WordTrace tailWord_309394 prefixEnd_309394 47071950701412660222853 := by
  unfold tailWord_309394
  simp only [CollatzResearch.WordTrace]
  refine ⟨2821131560281463283369809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7523017494083902088986157 2821131560281463283369809)
  ·
    refine ⟨2115848670211097462527357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2821131560281463283369809 2115848670211097462527357)
    ·
      refine ⟨793443251329161548447759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2115848670211097462527357 793443251329161548447759)
      ·
        refine ⟨1190164876993742322671639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 793443251329161548447759 1190164876993742322671639)
        ·
          refine ⟨1785247315490613484007459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1190164876993742322671639 1785247315490613484007459)
          ·
            refine ⟨2677870973235920226011189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1785247315490613484007459 2677870973235920226011189)
            ·
              refine ⟨251050403740867521188549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2677870973235920226011189 251050403740867521188549)
              ·
                refine ⟨47071950701412660222853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 251050403740867521188549 47071950701412660222853)
                ·
                  rfl

theorem cell20_309394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 5, 4].length) (baseStart_309394 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_309394 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_309394 prefixEnd_309394 := by exact prefixLift 309394
  have htrace : WordTrace (prefixWord ++ tailWord_309394) baseStart_309394 baseEnd_309394 := by
    simpa [prefixWord, tailWord_309394, baseEnd_309394] using wordTrace_append hprefix tailTrace_309394
  have hstable : (prefixWord ++ tailWord_309394).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309394).length < 2 ^ (prefixWord ++ tailWord_309394).sum := by decide
  have hdescent : baseEnd_309394 < baseStart_309394 := by decide
  rcases family_descends (prefixWord ++ tailWord_309394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309418 : List Nat := [3, 1, 5, 1, 2, 1, 1, 1, 5]
def baseStart_309418 : Nat := 118140960795 + 309418 * 2 ^ 59
def prefixEnd_309418 : Nat := 4983230072969 + 3 ^ 40 * 309418 * 2
def baseEnd_309418 : Nat := 141226806358200563868461

theorem tailTrace_309418 : CollatzResearch.WordTrace tailWord_309418 prefixEnd_309418 141226806358200563868461 := by
  unfold tailWord_309418
  simp only [CollatzResearch.WordTrace]
  refine ⟨2821350398259726308088227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7523601062025936821568605 2821350398259726308088227)
  ·
    refine ⟨4232025597389589462132341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2821350398259726308088227 4232025597389589462132341)
    ·
      refine ⟨396752399755274012074907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4232025597389589462132341 396752399755274012074907)
      ·
        refine ⟨595128599632911018112361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 396752399755274012074907 595128599632911018112361)
        ·
          refine ⟨446346449724683263584271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 595128599632911018112361 446346449724683263584271)
          ·
            refine ⟨669519674587024895376407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 446346449724683263584271 669519674587024895376407)
            ·
              refine ⟨1004279511880537343064611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 669519674587024895376407 1004279511880537343064611)
              ·
                refine ⟨1506419267820806014596917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1004279511880537343064611 1506419267820806014596917)
                ·
                  refine ⟨141226806358200563868461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1506419267820806014596917 141226806358200563868461)
                  ·
                    rfl

theorem cell20_309418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 1, 5].length) (baseStart_309418 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_309418 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_309418 prefixEnd_309418 := by exact prefixLift 309418
  have htrace : WordTrace (prefixWord ++ tailWord_309418) baseStart_309418 baseEnd_309418 := by
    simpa [prefixWord, tailWord_309418, baseEnd_309418] using wordTrace_append hprefix tailTrace_309418
  have hstable : (prefixWord ++ tailWord_309418).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309418).length < 2 ^ (prefixWord ++ tailWord_309418).sum := by decide
  have hdescent : baseEnd_309418 < baseStart_309418 := by decide
  rcases family_descends (prefixWord ++ tailWord_309418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309425 : List Nat := [1, 2, 2, 5, 2, 1, 2, 1, 4]
def baseStart_309425 : Nat := 118140960795 + 309425 * 2 ^ 59
def prefixEnd_309425 : Nat := 4983230072969 + 3 ^ 40 * 309425 * 2
def baseEnd_309425 : Nat := 141230001348939650635099

theorem tailTrace_309425 : CollatzResearch.WordTrace tailWord_309425 prefixEnd_309425 141230001348939650635099 := by
  unfold tailWord_309425
  simp only [CollatzResearch.WordTrace]
  refine ⟨11285656904013545427857729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7523771269342363618571819 11285656904013545427857729)
  ·
    refine ⟨8464242678010159070893297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11285656904013545427857729 8464242678010159070893297)
    ·
      refine ⟨6348182008507619303169973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8464242678010159070893297 6348182008507619303169973)
      ·
        refine ⟨595142063297589309672185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6348182008507619303169973 595142063297589309672185)
        ·
          refine ⟨446356547473191982254139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 595142063297589309672185 446356547473191982254139)
          ·
            refine ⟨669534821209787973381209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 446356547473191982254139 669534821209787973381209)
            ·
              refine ⟨502151115907340980035907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 669534821209787973381209 502151115907340980035907)
              ·
                refine ⟨753226673861011470053861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 502151115907340980035907 753226673861011470053861)
                ·
                  refine ⟨141230001348939650635099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 753226673861011470053861 141230001348939650635099)
                  ·
                    rfl

theorem cell20_309425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 2, 1, 4].length) (baseStart_309425 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_309425 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_309425 prefixEnd_309425 := by exact prefixLift 309425
  have htrace : WordTrace (prefixWord ++ tailWord_309425) baseStart_309425 baseEnd_309425 := by
    simpa [prefixWord, tailWord_309425, baseEnd_309425] using wordTrace_append hprefix tailTrace_309425
  have hstable : (prefixWord ++ tailWord_309425).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309425).length < 2 ^ (prefixWord ++ tailWord_309425).sum := by decide
  have hdescent : baseEnd_309425 < baseStart_309425 := by decide
  rcases family_descends (prefixWord ++ tailWord_309425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309442 : List Nat := [3, 5, 1, 1, 1, 1, 2, 2, 4]
def baseStart_309442 : Nat := 118140960795 + 309442 * 2 ^ 59
def prefixEnd_309442 : Nat := 4983230072969 + 3 ^ 40 * 309442 * 2
def baseEnd_309442 : Nat := 141237760612163147068363

theorem tailTrace_309442 : CollatzResearch.WordTrace tailWord_309442 prefixEnd_309442 141237760612163147068363 := by
  unfold tailWord_309442
  simp only [CollatzResearch.WordTrace]
  refine ⟨2821569236237989332806645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7524184629967971554151053 2821569236237989332806645)
  ·
    refine ⟨264522115897311499950623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2821569236237989332806645 264522115897311499950623)
    ·
      refine ⟨396783173845967249925935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 264522115897311499950623 396783173845967249925935)
      ·
        refine ⟨595174760768950874888903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 396783173845967249925935 595174760768950874888903)
        ·
          refine ⟨892762141153426312333355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 595174760768950874888903 892762141153426312333355)
          ·
            refine ⟨1339143211730139468500033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 892762141153426312333355 1339143211730139468500033)
            ·
              refine ⟨1004357408797604601375025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1339143211730139468500033 1004357408797604601375025)
              ·
                refine ⟨753268056598203451031269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1004357408797604601375025 753268056598203451031269)
                ·
                  refine ⟨141237760612163147068363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 753268056598203451031269 141237760612163147068363)
                  ·
                    rfl

theorem cell20_309442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_309442 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_309442 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_309442 prefixEnd_309442 := by exact prefixLift 309442
  have htrace : WordTrace (prefixWord ++ tailWord_309442) baseStart_309442 baseEnd_309442 := by
    simpa [prefixWord, tailWord_309442, baseEnd_309442] using wordTrace_append hprefix tailTrace_309442
  have hstable : (prefixWord ++ tailWord_309442).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309442).length < 2 ^ (prefixWord ++ tailWord_309442).sum := by decide
  have hdescent : baseEnd_309442 < baseStart_309442 := by decide
  rcases family_descends (prefixWord ++ tailWord_309442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309480 : List Nat := [2, 1, 4, 1, 2, 3, 3, 2, 2]
def baseStart_309480 : Nat := 118140960795 + 309480 * 2 ^ 59
def prefixEnd_309480 : Nat := 4983230072969 + 3 ^ 40 * 309480 * 2
def baseEnd_309480 : Nat := 141255104847603903801541

theorem tailTrace_309480 : CollatzResearch.WordTrace tailWord_309480 prefixEnd_309480 141255104847603903801541 := by
  unfold tailWord_309480
  simp only [CollatzResearch.WordTrace]
  refine ⟨5643831459407144910554947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7525108612542859880739929 5643831459407144910554947)
  ·
    refine ⟨8465747189110717365832421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5643831459407144910554947 8465747189110717365832421)
    ·
      refine ⟨1587327597958259506093579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8465747189110717365832421 1587327597958259506093579)
      ·
        refine ⟨2380991396937389259140369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1587327597958259506093579 2380991396937389259140369)
        ·
          refine ⟨1785743547703041944355277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2380991396937389259140369 1785743547703041944355277)
          ·
            refine ⟨669653830388640729133229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1785743547703041944355277 669653830388640729133229)
            ·
              refine ⟨251120186395740273424961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 669653830388640729133229 251120186395740273424961)
              ·
                refine ⟨188340139796805205068721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 251120186395740273424961 188340139796805205068721)
                ·
                  refine ⟨141255104847603903801541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 188340139796805205068721 141255104847603903801541)
                  ·
                    rfl

theorem cell20_309480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 3, 2, 2].length) (baseStart_309480 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_309480 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_309480 prefixEnd_309480 := by exact prefixLift 309480
  have htrace : WordTrace (prefixWord ++ tailWord_309480) baseStart_309480 baseEnd_309480 := by
    simpa [prefixWord, tailWord_309480, baseEnd_309480] using wordTrace_append hprefix tailTrace_309480
  have hstable : (prefixWord ++ tailWord_309480).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309480).length < 2 ^ (prefixWord ++ tailWord_309480).sum := by decide
  have hdescent : baseEnd_309480 < baseStart_309480 := by decide
  rcases family_descends (prefixWord ++ tailWord_309480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309494 : List Nat := [5, 1, 1, 1, 1, 1, 6, 1, 3]
def baseStart_309494 : Nat := 118140960795 + 309494 * 2 ^ 59
def prefixEnd_309494 : Nat := 4983230072969 + 3 ^ 40 * 309494 * 2
def baseEnd_309494 : Nat := 141261494829082077334817

theorem tailTrace_309494 : CollatzResearch.WordTrace tailWord_309494 prefixEnd_309494 141261494829082077334817 := by
  unfold tailWord_309494
  simp only [CollatzResearch.WordTrace]
  refine ⟨705510846297723138257471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7525449027175713474746357 705510846297723138257471)
  ·
    refine ⟨1058266269446584707386207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 705510846297723138257471 1058266269446584707386207)
    ·
      refine ⟨1587399404169877061079311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1058266269446584707386207 1587399404169877061079311)
      ·
        refine ⟨2381099106254815591618967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1587399404169877061079311 2381099106254815591618967)
        ·
          refine ⟨3571648659382223387428451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2381099106254815591618967 3571648659382223387428451)
          ·
            refine ⟨5357472989073335081142677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3571648659382223387428451 5357472989073335081142677)
            ·
              refine ⟨251131546362812581928563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 5357472989073335081142677 251131546362812581928563)
              ·
                refine ⟨376697319544218872892845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 251131546362812581928563 376697319544218872892845)
                ·
                  refine ⟨141261494829082077334817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 376697319544218872892845 141261494829082077334817)
                  ·
                    rfl

theorem cell20_309494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 6, 1, 3].length) (baseStart_309494 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_309494 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_309494 prefixEnd_309494 := by exact prefixLift 309494
  have htrace : WordTrace (prefixWord ++ tailWord_309494) baseStart_309494 baseEnd_309494 := by
    simpa [prefixWord, tailWord_309494, baseEnd_309494] using wordTrace_append hprefix tailTrace_309494
  have hstable : (prefixWord ++ tailWord_309494).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309494).length < 2 ^ (prefixWord ++ tailWord_309494).sum := by decide
  have hdescent : baseEnd_309494 < baseStart_309494 := by decide
  rcases family_descends (prefixWord ++ tailWord_309494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309505 : List Nat := [1, 2, 4, 1, 1, 2, 2, 1, 6]
def baseStart_309505 : Nat := 118140960795 + 309505 * 2 ^ 59
def prefixEnd_309505 : Nat := 4983230072969 + 3 ^ 40 * 309505 * 2
def baseEnd_309505 : Nat := 141266515528814927968105

theorem tailTrace_309505 : CollatzResearch.WordTrace tailWord_309505 prefixEnd_309505 141266515528814927968105 := by
  unfold tailWord_309505
  simp only [CollatzResearch.WordTrace]
  refine ⟨11288574743723719090769969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7525716495815812727179979 11288574743723719090769969)
  ·
    refine ⟨8466431057792789318077477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11288574743723719090769969 8466431057792789318077477)
    ·
      refine ⟨1587455823336147997139527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8466431057792789318077477 1587455823336147997139527)
      ·
        refine ⟨2381183735004221995709291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1587455823336147997139527 2381183735004221995709291)
        ·
          refine ⟨3571775602506332993563937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2381183735004221995709291 3571775602506332993563937)
          ·
            refine ⟨2678831701879749745172953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3571775602506332993563937 2678831701879749745172953)
            ·
              refine ⟨2009123776409812308879715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2678831701879749745172953 2009123776409812308879715)
              ·
                refine ⟨3013685664614718463319573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2009123776409812308879715 3013685664614718463319573)
                ·
                  refine ⟨141266515528814927968105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3013685664614718463319573 141266515528814927968105)
                  ·
                    rfl

theorem cell20_309505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 1, 6].length) (baseStart_309505 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_309505 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_309505 prefixEnd_309505 := by exact prefixLift 309505
  have htrace : WordTrace (prefixWord ++ tailWord_309505) baseStart_309505 baseEnd_309505 := by
    simpa [prefixWord, tailWord_309505, baseEnd_309505] using wordTrace_append hprefix tailTrace_309505
  have hstable : (prefixWord ++ tailWord_309505).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309505).length < 2 ^ (prefixWord ++ tailWord_309505).sum := by decide
  have hdescent : baseEnd_309505 < baseStart_309505 := by decide
  rcases family_descends (prefixWord ++ tailWord_309505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309519 : List Nat := [1, 1, 2, 1, 1, 1, 3, 3, 7]
def baseStart_309519 : Nat := 118140960795 + 309519 * 2 ^ 59
def prefixEnd_309519 : Nat := 4983230072969 + 3 ^ 40 * 309519 * 2
def baseEnd_309519 : Nat := 141272905510293101501381

theorem tailTrace_309519 : CollatzResearch.WordTrace tailWord_309519 prefixEnd_309519 141272905510293101501381 := by
  unfold tailWord_309519
  simp only [CollatzResearch.WordTrace]
  refine ⟨11289085365672999481779611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7526056910448666321186407 11289085365672999481779611)
  ·
    refine ⟨16933628048509499222669417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11289085365672999481779611 16933628048509499222669417)
    ·
      refine ⟨12700221036382124417002063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16933628048509499222669417 12700221036382124417002063)
      ·
        refine ⟨19050331554573186625503095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12700221036382124417002063 19050331554573186625503095)
        ·
          refine ⟨28575497331859779938254643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19050331554573186625503095 28575497331859779938254643)
          ·
            refine ⟨42863245997789669907381965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28575497331859779938254643 42863245997789669907381965)
            ·
              refine ⟨16073717249171126215268237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42863245997789669907381965 16073717249171126215268237)
              ·
                refine ⟨6027643968439172330725589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16073717249171126215268237 6027643968439172330725589)
                ·
                  refine ⟨141272905510293101501381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6027643968439172330725589 141272905510293101501381)
                  ·
                    rfl

theorem cell20_309519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 3, 7].length) (baseStart_309519 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_309519 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_309519 prefixEnd_309519 := by exact prefixLift 309519
  have htrace : WordTrace (prefixWord ++ tailWord_309519) baseStart_309519 baseEnd_309519 := by
    simpa [prefixWord, tailWord_309519, baseEnd_309519] using wordTrace_append hprefix tailTrace_309519
  have hstable : (prefixWord ++ tailWord_309519).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309519).length < 2 ^ (prefixWord ++ tailWord_309519).sum := by decide
  have hdescent : baseEnd_309519 < baseStart_309519 := by decide
  rcases family_descends (prefixWord ++ tailWord_309519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309567 : List Nat := [1, 1, 2, 2, 4, 1, 5, 4]
def baseStart_309567 : Nat := 118140960795 + 309567 * 2 ^ 59
def prefixEnd_309567 : Nat := 4983230072969 + 3 ^ 40 * 309567 * 2
def baseEnd_309567 : Nat := 47098271339406089300395

theorem tailTrace_309567 : CollatzResearch.WordTrace tailWord_309567 prefixEnd_309567 47098271339406089300395 := by
  unfold tailWord_309567
  simp only [CollatzResearch.WordTrace]
  refine ⟨11290836069499103679526955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7527224046332735786351303 11290836069499103679526955)
  ·
    refine ⟨16936254104248655519290433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11290836069499103679526955 16936254104248655519290433)
    ·
      refine ⟨12702190578186491639467825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16936254104248655519290433 12702190578186491639467825)
      ·
        refine ⟨9526642933639868729600869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12702190578186491639467825 9526642933639868729600869)
        ·
          refine ⟨1786245550057475386800163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9526642933639868729600869 1786245550057475386800163)
          ·
            refine ⟨2679368325086213080200245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1786245550057475386800163 2679368325086213080200245)
            ·
              refine ⟨251190780476832476268773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2679368325086213080200245 251190780476832476268773)
              ·
                refine ⟨47098271339406089300395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 251190780476832476268773 47098271339406089300395)
                ·
                  rfl

theorem cell20_309567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 5, 4].length) (baseStart_309567 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_309567 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_309567 prefixEnd_309567 := by exact prefixLift 309567
  have htrace : WordTrace (prefixWord ++ tailWord_309567) baseStart_309567 baseEnd_309567 := by
    simpa [prefixWord, tailWord_309567, baseEnd_309567] using wordTrace_append hprefix tailTrace_309567
  have hstable : (prefixWord ++ tailWord_309567).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309567).length < 2 ^ (prefixWord ++ tailWord_309567).sum := by decide
  have hdescent : baseEnd_309567 < baseStart_309567 := by decide
  rcases family_descends (prefixWord ++ tailWord_309567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309608 : List Nat := [2, 1, 4, 2, 2, 2, 3, 1, 3]
def baseStart_309608 : Nat := 118140960795 + 309608 * 2 ^ 59
def prefixEnd_309608 : Nat := 4983230072969 + 3 ^ 40 * 309608 * 2
def baseEnd_309608 : Nat := 141313527535404347534351

theorem tailTrace_309608 : CollatzResearch.WordTrace tailWord_309608 prefixEnd_309608 141313527535404347534351 := by
  unfold tailWord_309608
  simp only [CollatzResearch.WordTrace]
  refine ⟨5646165731175283840884739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7528220974900378454512985 5646165731175283840884739)
  ·
    refine ⟨8469248596762925761327109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5646165731175283840884739 8469248596762925761327109)
    ·
      refine ⟨1587984111893048580248833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8469248596762925761327109 1587984111893048580248833)
      ·
        refine ⟨1190988083919786435186625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1587984111893048580248833 1190988083919786435186625)
        ·
          refine ⟨893241062939839826389969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1190988083919786435186625 893241062939839826389969)
          ·
            refine ⟨669930797204879869792477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 893241062939839826389969 669930797204879869792477)
            ·
              refine ⟨251224048951829951172179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 669930797204879869792477 251224048951829951172179)
              ·
                refine ⟨376836073427744926758269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 251224048951829951172179 376836073427744926758269)
                ·
                  refine ⟨141313527535404347534351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 376836073427744926758269 141313527535404347534351)
                  ·
                    rfl

theorem cell20_309608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 3, 1, 3].length) (baseStart_309608 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_309608 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_309608 prefixEnd_309608 := by exact prefixLift 309608
  have htrace : WordTrace (prefixWord ++ tailWord_309608) baseStart_309608 baseEnd_309608 := by
    simpa [prefixWord, tailWord_309608, baseEnd_309608] using wordTrace_append hprefix tailTrace_309608
  have hstable : (prefixWord ++ tailWord_309608).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309608).length < 2 ^ (prefixWord ++ tailWord_309608).sum := by decide
  have hdescent : baseEnd_309608 < baseStart_309608 := by decide
  rcases family_descends (prefixWord ++ tailWord_309608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309664 : List Nat := [2, 1, 1, 4, 1, 3, 1, 7]
def baseStart_309664 : Nat := 118140960795 + 309664 * 2 ^ 59
def prefixEnd_309664 : Nat := 4983230072969 + 3 ^ 40 * 309664 * 2
def baseEnd_309664 : Nat := 47113029153772347222485

theorem tailTrace_309664 : CollatzResearch.WordTrace tailWord_309664 prefixEnd_309664 47113029153772347222485 := by
  unfold tailWord_309664
  simp only [CollatzResearch.WordTrace]
  refine ⟨5647186975073844622904023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7529582633431792830538697 5647186975073844622904023)
  ·
    refine ⟨8470780462610766934356035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5647186975073844622904023 8470780462610766934356035)
    ·
      refine ⟨12706170693916150401534053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8470780462610766934356035 12706170693916150401534053)
      ·
        refine ⟨2382407005109278200287635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12706170693916150401534053 2382407005109278200287635)
        ·
          refine ⟨3573610507663917300431453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2382407005109278200287635 3573610507663917300431453)
          ·
            refine ⟨1340103940373968987661795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3573610507663917300431453 1340103940373968987661795)
            ·
              refine ⟨2010155910560953481492693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1340103940373968987661795 2010155910560953481492693)
              ·
                refine ⟨47113029153772347222485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2010155910560953481492693 47113029153772347222485)
                ·
                  rfl

theorem cell20_309664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 7].length) (baseStart_309664 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_309664 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_309664 prefixEnd_309664 := by exact prefixLift 309664
  have htrace : WordTrace (prefixWord ++ tailWord_309664) baseStart_309664 baseEnd_309664 := by
    simpa [prefixWord, tailWord_309664, baseEnd_309664] using wordTrace_append hprefix tailTrace_309664
  have hstable : (prefixWord ++ tailWord_309664).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309664).length < 2 ^ (prefixWord ++ tailWord_309664).sum := by decide
  have hdescent : baseEnd_309664 < baseStart_309664 := by decide
  rcases family_descends (prefixWord ++ tailWord_309664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309667 : List Nat := [1, 1, 1, 4, 1, 4, 4, 1, 3]
def baseStart_309667 : Nat := 118140960795 + 309667 * 2 ^ 59
def prefixEnd_309667 : Nat := 4983230072969 + 3 ^ 40 * 309667 * 2
def baseEnd_309667 : Nat := 141340456743062364567443

theorem tailTrace_309667 : CollatzResearch.WordTrace tailWord_309667 prefixEnd_309667 141340456743062364567443 := by
  unfold tailWord_309667
  simp only [CollatzResearch.WordTrace]
  refine ⟨11294483369136820758167255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7529655579424547172111503 11294483369136820758167255)
  ·
    refine ⟨16941725053705231137250883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11294483369136820758167255 16941725053705231137250883)
    ·
      refine ⟨25412587580557846705876325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16941725053705231137250883 25412587580557846705876325)
      ·
        refine ⟨4764860171354596257351811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25412587580557846705876325 4764860171354596257351811)
        ·
          refine ⟨7147290257031894386027717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4764860171354596257351811 7147290257031894386027717)
          ·
            refine ⟨1340116923193480197380197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7147290257031894386027717 1340116923193480197380197)
            ·
              refine ⟨251271923098777537008787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1340116923193480197380197 251271923098777537008787)
              ·
                refine ⟨376907884648166305513181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 251271923098777537008787 376907884648166305513181)
                ·
                  refine ⟨141340456743062364567443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 376907884648166305513181 141340456743062364567443)
                  ·
                    rfl

theorem cell20_309667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 4, 1, 3].length) (baseStart_309667 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_309667 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_309667 prefixEnd_309667 := by exact prefixLift 309667
  have htrace : WordTrace (prefixWord ++ tailWord_309667) baseStart_309667 baseEnd_309667 := by
    simpa [prefixWord, tailWord_309667, baseEnd_309667] using wordTrace_append hprefix tailTrace_309667
  have hstable : (prefixWord ++ tailWord_309667).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309667).length < 2 ^ (prefixWord ++ tailWord_309667).sum := by decide
  have hdescent : baseEnd_309667 < baseStart_309667 := by decide
  rcases family_descends (prefixWord ++ tailWord_309667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309698 : List Nat := [3, 5, 2, 10]
def baseStart_309698 : Nat := 118140960795 + 309698 * 2 ^ 59
def prefixEnd_309698 : Nat := 4983230072969 + 3 ^ 40 * 309698 * 2
def baseEnd_309698 : Nat := 581706197480510430181

theorem tailTrace_309698 : CollatzResearch.WordTrace tailWord_309698 prefixEnd_309698 581706197480510430181 := by
  unfold tailWord_309698
  simp only [CollatzResearch.WordTrace]
  refine ⟨2823903508006128263136437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7530409354683008701697165 2823903508006128263136437)
  ·
    refine ⟨264740953875574524669041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2823903508006128263136437 264740953875574524669041)
    ·
      refine ⟨198555715406680893501781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 264740953875574524669041 198555715406680893501781)
      ·
        refine ⟨581706197480510430181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 10 198555715406680893501781 581706197480510430181)
        ·
          rfl

theorem cell20_309698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 10].length) (baseStart_309698 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_309698 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_309698 prefixEnd_309698 := by exact prefixLift 309698
  have htrace : WordTrace (prefixWord ++ tailWord_309698) baseStart_309698 baseEnd_309698 := by
    simpa [prefixWord, tailWord_309698, baseEnd_309698] using wordTrace_append hprefix tailTrace_309698
  have hstable : (prefixWord ++ tailWord_309698).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309698).length < 2 ^ (prefixWord ++ tailWord_309698).sum := by decide
  have hdescent : baseEnd_309698 < baseStart_309698 := by decide
  rcases family_descends (prefixWord ++ tailWord_309698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309746 : List Nat := [3, 2, 1, 4, 2, 1, 2, 3, 2]
def baseStart_309746 : Nat := 118140960795 + 309746 * 2 ^ 59
def prefixEnd_309746 : Nat := 4983230072969 + 3 ^ 40 * 309746 * 2
def baseEnd_309746 : Nat := 141376514495689200933787

theorem tailTrace_309746 : CollatzResearch.WordTrace tailWord_309746 prefixEnd_309746 141376514495689200933787 := by
  unfold tailWord_309746
  simp only [CollatzResearch.WordTrace]
  refine ⟨2824341183962654312573273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7531576490567078166862061 2824341183962654312573273)
  ·
    refine ⟨2118255887971990734429955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2824341183962654312573273 2118255887971990734429955)
    ·
      refine ⟨3177383831957986101644933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2118255887971990734429955 3177383831957986101644933)
      ·
        refine ⟨595759468492122394058425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3177383831957986101644933 595759468492122394058425)
        ·
          refine ⟨446819601369091795543819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 595759468492122394058425 446819601369091795543819)
          ·
            refine ⟨670229402053637693315729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 446819601369091795543819 670229402053637693315729)
            ·
              refine ⟨502672051540228269986797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 670229402053637693315729 502672051540228269986797)
              ·
                refine ⟨188502019327585601245049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 502672051540228269986797 188502019327585601245049)
                ·
                  refine ⟨141376514495689200933787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 188502019327585601245049 141376514495689200933787)
                  ·
                    rfl

theorem cell20_309746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 2, 3, 2].length) (baseStart_309746 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_309746 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_309746 prefixEnd_309746 := by exact prefixLift 309746
  have htrace : WordTrace (prefixWord ++ tailWord_309746) baseStart_309746 baseEnd_309746 := by
    simpa [prefixWord, tailWord_309746, baseEnd_309746] using wordTrace_append hprefix tailTrace_309746
  have hstable : (prefixWord ++ tailWord_309746).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309746).length < 2 ^ (prefixWord ++ tailWord_309746).sum := by decide
  have hdescent : baseEnd_309746 < baseStart_309746 := by decide
  rcases family_descends (prefixWord ++ tailWord_309746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309747 : List Nat := [1, 1, 1, 2, 2, 2, 4, 2, 5]
def baseStart_309747 : Nat := 118140960795 + 309747 * 2 ^ 59
def prefixEnd_309747 : Nat := 4983230072969 + 3 ^ 40 * 309747 * 2
def baseEnd_309747 : Nat := 141376970922937641900449

theorem tailTrace_309747 : CollatzResearch.WordTrace tailWord_309747 prefixEnd_309747 141376970922937641900449 := by
  unfold tailWord_309747
  simp only [CollatzResearch.WordTrace]
  refine ⟨11297401208846994421079495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7531600805897996280719663 11297401208846994421079495)
  ·
    refine ⟨16946101813270491631619243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11297401208846994421079495 16946101813270491631619243)
    ·
      refine ⟨25419152719905737447428865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16946101813270491631619243 25419152719905737447428865)
      ·
        refine ⟨19064364539929303085571649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25419152719905737447428865 19064364539929303085571649)
        ·
          refine ⟨14298273404946977314178737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19064364539929303085571649 14298273404946977314178737)
          ·
            refine ⟨10723705053710232985634053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14298273404946977314178737 10723705053710232985634053)
            ·
              refine ⟨2010694697570668684806385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10723705053710232985634053 2010694697570668684806385)
              ·
                refine ⟨1508021023178001513604789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2010694697570668684806385 1508021023178001513604789)
                ·
                  refine ⟨141376970922937641900449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1508021023178001513604789 141376970922937641900449)
                  ·
                    rfl

theorem cell20_309747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 2, 5].length) (baseStart_309747 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_309747 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_309747 prefixEnd_309747 := by exact prefixLift 309747
  have htrace : WordTrace (prefixWord ++ tailWord_309747) baseStart_309747 baseEnd_309747 := by
    simpa [prefixWord, tailWord_309747, baseEnd_309747] using wordTrace_append hprefix tailTrace_309747
  have hstable : (prefixWord ++ tailWord_309747).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309747).length < 2 ^ (prefixWord ++ tailWord_309747).sum := by decide
  have hdescent : baseEnd_309747 < baseStart_309747 := by decide
  rcases family_descends (prefixWord ++ tailWord_309747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309771 : List Nat := [1, 1, 1, 1, 7, 1, 1, 3, 4]
def baseStart_309771 : Nat := 118140960795 + 309771 * 2 ^ 59
def prefixEnd_309771 : Nat := 4983230072969 + 3 ^ 40 * 309771 * 2
def baseEnd_309771 : Nat := 141387925176900225100351

theorem tailTrace_309771 : CollatzResearch.WordTrace tailWord_309771 prefixEnd_309771 141387925176900225100351 := by
  unfold tailWord_309771
  simp only [CollatzResearch.WordTrace]
  refine ⟨11298276560760046519953167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7532184373840031013302111 11298276560760046519953167)
  ·
    refine ⟨16947414841140069779929751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11298276560760046519953167 16947414841140069779929751)
    ·
      refine ⟨25421122261710104669894627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16947414841140069779929751 25421122261710104669894627)
      ·
        refine ⟨38131683392565157004841941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25421122261710104669894627 38131683392565157004841941)
        ·
          refine ⟨893711329513245867300983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 38131683392565157004841941 893711329513245867300983)
          ·
            refine ⟨1340566994269868800951475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 893711329513245867300983 1340566994269868800951475)
            ·
              refine ⟨2010850491404803201427213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1340566994269868800951475 2010850491404803201427213)
              ·
                refine ⟨754068934276801200535205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2010850491404803201427213 754068934276801200535205)
                ·
                  refine ⟨141387925176900225100351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 754068934276801200535205 141387925176900225100351)
                  ·
                    rfl

theorem cell20_309771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 3, 4].length) (baseStart_309771 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_309771 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_309771 prefixEnd_309771 := by exact prefixLift 309771
  have htrace : WordTrace (prefixWord ++ tailWord_309771) baseStart_309771 baseEnd_309771 := by
    simpa [prefixWord, tailWord_309771, baseEnd_309771] using wordTrace_append hprefix tailTrace_309771
  have hstable : (prefixWord ++ tailWord_309771).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309771).length < 2 ^ (prefixWord ++ tailWord_309771).sum := by decide
  have hdescent : baseEnd_309771 < baseStart_309771 := by decide
  rcases family_descends (prefixWord ++ tailWord_309771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309781 : List Nat := [1, 3, 2, 1, 3, 1, 5, 1, 3]
def baseStart_309781 : Nat := 118140960795 + 309781 * 2 ^ 59
def prefixEnd_309781 : Nat := 4983230072969 + 3 ^ 40 * 309781 * 2
def baseEnd_309781 : Nat := 141392489449384634766977

theorem tailTrace_309781 : CollatzResearch.WordTrace tailWord_309781 prefixEnd_309781 141392489449384634766977 := by
  unfold tailWord_309781
  simp only [CollatzResearch.WordTrace]
  refine ⟨11298641290723818227817197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7532427527149212151878131 11298641290723818227817197)
  ·
    refine ⟨4236990484021431835431449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11298641290723818227817197 4236990484021431835431449)
    ·
      refine ⟨3177742863016073876573587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4236990484021431835431449 3177742863016073876573587)
      ·
        refine ⟨4766614294524110814860381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3177742863016073876573587 4766614294524110814860381)
        ·
          refine ⟨1787480360446541555572643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4766614294524110814860381 1787480360446541555572643)
          ·
            refine ⟨2681220540669812333358965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1787480360446541555572643 2681220540669812333358965)
            ·
              refine ⟨251364425687794906252403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2681220540669812333358965 251364425687794906252403)
              ·
                refine ⟨377046638531692359378605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 251364425687794906252403 377046638531692359378605)
                ·
                  refine ⟨141392489449384634766977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 377046638531692359378605 141392489449384634766977)
                  ·
                    rfl

theorem cell20_309781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 5, 1, 3].length) (baseStart_309781 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_309781 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_309781 prefixEnd_309781 := by exact prefixLift 309781
  have htrace : WordTrace (prefixWord ++ tailWord_309781) baseStart_309781 baseEnd_309781 := by
    simpa [prefixWord, tailWord_309781, baseEnd_309781] using wordTrace_append hprefix tailTrace_309781
  have hstable : (prefixWord ++ tailWord_309781).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309781).length < 2 ^ (prefixWord ++ tailWord_309781).sum := by decide
  have hdescent : baseEnd_309781 < baseStart_309781 := by decide
  rcases family_descends (prefixWord ++ tailWord_309781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309795 : List Nat := [1, 1, 1, 4, 4, 1, 4, 4]
def baseStart_309795 : Nat := 118140960795 + 309795 * 2 ^ 59
def prefixEnd_309795 : Nat := 4983230072969 + 3 ^ 40 * 309795 * 2
def baseEnd_309795 : Nat := 47132959810287602766751

theorem tailTrace_309795 : CollatzResearch.WordTrace tailWord_309795 prefixEnd_309795 47132959810287602766751 := by
  unfold tailWord_309795
  simp only [CollatzResearch.WordTrace]
  refine ⟨11299151912673098618826839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7532767941782065745884559 11299151912673098618826839)
  ·
    refine ⟨16948727869009647928240259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11299151912673098618826839 16948727869009647928240259)
    ·
      refine ⟨25423091803514471892360389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16948727869009647928240259 25423091803514471892360389)
      ·
        refine ⟨4766829713158963479817573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25423091803514471892360389 4766829713158963479817573)
        ·
          refine ⟨893780571217305652465795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4766829713158963479817573 893780571217305652465795)
          ·
            refine ⟨1340670856825958478698693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 893780571217305652465795 1340670856825958478698693)
            ·
              refine ⟨251375785654867214756005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1340670856825958478698693 251375785654867214756005)
              ·
                refine ⟨47132959810287602766751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 251375785654867214756005 47132959810287602766751)
                ·
                  rfl

theorem cell20_309795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 4, 4].length) (baseStart_309795 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_309795 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_309795 prefixEnd_309795 := by exact prefixLift 309795
  have htrace : WordTrace (prefixWord ++ tailWord_309795) baseStart_309795 baseEnd_309795 := by
    simpa [prefixWord, tailWord_309795, baseEnd_309795] using wordTrace_append hprefix tailTrace_309795
  have hstable : (prefixWord ++ tailWord_309795).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309795).length < 2 ^ (prefixWord ++ tailWord_309795).sum := by decide
  have hdescent : baseEnd_309795 < baseStart_309795 := by decide
  rcases family_descends (prefixWord ++ tailWord_309795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309802 : List Nat := [3, 1, 4, 1, 1, 2, 1, 2, 5]
def baseStart_309802 : Nat := 118140960795 + 309802 * 2 ^ 59
def prefixEnd_309802 : Nat := 4983230072969 + 3 ^ 40 * 309802 * 2
def baseEnd_309802 : Nat := 141402074421601895066891

theorem tailTrace_309802 : CollatzResearch.WordTrace tailWord_309802 prefixEnd_309802 141402074421601895066891 := by
  unfold tailWord_309802
  simp only [CollatzResearch.WordTrace]
  refine ⟨2824851805911934703582915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7532938149098492542887773 2824851805911934703582915)
  ·
    refine ⟨4237277708867902055374373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2824851805911934703582915 4237277708867902055374373)
    ·
      refine ⟨794489570412731635382695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4237277708867902055374373 794489570412731635382695)
      ·
        refine ⟨1191734355619097453074043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 794489570412731635382695 1191734355619097453074043)
        ·
          refine ⟨1787601533428646179611065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1191734355619097453074043 1787601533428646179611065)
          ·
            refine ⟨1340701150071484634708299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1787601533428646179611065 1340701150071484634708299)
            ·
              refine ⟨2011051725107226952062449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1340701150071484634708299 2011051725107226952062449)
              ·
                refine ⟨1508288793830420214046837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2011051725107226952062449 1508288793830420214046837)
                ·
                  refine ⟨141402074421601895066891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1508288793830420214046837 141402074421601895066891)
                  ·
                    rfl

theorem cell20_309802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 2, 5].length) (baseStart_309802 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_309802 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_309802 prefixEnd_309802 := by exact prefixLift 309802
  have htrace : WordTrace (prefixWord ++ tailWord_309802) baseStart_309802 baseEnd_309802 := by
    simpa [prefixWord, tailWord_309802, baseEnd_309802] using wordTrace_append hprefix tailTrace_309802
  have hstable : (prefixWord ++ tailWord_309802).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309802).length < 2 ^ (prefixWord ++ tailWord_309802).sum := by decide
  have hdescent : baseEnd_309802 < baseStart_309802 := by decide
  rcases family_descends (prefixWord ++ tailWord_309802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309822 : List Nat := [4, 2, 1, 4, 1, 2, 1, 1, 4]
def baseStart_309822 : Nat := 118140960795 + 309822 * 2 ^ 59
def prefixEnd_309822 : Nat := 4983230072969 + 3 ^ 40 * 309822 * 2
def baseEnd_309822 : Nat := 141411202966570714400143

theorem tailTrace_309822 : CollatzResearch.WordTrace tailWord_309822 prefixEnd_309822 141411202966570714400143 := by
  unfold tailWord_309822
  simp only [CollatzResearch.WordTrace]
  refine ⟨1412517085446910278757465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7533424455716854820039813 1412517085446910278757465)
  ·
    refine ⟨1059387814085182709068099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1412517085446910278757465 1059387814085182709068099)
    ·
      refine ⟨1589081721127774063602149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1059387814085182709068099 1589081721127774063602149)
      ·
        refine ⟨297952822711457636925403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1589081721127774063602149 297952822711457636925403)
        ·
          refine ⟨446929234067186455388105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 297952822711457636925403 446929234067186455388105)
          ·
            refine ⟨335196925550389841541079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 446929234067186455388105 335196925550389841541079)
            ·
              refine ⟨502795388325584762311619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 335196925550389841541079 502795388325584762311619)
              ·
                refine ⟨754193082488377143467429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 502795388325584762311619 754193082488377143467429)
                ·
                  refine ⟨141411202966570714400143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 754193082488377143467429 141411202966570714400143)
                  ·
                    rfl

theorem cell20_309822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 1, 1, 4].length) (baseStart_309822 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_309822 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_309822 prefixEnd_309822 := by exact prefixLift 309822
  have htrace : WordTrace (prefixWord ++ tailWord_309822) baseStart_309822 baseEnd_309822 := by
    simpa [prefixWord, tailWord_309822, baseEnd_309822] using wordTrace_append hprefix tailTrace_309822
  have hstable : (prefixWord ++ tailWord_309822).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309822).length < 2 ^ (prefixWord ++ tailWord_309822).sum := by decide
  have hdescent : baseEnd_309822 < baseStart_309822 := by decide
  rcases family_descends (prefixWord ++ tailWord_309822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309823 : List Nat := [1, 1, 2, 2, 3, 2, 1, 3, 5]
def baseStart_309823 : Nat := 118140960795 + 309823 * 2 ^ 59
def prefixEnd_309823 : Nat := 4983230072969 + 3 ^ 40 * 309823 * 2
def baseEnd_309823 : Nat := 141411659393819155366805

theorem tailTrace_309823 : CollatzResearch.WordTrace tailWord_309823 prefixEnd_309823 141411659393819155366805 := by
  unfold tailWord_309823
  simp only [CollatzResearch.WordTrace]
  refine ⟨11300173156571659400846123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7533448771047772933897415 11300173156571659400846123)
  ·
    refine ⟨16950259734857489101269185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11300173156571659400846123 16950259734857489101269185)
    ·
      refine ⟨12712694801143116825951889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16950259734857489101269185 12712694801143116825951889)
      ·
        refine ⟨9534521100857337619463917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12712694801143116825951889 9534521100857337619463917)
        ·
          refine ⟨3575445412821501607298969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9534521100857337619463917 3575445412821501607298969)
          ·
            refine ⟨2681584059616126205474227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3575445412821501607298969 2681584059616126205474227)
            ·
              refine ⟨4022376089424189308211341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2681584059616126205474227 4022376089424189308211341)
              ·
                refine ⟨1508391033534070990579253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4022376089424189308211341 1508391033534070990579253)
                ·
                  refine ⟨141411659393819155366805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1508391033534070990579253 141411659393819155366805)
                  ·
                    rfl

theorem cell20_309823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 3, 5].length) (baseStart_309823 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_309823 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_309823 prefixEnd_309823 := by exact prefixLift 309823
  have htrace : WordTrace (prefixWord ++ tailWord_309823) baseStart_309823 baseEnd_309823 := by
    simpa [prefixWord, tailWord_309823, baseEnd_309823] using wordTrace_append hprefix tailTrace_309823
  have hstable : (prefixWord ++ tailWord_309823).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309823).length < 2 ^ (prefixWord ++ tailWord_309823).sum := by decide
  have hdescent : baseEnd_309823 < baseStart_309823 := by decide
  rcases family_descends (prefixWord ++ tailWord_309823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309877 : List Nat := [1, 3, 4, 2, 2, 2, 2, 2, 2]
def baseStart_309877 : Nat := 118140960795 + 309877 * 2 ^ 59
def prefixEnd_309877 : Nat := 4983230072969 + 3 ^ 40 * 309877 * 2
def baseEnd_309877 : Nat := 141436306465234967566585

theorem tailTrace_309877 : CollatzResearch.WordTrace tailWord_309877 prefixEnd_309877 141436306465234967566585 := by
  unfold tailWord_309877
  simp only [CollatzResearch.WordTrace]
  refine ⟨11302142698376026623311885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7534761798917351082207923 11302142698376026623311885)
  ·
    refine ⟨4238303511891009983741957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11302142698376026623311885 4238303511891009983741957)
    ·
      refine ⟨794681908479564371951617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4238303511891009983741957 794681908479564371951617)
      ·
        refine ⟨596011431359673278963713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 794681908479564371951617 596011431359673278963713)
        ·
          refine ⟨447008573519754959222785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 596011431359673278963713 447008573519754959222785)
          ·
            refine ⟨335256430139816219417089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 447008573519754959222785 335256430139816219417089)
            ·
              refine ⟨251442322604862164562817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 335256430139816219417089 251442322604862164562817)
              ·
                refine ⟨188581741953646623422113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 251442322604862164562817 188581741953646623422113)
                ·
                  refine ⟨141436306465234967566585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 188581741953646623422113 141436306465234967566585)
                  ·
                    rfl

theorem cell20_309877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 2, 2, 2].length) (baseStart_309877 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_309877 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_309877 prefixEnd_309877 := by exact prefixLift 309877
  have htrace : WordTrace (prefixWord ++ tailWord_309877) baseStart_309877 baseEnd_309877 := by
    simpa [prefixWord, tailWord_309877, baseEnd_309877] using wordTrace_append hprefix tailTrace_309877
  have hstable : (prefixWord ++ tailWord_309877).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309877).length < 2 ^ (prefixWord ++ tailWord_309877).sum := by decide
  have hdescent : baseEnd_309877 < baseStart_309877 := by decide
  rcases family_descends (prefixWord ++ tailWord_309877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309881 : List Nat := [1, 2, 1, 3, 3, 2, 4, 2, 2]
def baseStart_309881 : Nat := 118140960795 + 309881 * 2 ^ 59
def prefixEnd_309881 : Nat := 4983230072969 + 3 ^ 40 * 309881 * 2
def baseEnd_309881 : Nat := 141438132174228731433235

theorem tailTrace_309881 : CollatzResearch.WordTrace tailWord_309881 prefixEnd_309881 141438132174228731433235 := by
  unfold tailWord_309881
  simp only [CollatzResearch.WordTrace]
  refine ⟨11302288590361535306457497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7534859060241023537638331 11302288590361535306457497)
  ·
    refine ⟨8476716442771151479843123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11302288590361535306457497 8476716442771151479843123)
    ·
      refine ⟨12715074664156727219764685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8476716442771151479843123 12715074664156727219764685)
      ·
        refine ⟨4768152999058772707411757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12715074664156727219764685 4768152999058772707411757)
        ·
          refine ⟨1788057374647039765279409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4768152999058772707411757 1788057374647039765279409)
          ·
            refine ⟨1341043030985279823959557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1788057374647039765279409 1341043030985279823959557)
            ·
              refine ⟨251445568309739966992417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1341043030985279823959557 251445568309739966992417)
              ·
                refine ⟨188584176232304975244313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 251445568309739966992417 188584176232304975244313)
                ·
                  refine ⟨141438132174228731433235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 188584176232304975244313 141438132174228731433235)
                  ·
                    rfl

theorem cell20_309881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 4, 2, 2].length) (baseStart_309881 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_309881 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_309881 prefixEnd_309881 := by exact prefixLift 309881
  have htrace : WordTrace (prefixWord ++ tailWord_309881) baseStart_309881 baseEnd_309881 := by
    simpa [prefixWord, tailWord_309881, baseEnd_309881] using wordTrace_append hprefix tailTrace_309881
  have hstable : (prefixWord ++ tailWord_309881).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309881).length < 2 ^ (prefixWord ++ tailWord_309881).sum := by decide
  have hdescent : baseEnd_309881 < baseStart_309881 := by decide
  rcases family_descends (prefixWord ++ tailWord_309881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309933 : List Nat := [1, 5, 2, 1, 1, 2, 3, 2, 3]
def baseStart_309933 : Nat := 118140960795 + 309933 * 2 ^ 59
def prefixEnd_309933 : Nat := 4983230072969 + 3 ^ 40 * 309933 * 2
def baseEnd_309933 : Nat := 141461866391147661699689

theorem tailTrace_309933 : CollatzResearch.WordTrace tailWord_309933 prefixEnd_309933 141461866391147661699689 := by
  unfold tailWord_309933
  simp only [CollatzResearch.WordTrace]
  refine ⟨11304185186173148187350453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7536123457448765458233635 11304185186173148187350453)
  ·
    refine ⟨1059767361203732642564105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11304185186173148187350453 1059767361203732642564105)
    ·
      refine ⟨794825520902799481923079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1059767361203732642564105 794825520902799481923079)
      ·
        refine ⟨1192238281354199222884619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 794825520902799481923079 1192238281354199222884619)
        ·
          refine ⟨1788357422031298834326929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1192238281354199222884619 1788357422031298834326929)
          ·
            refine ⟨1341268066523474125745197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1788357422031298834326929 1341268066523474125745197)
            ·
              refine ⟨502975524946302797154449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1341268066523474125745197 502975524946302797154449)
              ·
                refine ⟨377231643709727097865837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 502975524946302797154449 377231643709727097865837)
                ·
                  refine ⟨141461866391147661699689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 377231643709727097865837 141461866391147661699689)
                  ·
                    rfl

theorem cell20_309933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 3, 2, 3].length) (baseStart_309933 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_309933 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_309933 prefixEnd_309933 := by exact prefixLift 309933
  have htrace : WordTrace (prefixWord ++ tailWord_309933) baseStart_309933 baseEnd_309933 := by
    simpa [prefixWord, tailWord_309933, baseEnd_309933] using wordTrace_append hprefix tailTrace_309933
  have hstable : (prefixWord ++ tailWord_309933).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309933).length < 2 ^ (prefixWord ++ tailWord_309933).sum := by decide
  have hdescent : baseEnd_309933 < baseStart_309933 := by decide
  rcases family_descends (prefixWord ++ tailWord_309933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309964 : List Nat := [2, 2, 1, 5, 1, 3, 2, 4]
def baseStart_309964 : Nat := 118140960795 + 309964 * 2 ^ 59
def prefixEnd_309964 : Nat := 4983230072969 + 3 ^ 40 * 309964 * 2
def baseEnd_309964 : Nat := 47158671878616443888743

theorem tailTrace_309964 : CollatzResearch.WordTrace tailWord_309964 prefixEnd_309964 47158671878616443888743 := by
  unfold tailWord_309964
  simp only [CollatzResearch.WordTrace]
  refine ⟨5652657924530420240864473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7536877232707226987819297 5652657924530420240864473)
  ·
    refine ⟨4239493443397815180648355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5652657924530420240864473 4239493443397815180648355)
    ·
      refine ⟨6359240165096722770972533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4239493443397815180648355 6359240165096722770972533)
      ·
        refine ⟨596178765477817759778675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6359240165096722770972533 596178765477817759778675)
        ·
          refine ⟨894268148216726639668013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 596178765477817759778675 894268148216726639668013)
          ·
            refine ⟨335350555581272489875505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 894268148216726639668013 335350555581272489875505)
            ·
              refine ⟨251512916685954367406629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 335350555581272489875505 251512916685954367406629)
              ·
                refine ⟨47158671878616443888743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 251512916685954367406629 47158671878616443888743)
                ·
                  rfl

theorem cell20_309964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 2, 4].length) (baseStart_309964 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_309964 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_309964 prefixEnd_309964 := by exact prefixLift 309964
  have htrace : WordTrace (prefixWord ++ tailWord_309964) baseStart_309964 baseEnd_309964 := by
    simpa [prefixWord, tailWord_309964, baseEnd_309964] using wordTrace_append hprefix tailTrace_309964
  have hstable : (prefixWord ++ tailWord_309964).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309964).length < 2 ^ (prefixWord ++ tailWord_309964).sum := by decide
  have hdescent : baseEnd_309964 < baseStart_309964 := by decide
  rcases family_descends (prefixWord ++ tailWord_309964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309975 : List Nat := [1, 1, 3, 2, 1, 4, 1, 2, 5]
def baseStart_309975 : Nat := 118140960795 + 309975 * 2 ^ 59
def prefixEnd_309975 : Nat := 4983230072969 + 3 ^ 40 * 309975 * 2
def baseEnd_309975 : Nat := 141481036335582182299517

theorem tailTrace_309975 : CollatzResearch.WordTrace tailWord_309975 prefixEnd_309975 141481036335582182299517 := by
  unfold tailWord_309975
  simp only [CollatzResearch.WordTrace]
  refine ⟨11305717052020989360379379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7537144701347326240252919 11305717052020989360379379)
  ·
    refine ⟨16958575578031484040569069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11305717052020989360379379 16958575578031484040569069)
    ·
      refine ⟨6359465841761806515213401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16958575578031484040569069 6359465841761806515213401)
      ·
        refine ⟨4769599381321354886410051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6359465841761806515213401 4769599381321354886410051)
        ·
          refine ⟨7154399071982032329615077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4769599381321354886410051 7154399071982032329615077)
          ·
            refine ⟨1341449825996631061802827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7154399071982032329615077 1341449825996631061802827)
            ·
              refine ⟨2012174738994946592704241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1341449825996631061802827 2012174738994946592704241)
              ·
                refine ⟨1509131054246209944528181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2012174738994946592704241 1509131054246209944528181)
                ·
                  refine ⟨141481036335582182299517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1509131054246209944528181 141481036335582182299517)
                  ·
                    rfl

theorem cell20_309975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 2, 5].length) (baseStart_309975 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_309975 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_309975 prefixEnd_309975 := by exact prefixLift 309975
  have htrace : WordTrace (prefixWord ++ tailWord_309975) baseStart_309975 baseEnd_309975 := by
    simpa [prefixWord, tailWord_309975, baseEnd_309975] using wordTrace_append hprefix tailTrace_309975
  have hstable : (prefixWord ++ tailWord_309975).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309975).length < 2 ^ (prefixWord ++ tailWord_309975).sum := by decide
  have hdescent : baseEnd_309975 < baseStart_309975 := by decide
  rcases family_descends (prefixWord ++ tailWord_309975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_309999 : List Nat := [1, 1, 2, 1, 5, 2, 3, 1, 4]
def baseStart_309999 : Nat := 118140960795 + 309999 * 2 ^ 59
def prefixEnd_309999 : Nat := 4983230072969 + 3 ^ 40 * 309999 * 2
def baseEnd_309999 : Nat := 141491990589544765499419

theorem tailTrace_309999 : CollatzResearch.WordTrace tailWord_309999 prefixEnd_309999 141491990589544765499419 := by
  unfold tailWord_309999
  simp only [CollatzResearch.WordTrace]
  refine ⟨11306592403934041459253051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7537728269289360972835367 11306592403934041459253051)
  ·
    refine ⟨16959888605901062188879577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11306592403934041459253051 16959888605901062188879577)
    ·
      refine ⟨12719916454425796641659683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16959888605901062188879577 12719916454425796641659683)
      ·
        refine ⟨19079874681638694962489525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12719916454425796641659683 19079874681638694962489525)
        ·
          refine ⟨1788738251403627652733393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19079874681638694962489525 1788738251403627652733393)
          ·
            refine ⟨1341553688552720739550045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1788738251403627652733393 1341553688552720739550045)
            ·
              refine ⟨503082633207270277331267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1341553688552720739550045 503082633207270277331267)
              ·
                refine ⟨754623949810905415996901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 503082633207270277331267 754623949810905415996901)
                ·
                  refine ⟨141491990589544765499419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 754623949810905415996901 141491990589544765499419)
                  ·
                    rfl

theorem cell20_309999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 3, 1, 4].length) (baseStart_309999 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_309999 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_309999 prefixEnd_309999 := by exact prefixLift 309999
  have htrace : WordTrace (prefixWord ++ tailWord_309999) baseStart_309999 baseEnd_309999 := by
    simpa [prefixWord, tailWord_309999, baseEnd_309999] using wordTrace_append hprefix tailTrace_309999
  have hstable : (prefixWord ++ tailWord_309999).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_309999).length < 2 ^ (prefixWord ++ tailWord_309999).sum := by decide
  have hdescent : baseEnd_309999 < baseStart_309999 := by decide
  rcases family_descends (prefixWord ++ tailWord_309999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310005 : List Nat := [1, 3, 6, 1, 1, 1, 1, 3, 3]
def baseStart_310005 : Nat := 118140960795 + 310005 * 2 ^ 59
def prefixEnd_310005 : Nat := 4983230072969 + 3 ^ 40 * 310005 * 2
def baseEnd_310005 : Nat := 141494729153035411299395

theorem tailTrace_310005 : CollatzResearch.WordTrace tailWord_310005 prefixEnd_310005 141494729153035411299395 := by
  unfold tailWord_310005
  simp only [CollatzResearch.WordTrace]
  refine ⟨11306811241912304483971469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7537874161274869655980979 11306811241912304483971469)
  ·
    refine ⟨4240054215717114181489301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11306811241912304483971469 4240054215717114181489301)
    ·
      refine ⟨198752541361739727257311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 4240054215717114181489301 198752541361739727257311)
      ·
        refine ⟨298128812042609590885967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198752541361739727257311 298128812042609590885967)
        ·
          refine ⟨447193218063914386328951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 298128812042609590885967 447193218063914386328951)
          ·
            refine ⟨670789827095871579493427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 447193218063914386328951 670789827095871579493427)
            ·
              refine ⟨1006184740643807369240141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 670789827095871579493427 1006184740643807369240141)
              ·
                refine ⟨377319277741427763465053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1006184740643807369240141 377319277741427763465053)
                ·
                  refine ⟨141494729153035411299395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 377319277741427763465053 141494729153035411299395)
                  ·
                    rfl

theorem cell20_310005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 3, 3].length) (baseStart_310005 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_310005 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_310005 prefixEnd_310005 := by exact prefixLift 310005
  have htrace : WordTrace (prefixWord ++ tailWord_310005) baseStart_310005 baseEnd_310005 := by
    simpa [prefixWord, tailWord_310005, baseEnd_310005] using wordTrace_append hprefix tailTrace_310005
  have hstable : (prefixWord ++ tailWord_310005).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310005).length < 2 ^ (prefixWord ++ tailWord_310005).sum := by decide
  have hdescent : baseEnd_310005 < baseStart_310005 := by decide
  rcases family_descends (prefixWord ++ tailWord_310005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310050 : List Nat := [3, 3, 1, 1, 2, 4, 2, 2, 2]
def baseStart_310050 : Nat := 118140960795 + 310050 * 2 ^ 59
def prefixEnd_310050 : Nat := 4983230072969 + 3 ^ 40 * 310050 * 2
def baseEnd_310050 : Nat := 141515268379215254799211

theorem tailTrace_310050 : CollatzResearch.WordTrace tailWord_310050 prefixEnd_310050 141515268379215254799211 := by
  unfold tailWord_310050
  simp only [CollatzResearch.WordTrace]
  refine ⟨2827113131687319292339901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7538968351166184779573069 2827113131687319292339901)
  ·
    refine ⟨1060167424382744734627463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2827113131687319292339901 1060167424382744734627463)
    ·
      refine ⟨1590251136574117101941195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1060167424382744734627463 1590251136574117101941195)
      ·
        refine ⟨2385376704861175652911793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1590251136574117101941195 2385376704861175652911793)
        ·
          refine ⟨1789032528645881739683845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2385376704861175652911793 1789032528645881739683845)
          ·
            refine ⟨335443599121102826190721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1789032528645881739683845 335443599121102826190721)
            ·
              refine ⟨251582699340827119643041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 335443599121102826190721 251582699340827119643041)
              ·
                refine ⟨188687024505620339732281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 251582699340827119643041 188687024505620339732281)
                ·
                  refine ⟨141515268379215254799211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 188687024505620339732281 141515268379215254799211)
                  ·
                    rfl

theorem cell20_310050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 2, 2, 2].length) (baseStart_310050 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_310050 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_310050 prefixEnd_310050 := by exact prefixLift 310050
  have htrace : WordTrace (prefixWord ++ tailWord_310050) baseStart_310050 baseEnd_310050 := by
    simpa [prefixWord, tailWord_310050, baseEnd_310050] using wordTrace_append hprefix tailTrace_310050
  have hstable : (prefixWord ++ tailWord_310050).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310050).length < 2 ^ (prefixWord ++ tailWord_310050).sum := by decide
  have hdescent : baseEnd_310050 < baseStart_310050 := by decide
  rcases family_descends (prefixWord ++ tailWord_310050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310078 : List Nat := [4, 2, 1, 2, 3, 1, 3, 4]
def baseStart_310078 : Nat := 118140960795 + 310078 * 2 ^ 59
def prefixEnd_310078 : Nat := 4983230072969 + 3 ^ 40 * 310078 * 2
def baseEnd_310078 : Nat := 47176016114057200621921

theorem tailTrace_310078 : CollatzResearch.WordTrace tailWord_310078 prefixEnd_310078 47176016114057200621921 := by
  unfold tailWord_310078
  simp only [CollatzResearch.WordTrace]
  refine ⟨1413684221330979743922361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7539649180431891967585925 1413684221330979743922361)
  ·
    refine ⟨1060263165998234807941771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1413684221330979743922361 1060263165998234807941771)
    ·
      refine ⟨1590394748997352211912657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1060263165998234807941771 1590394748997352211912657)
      ·
        refine ⟨1192796061748014158934493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1590394748997352211912657 1192796061748014158934493)
        ·
          refine ⟨447298523155505309600435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1192796061748014158934493 447298523155505309600435)
          ·
            refine ⟨670947784733257964400653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 447298523155505309600435 670947784733257964400653)
            ·
              refine ⟨251605419274971736650245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 670947784733257964400653 251605419274971736650245)
              ·
                refine ⟨47176016114057200621921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 251605419274971736650245 47176016114057200621921)
                ·
                  rfl

theorem cell20_310078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 3, 4].length) (baseStart_310078 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_310078 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_310078 prefixEnd_310078 := by exact prefixLift 310078
  have htrace : WordTrace (prefixWord ++ tailWord_310078) baseStart_310078 baseEnd_310078 := by
    simpa [prefixWord, tailWord_310078, baseEnd_310078] using wordTrace_append hprefix tailTrace_310078
  have hstable : (prefixWord ++ tailWord_310078).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310078).length < 2 ^ (prefixWord ++ tailWord_310078).sum := by decide
  have hdescent : baseEnd_310078 < baseStart_310078 := by decide
  rcases family_descends (prefixWord ++ tailWord_310078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310092 : List Nat := [2, 2, 1, 3, 3, 1, 1, 5, 2]
def baseStart_310092 : Nat := 118140960795 + 310092 * 2 ^ 59
def prefixEnd_310092 : Nat := 4983230072969 + 3 ^ 40 * 310092 * 2
def baseEnd_310092 : Nat := 141534438323649775399039

theorem tailTrace_310092 : CollatzResearch.WordTrace tailWord_310092 prefixEnd_310092 141534438323649775399039 := by
  unfold tailWord_310092
  simp only [CollatzResearch.WordTrace]
  refine ⟨5654992196298559171194265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7539989595064745561592353 5654992196298559171194265)
  ·
    refine ⟨4241244147223919378395699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5654992196298559171194265 4241244147223919378395699)
    ·
      refine ⟨6361866220835879067593549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4241244147223919378395699 6361866220835879067593549)
      ·
        refine ⟨2385699832813454650347581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6361866220835879067593549 2385699832813454650347581)
        ·
          refine ⟨894637437305045493880343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2385699832813454650347581 894637437305045493880343)
          ·
            refine ⟨1341956155957568240820515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 894637437305045493880343 1341956155957568240820515)
            ·
              refine ⟨2012934233936352361230773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1341956155957568240820515 2012934233936352361230773)
              ·
                refine ⟨188712584431533033865385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2012934233936352361230773 188712584431533033865385)
                ·
                  refine ⟨141534438323649775399039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 188712584431533033865385 141534438323649775399039)
                  ·
                    rfl

theorem cell20_310092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 5, 2].length) (baseStart_310092 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_310092 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_310092 prefixEnd_310092 := by exact prefixLift 310092
  have htrace : WordTrace (prefixWord ++ tailWord_310092) baseStart_310092 baseEnd_310092 := by
    simpa [prefixWord, tailWord_310092, baseEnd_310092] using wordTrace_append hprefix tailTrace_310092
  have hstable : (prefixWord ++ tailWord_310092).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310092).length < 2 ^ (prefixWord ++ tailWord_310092).sum := by decide
  have hdescent : baseEnd_310092 < baseStart_310092 := by decide
  rcases family_descends (prefixWord ++ tailWord_310092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310106 : List Nat := [3, 1, 1, 2, 1, 4, 3, 2, 3]
def baseStart_310106 : Nat := 118140960795 + 310106 * 2 ^ 59
def prefixEnd_310106 : Nat := 4983230072969 + 3 ^ 40 * 310106 * 2
def baseEnd_310106 : Nat := 141540828305127948932315

theorem tailTrace_310106 : CollatzResearch.WordTrace tailWord_310106 prefixEnd_310106 141540828305127948932315 := by
  unfold tailWord_310106
  simp only [CollatzResearch.WordTrace]
  refine ⟨2827623753636599683349543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7540330009697599155598781 2827623753636599683349543)
  ·
    refine ⟨4241435630454899525024315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2827623753636599683349543 4241435630454899525024315)
    ·
      refine ⟨6362153445682349287536473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4241435630454899525024315 6362153445682349287536473)
      ·
        refine ⟨4771615084261761965652355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6362153445682349287536473 4771615084261761965652355)
        ·
          refine ⟨7157422626392642948478533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4771615084261761965652355 7157422626392642948478533)
          ·
            refine ⟨1342016742448620552839725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7157422626392642948478533 1342016742448620552839725)
            ·
              refine ⟨503256278418232707314897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1342016742448620552839725 503256278418232707314897)
              ·
                refine ⟨377442208813674530486173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 503256278418232707314897 377442208813674530486173)
                ·
                  refine ⟨141540828305127948932315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 377442208813674530486173 141540828305127948932315)
                  ·
                    rfl

theorem cell20_310106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 3, 2, 3].length) (baseStart_310106 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_310106 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_310106 prefixEnd_310106 := by exact prefixLift 310106
  have htrace : WordTrace (prefixWord ++ tailWord_310106) baseStart_310106 baseEnd_310106 := by
    simpa [prefixWord, tailWord_310106, baseEnd_310106] using wordTrace_append hprefix tailTrace_310106
  have hstable : (prefixWord ++ tailWord_310106).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310106).length < 2 ^ (prefixWord ++ tailWord_310106).sum := by decide
  have hdescent : baseEnd_310106 < baseStart_310106 := by decide
  rcases family_descends (prefixWord ++ tailWord_310106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310127 : List Nat := [1, 1, 2, 1, 3, 1, 1, 7, 3]
def baseStart_310127 : Nat := 118140960795 + 310127 * 2 ^ 59
def prefixEnd_310127 : Nat := 4983230072969 + 3 ^ 40 * 310127 * 2
def baseEnd_310127 : Nat := 141550413277345209232229

theorem tailTrace_310127 : CollatzResearch.WordTrace tailWord_310127 prefixEnd_310127 141550413277345209232229 := by
  unfold tailWord_310127
  simp only [CollatzResearch.WordTrace]
  refine ⟨11311260947470319319912635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7540840631646879546608423 11311260947470319319912635)
  ·
    refine ⟨16966891421205478979868953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11311260947470319319912635 16966891421205478979868953)
    ·
      refine ⟨12725168565904109234901715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16966891421205478979868953 12725168565904109234901715)
      ·
        refine ⟨19087752848856163852352573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12725168565904109234901715 19087752848856163852352573)
        ·
          refine ⟨7157907318321061444632215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19087752848856163852352573 7157907318321061444632215)
          ·
            refine ⟨10736860977481592166948323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7157907318321061444632215 10736860977481592166948323)
            ·
              refine ⟨16105291466222388250422485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10736860977481592166948323 16105291466222388250422485)
              ·
                refine ⟨377467768739587224619277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 16105291466222388250422485 377467768739587224619277)
                ·
                  refine ⟨141550413277345209232229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 377467768739587224619277 141550413277345209232229)
                  ·
                    rfl

theorem cell20_310127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 7, 3].length) (baseStart_310127 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_310127 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_310127 prefixEnd_310127 := by exact prefixLift 310127
  have htrace : WordTrace (prefixWord ++ tailWord_310127) baseStart_310127 baseEnd_310127 := by
    simpa [prefixWord, tailWord_310127, baseEnd_310127] using wordTrace_append hprefix tailTrace_310127
  have hstable : (prefixWord ++ tailWord_310127).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310127).length < 2 ^ (prefixWord ++ tailWord_310127).sum := by decide
  have hdescent : baseEnd_310127 < baseStart_310127 := by decide
  rcases family_descends (prefixWord ++ tailWord_310127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310137 : List Nat := [1, 2, 1, 3, 2, 5, 2, 4]
def baseStart_310137 : Nat := 118140960795 + 310137 * 2 ^ 59
def prefixEnd_310137 : Nat := 4983230072969 + 3 ^ 40 * 310137 * 2
def baseEnd_310137 : Nat := 47184992516609872966285

theorem tailTrace_310137 : CollatzResearch.WordTrace tailWord_310137 prefixEnd_310137 47184992516609872966285 := by
  unfold tailWord_310137
  simp only [CollatzResearch.WordTrace]
  refine ⟨11311625677434091027776665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7541083784956060685184443 11311625677434091027776665)
  ·
    refine ⟨8483719258075568270832499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11311625677434091027776665 8483719258075568270832499)
    ·
      refine ⟨12725578887113352406248749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8483719258075568270832499 12725578887113352406248749)
      ·
        refine ⟨4772092082667507152343281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12725578887113352406248749 4772092082667507152343281)
        ·
          refine ⟨3579069062000630364257461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4772092082667507152343281 3579069062000630364257461)
          ·
            refine ⟨335537724562559096649137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3579069062000630364257461 335537724562559096649137)
            ·
              refine ⟨251653293421919322486853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 335537724562559096649137 251653293421919322486853)
              ·
                refine ⟨47184992516609872966285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 251653293421919322486853 47184992516609872966285)
                ·
                  rfl

theorem cell20_310137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 2, 4].length) (baseStart_310137 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_310137 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_310137 prefixEnd_310137 := by exact prefixLift 310137
  have htrace : WordTrace (prefixWord ++ tailWord_310137) baseStart_310137 baseEnd_310137 := by
    simpa [prefixWord, tailWord_310137, baseEnd_310137] using wordTrace_append hprefix tailTrace_310137
  have hstable : (prefixWord ++ tailWord_310137).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310137).length < 2 ^ (prefixWord ++ tailWord_310137).sum := by decide
  have hdescent : baseEnd_310137 < baseStart_310137 := by decide
  rcases family_descends (prefixWord ++ tailWord_310137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310165 : List Nat := [1, 3, 2, 1, 1, 4, 2, 1, 5]
def baseStart_310165 : Nat := 118140960795 + 310165 * 2 ^ 59
def prefixEnd_310165 : Nat := 4983230072969 + 3 ^ 40 * 310165 * 2
def baseEnd_310165 : Nat := 141567757512785965965407

theorem tailTrace_310165 : CollatzResearch.WordTrace tailWord_310165 prefixEnd_310165 141567757512785965965407 := by
  unfold tailWord_310165
  simp only [CollatzResearch.WordTrace]
  refine ⟨11312646921332651809795949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7541764614221767873197299 11312646921332651809795949)
  ·
    refine ⟨4242242595499744428673481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11312646921332651809795949 4242242595499744428673481)
    ·
      refine ⟨3181681946624808321505111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4242242595499744428673481 3181681946624808321505111)
      ·
        refine ⟨4772522919937212482257667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3181681946624808321505111 4772522919937212482257667)
        ·
          refine ⟨7158784379905818723386501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4772522919937212482257667 7158784379905818723386501)
          ·
            refine ⟨1342272071232341010634969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7158784379905818723386501 1342272071232341010634969)
            ·
              refine ⟨1006704053424255757976227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1342272071232341010634969 1006704053424255757976227)
              ·
                refine ⟨1510056080136383636964341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1006704053424255757976227 1510056080136383636964341)
                ·
                  refine ⟨141567757512785965965407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1510056080136383636964341 141567757512785965965407)
                  ·
                    rfl

theorem cell20_310165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 1, 5].length) (baseStart_310165 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_310165 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_310165 prefixEnd_310165 := by exact prefixLift 310165
  have htrace : WordTrace (prefixWord ++ tailWord_310165) baseStart_310165 baseEnd_310165 := by
    simpa [prefixWord, tailWord_310165, baseEnd_310165] using wordTrace_append hprefix tailTrace_310165
  have hstable : (prefixWord ++ tailWord_310165).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310165).length < 2 ^ (prefixWord ++ tailWord_310165).sum := by decide
  have hdescent : baseEnd_310165 < baseStart_310165 := by decide
  rcases family_descends (prefixWord ++ tailWord_310165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310178 : List Nat := [3, 3, 1, 2, 2, 3, 2, 1, 3]
def baseStart_310178 : Nat := 118140960795 + 310178 * 2 ^ 59
def prefixEnd_310178 : Nat := 4983230072969 + 3 ^ 40 * 310178 * 2
def baseEnd_310178 : Nat := 141573691067015698532021

theorem tailTrace_310178 : CollatzResearch.WordTrace tailWord_310178 prefixEnd_310178 141573691067015698532021 := by
  unfold tailWord_310178
  simp only [CollatzResearch.WordTrace]
  refine ⟨2828280267571388757504797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7542080713523703353346125 2828280267571388757504797)
  ·
    refine ⟨1060605100339270784064299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2828280267571388757504797 1060605100339270784064299)
    ·
      refine ⟨1590907650508906176096449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1060605100339270784064299 1590907650508906176096449)
      ·
        refine ⟨1193180737881679632072337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1590907650508906176096449 1193180737881679632072337)
        ·
          refine ⟨894885553411259724054253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1193180737881679632072337 894885553411259724054253)
          ·
            refine ⟨335582082529222396520345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 894885553411259724054253 335582082529222396520345)
            ·
              refine ⟨251686561896916797390259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 335582082529222396520345 251686561896916797390259)
              ·
                refine ⟨377529842845375196085389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 251686561896916797390259 377529842845375196085389)
                ·
                  refine ⟨141573691067015698532021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 377529842845375196085389 141573691067015698532021)
                  ·
                    rfl

theorem cell20_310178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 2, 1, 3].length) (baseStart_310178 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_310178 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_310178 prefixEnd_310178 := by exact prefixLift 310178
  have htrace : WordTrace (prefixWord ++ tailWord_310178) baseStart_310178 baseEnd_310178 := by
    simpa [prefixWord, tailWord_310178, baseEnd_310178] using wordTrace_append hprefix tailTrace_310178
  have hstable : (prefixWord ++ tailWord_310178).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310178).length < 2 ^ (prefixWord ++ tailWord_310178).sum := by decide
  have hdescent : baseEnd_310178 < baseStart_310178 := by decide
  rcases family_descends (prefixWord ++ tailWord_310178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310179 : List Nat := [1, 1, 1, 4, 1, 2, 3, 7]
def baseStart_310179 : Nat := 118140960795 + 310179 * 2 ^ 59
def prefixEnd_310179 : Nat := 4983230072969 + 3 ^ 40 * 310179 * 2
def baseEnd_310179 : Nat := 47191382498088046499561

theorem tailTrace_310179 : CollatzResearch.WordTrace tailWord_310179 prefixEnd_310179 47191382498088046499561 := by
  unfold tailWord_310179
  simp only [CollatzResearch.WordTrace]
  refine ⟨11313157543281932200805591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7542105028854621467203727 11313157543281932200805591)
  ·
    refine ⟨16969736314922898301208387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11313157543281932200805591 16969736314922898301208387)
    ·
      refine ⟨25454604472384347451812581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16969736314922898301208387 25454604472384347451812581)
      ·
        refine ⟨4772738338572065147214859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25454604472384347451812581 4772738338572065147214859)
        ·
          refine ⟨7159107507858097720822289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4772738338572065147214859 7159107507858097720822289)
          ·
            refine ⟨5369330630893573290616717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7159107507858097720822289 5369330630893573290616717)
            ·
              refine ⟨2013498986585089983981269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5369330630893573290616717 2013498986585089983981269)
              ·
                refine ⟨47191382498088046499561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2013498986585089983981269 47191382498088046499561)
                ·
                  rfl

theorem cell20_310179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 7].length) (baseStart_310179 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_310179 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_310179 prefixEnd_310179 := by exact prefixLift 310179
  have htrace : WordTrace (prefixWord ++ tailWord_310179) baseStart_310179 baseEnd_310179 := by
    simpa [prefixWord, tailWord_310179, baseEnd_310179] using wordTrace_append hprefix tailTrace_310179
  have hstable : (prefixWord ++ tailWord_310179).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310179).length < 2 ^ (prefixWord ++ tailWord_310179).sum := by decide
  have hdescent : baseEnd_310179 < baseStart_310179 := by decide
  rcases family_descends (prefixWord ++ tailWord_310179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310206 : List Nat := [4, 2, 1, 1, 1, 2, 2, 5, 2]
def baseStart_310206 : Nat := 118140960795 + 310206 * 2 ^ 59
def prefixEnd_310206 : Nat := 4983230072969 + 3 ^ 40 * 310206 * 2
def baseEnd_310206 : Nat := 141586471029972045598573

theorem tailTrace_310206 : CollatzResearch.WordTrace tailWord_310206 prefixEnd_310206 141586471029972045598573 := by
  unfold tailWord_310206
  simp only [CollatzResearch.WordTrace]
  refine ⟨1414267789273014476504809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 7542761542789410541358981 1414267789273014476504809)
  ·
    refine ⟨1060700841954760857378607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1414267789273014476504809 1060700841954760857378607)
    ·
      refine ⟨1591051262932141286067911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1060700841954760857378607 1591051262932141286067911)
      ·
        refine ⟨2386576894398211929101867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1591051262932141286067911 2386576894398211929101867)
        ·
          refine ⟨3579865341597317893652801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2386576894398211929101867 3579865341597317893652801)
          ·
            refine ⟨2684899006197988420239601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3579865341597317893652801 2684899006197988420239601)
            ·
              refine ⟨2013674254648491315179701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2684899006197988420239601 2013674254648491315179701)
              ·
                refine ⟨188781961373296060798097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2013674254648491315179701 188781961373296060798097)
                ·
                  refine ⟨141586471029972045598573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 188781961373296060798097 141586471029972045598573)
                  ·
                    rfl

theorem cell20_310206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 5, 2].length) (baseStart_310206 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_310206 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_310206 prefixEnd_310206 := by exact prefixLift 310206
  have htrace : WordTrace (prefixWord ++ tailWord_310206) baseStart_310206 baseEnd_310206 := by
    simpa [prefixWord, tailWord_310206, baseEnd_310206] using wordTrace_append hprefix tailTrace_310206
  have hstable : (prefixWord ++ tailWord_310206).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310206).length < 2 ^ (prefixWord ++ tailWord_310206).sum := by decide
  have hdescent : baseEnd_310206 < baseStart_310206 := by decide
  rcases family_descends (prefixWord ++ tailWord_310206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310220 : List Nat := [2, 2, 1, 4, 1, 1, 4, 2, 3]
def baseStart_310220 : Nat := 118140960795 + 310220 * 2 ^ 59
def prefixEnd_310220 : Nat := 4983230072969 + 3 ^ 40 * 310220 * 2
def baseEnd_310220 : Nat := 141592861011450219131849

theorem tailTrace_310220 : CollatzResearch.WordTrace tailWord_310220 prefixEnd_310220 141592861011450219131849 := by
  unfold tailWord_310220
  simp only [CollatzResearch.WordTrace]
  refine ⟨5657326468066698101524057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7543101957422264135365409 5657326468066698101524057)
  ·
    refine ⟨4242994851050023576143043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5657326468066698101524057 4242994851050023576143043)
    ·
      refine ⟨6364492276575035364214565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4242994851050023576143043 6364492276575035364214565)
      ·
        refine ⟨1193342301857819130790231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6364492276575035364214565 1193342301857819130790231)
        ·
          refine ⟨1790013452786728696185347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1193342301857819130790231 1790013452786728696185347)
          ·
            refine ⟨2685020179180093044278021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1790013452786728696185347 2685020179180093044278021)
            ·
              refine ⟨503441283596267445802129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2685020179180093044278021 503441283596267445802129)
              ·
                refine ⟨377580962697200584351597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 503441283596267445802129 377580962697200584351597)
                ·
                  refine ⟨141592861011450219131849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 377580962697200584351597 141592861011450219131849)
                  ·
                    rfl

theorem cell20_310220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 4, 2, 3].length) (baseStart_310220 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_310220 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_310220 prefixEnd_310220 := by exact prefixLift 310220
  have htrace : WordTrace (prefixWord ++ tailWord_310220) baseStart_310220 baseEnd_310220 := by
    simpa [prefixWord, tailWord_310220, baseEnd_310220] using wordTrace_append hprefix tailTrace_310220
  have hstable : (prefixWord ++ tailWord_310220).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310220).length < 2 ^ (prefixWord ++ tailWord_310220).sum := by decide
  have hdescent : baseEnd_310220 < baseStart_310220 := by decide
  rcases family_descends (prefixWord ++ tailWord_310220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310223 : List Nat := [1, 1, 2, 1, 1, 8, 2, 2, 2]
def baseStart_310223 : Nat := 118140960795 + 310223 * 2 ^ 59
def prefixEnd_310223 : Nat := 4983230072969 + 3 ^ 40 * 310223 * 2
def baseEnd_310223 : Nat := 141594230293195542031837

theorem tailTrace_310223 : CollatzResearch.WordTrace tailWord_310223 prefixEnd_310223 141594230293195542031837 := by
  unfold tailWord_310223
  simp only [CollatzResearch.WordTrace]
  refine ⟨11314762355122527715407323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 7543174903415018476938215 11314762355122527715407323)
  ·
    refine ⟨16972143532683791573110985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11314762355122527715407323 16972143532683791573110985)
    ·
      refine ⟨12729107649512843679833239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16972143532683791573110985 12729107649512843679833239)
      ·
        refine ⟨19093661474269265519749859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12729107649512843679833239 19093661474269265519749859)
        ·
          refine ⟨28640492211403898279624789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19093661474269265519749859 28640492211403898279624789)
          ·
            refine ⟨335630768102389432964353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 28640492211403898279624789 335630768102389432964353)
            ·
              refine ⟨251723076076792074723265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 335630768102389432964353 251723076076792074723265)
              ·
                refine ⟨188792307057594056042449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 251723076076792074723265 188792307057594056042449)
                ·
                  refine ⟨141594230293195542031837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 188792307057594056042449 141594230293195542031837)
                  ·
                    rfl

theorem cell20_310223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 2, 2, 2].length) (baseStart_310223 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_310223 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_310223 prefixEnd_310223 := by exact prefixLift 310223
  have htrace : WordTrace (prefixWord ++ tailWord_310223) baseStart_310223 baseEnd_310223 := by
    simpa [prefixWord, tailWord_310223, baseEnd_310223] using wordTrace_append hprefix tailTrace_310223
  have hstable : (prefixWord ++ tailWord_310223).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310223).length < 2 ^ (prefixWord ++ tailWord_310223).sum := by decide
  have hdescent : baseEnd_310223 < baseStart_310223 := by decide
  rcases family_descends (prefixWord ++ tailWord_310223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310230 : List Nat := [5, 2, 1, 1, 2, 3, 1, 5]
def baseStart_310230 : Nat := 118140960795 + 310230 * 2 ^ 59
def prefixEnd_310230 : Nat := 4983230072969 + 3 ^ 40 * 310230 * 2
def baseEnd_310230 : Nat := 47199141761311542932825

theorem tailTrace_310230 : CollatzResearch.WordTrace tailWord_310230 prefixEnd_310230 47199141761311542932825 := by
  unfold tailWord_310230
  simp only [CollatzResearch.WordTrace]
  refine ⟨707188604131072994432009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 7543345110731445273941429 707188604131072994432009)
  ·
    refine ⟨530391453098304745824007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 707188604131072994432009 530391453098304745824007)
    ·
      refine ⟨795587179647457118736011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 530391453098304745824007 795587179647457118736011)
      ·
        refine ⟨1193380769471185678104017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 795587179647457118736011 1193380769471185678104017)
        ·
          refine ⟨895035577103389258578013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1193380769471185678104017 895035577103389258578013)
          ·
            refine ⟨335638341413770971966755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 895035577103389258578013 335638341413770971966755)
            ·
              refine ⟨503457512120656457950133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 335638341413770971966755 503457512120656457950133)
              ·
                refine ⟨47199141761311542932825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 503457512120656457950133 47199141761311542932825)
                ·
                  rfl

theorem cell20_310230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 1, 5].length) (baseStart_310230 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_310230 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_310230 prefixEnd_310230 := by exact prefixLift 310230
  have htrace : WordTrace (prefixWord ++ tailWord_310230) baseStart_310230 baseEnd_310230 := by
    simpa [prefixWord, tailWord_310230, baseEnd_310230] using wordTrace_append hprefix tailTrace_310230
  have hstable : (prefixWord ++ tailWord_310230).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310230).length < 2 ^ (prefixWord ++ tailWord_310230).sum := by decide
  have hdescent : baseEnd_310230 < baseStart_310230 := by decide
  rcases family_descends (prefixWord ++ tailWord_310230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310234 : List Nat := [3, 1, 1, 2, 4, 1, 3, 5]
def baseStart_310234 : Nat := 118140960795 + 310234 * 2 ^ 59
def prefixEnd_310234 : Nat := 4983230072969 + 3 ^ 40 * 310234 * 2
def baseEnd_310234 : Nat := 47199750330976130888375

theorem tailTrace_310234 : CollatzResearch.WordTrace tailWord_310234 prefixEnd_310234 47199750330976130888375 := by
  unfold tailWord_310234
  simp only [CollatzResearch.WordTrace]
  refine ⟨2828790889520669148514439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 7543442372055117729371837 2828790889520669148514439)
  ·
    refine ⟨4243186334281003722771659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2828790889520669148514439 4243186334281003722771659)
    ·
      refine ⟨6364779501421505584157489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4243186334281003722771659 6364779501421505584157489)
      ·
        refine ⟨4773584626066129188118117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6364779501421505584157489 4773584626066129188118117)
        ·
          refine ⟨895047117387399222772147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4773584626066129188118117 895047117387399222772147)
          ·
            refine ⟨1342570676081098834158221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 895047117387399222772147 1342570676081098834158221)
            ·
              refine ⟨503464003530412062809333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1342570676081098834158221 503464003530412062809333)
              ·
                refine ⟨47199750330976130888375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 503464003530412062809333 47199750330976130888375)
                ·
                  rfl

theorem cell20_310234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 3, 5].length) (baseStart_310234 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_310234 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_310234 prefixEnd_310234 := by exact prefixLift 310234
  have htrace : WordTrace (prefixWord ++ tailWord_310234) baseStart_310234 baseEnd_310234 := by
    simpa [prefixWord, tailWord_310234, baseEnd_310234] using wordTrace_append hprefix tailTrace_310234
  have hstable : (prefixWord ++ tailWord_310234).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310234).length < 2 ^ (prefixWord ++ tailWord_310234).sum := by decide
  have hdescent : baseEnd_310234 < baseStart_310234 := by decide
  rcases family_descends (prefixWord ++ tailWord_310234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_310248 : List Nat := [2, 1, 4, 1, 1, 1, 3, 1, 6]
def baseStart_310248 : Nat := 118140960795 + 310248 * 2 ^ 59
def prefixEnd_310248 : Nat := 4983230072969 + 3 ^ 40 * 310248 * 2
def baseEnd_310248 : Nat := 141605640974406566198401

theorem tailTrace_310248 : CollatzResearch.WordTrace tailWord_310248 prefixEnd_310248 141605640974406566198401 := by
  unfold tailWord_310248
  simp only [CollatzResearch.WordTrace]
  refine ⟨5657837090015978492533699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 7543782786687971323378265 5657837090015978492533699)
  ·
    refine ⟨8486755635023967738800549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5657837090015978492533699 8486755635023967738800549)
    ·
      refine ⟨1591266681566993951025103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8486755635023967738800549 1591266681566993951025103)
      ·
        refine ⟨2386900022350490926537655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1591266681566993951025103 2386900022350490926537655)
        ·
          refine ⟨3580350033525736389806483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2386900022350490926537655 3580350033525736389806483)
          ·
            refine ⟨5370525050288604584709725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3580350033525736389806483 5370525050288604584709725)
            ·
              refine ⟨2013946893858226719266147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5370525050288604584709725 2013946893858226719266147)
              ·
                refine ⟨3020920340787340078899221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2013946893858226719266147 3020920340787340078899221)
                ·
                  refine ⟨141605640974406566198401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3020920340787340078899221 141605640974406566198401)
                  ·
                    rfl

theorem cell20_310248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 1, 6].length) (baseStart_310248 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_310248 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_310248 prefixEnd_310248 := by exact prefixLift 310248
  have htrace : WordTrace (prefixWord ++ tailWord_310248) baseStart_310248 baseEnd_310248 := by
    simpa [prefixWord, tailWord_310248, baseEnd_310248] using wordTrace_append hprefix tailTrace_310248
  have hstable : (prefixWord ++ tailWord_310248).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_310248).length < 2 ^ (prefixWord ++ tailWord_310248).sum := by decide
  have hdescent : baseEnd_310248 < baseStart_310248 := by decide
  rcases family_descends (prefixWord ++ tailWord_310248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
