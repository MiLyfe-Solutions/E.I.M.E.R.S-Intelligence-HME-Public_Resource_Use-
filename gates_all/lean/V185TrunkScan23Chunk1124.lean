import V185TrunkScan23Chunk1123

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6657623 : List Nat := [1, 1, 3, 2, 2, 3, 1, 2, 2, 3, 3]
def baseStart_6657623 : Nat := 118140960795 + 6657623 * 2 ^ 59
def prefixEnd_6657623 : Nat := 4983230072969 + 3 ^ 40 * 6657623 * 2
def baseEnd_6657623 : Nat := 3418560615428310753094655

theorem tailTrace_6657623 : CollatzResearch.WordTrace tailWord_6657623 prefixEnd_6657623 3418560615428310753094655 := by
  unfold tailWord_6657623
  simp only [CollatzResearch.WordTrace]
  refine ⟨242823459559576377329809523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161882306373050918219873015 242823459559576377329809523)
  ·
    refine ⟨364235189339364565994714285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242823459559576377329809523 364235189339364565994714285)
    ·
      refine ⟨136588196002261712248017857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 364235189339364565994714285 136588196002261712248017857)
      ·
        refine ⟨102441147001696284186013393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136588196002261712248017857 102441147001696284186013393)
        ·
          refine ⟨76830860251272213139510045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102441147001696284186013393 76830860251272213139510045)
          ·
            refine ⟨28811572594227079927316267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76830860251272213139510045 28811572594227079927316267)
            ·
              refine ⟨43217358891340619890974401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28811572594227079927316267 43217358891340619890974401)
              ·
                refine ⟨32413019168505464918230801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43217358891340619890974401 32413019168505464918230801)
                ·
                  refine ⟨24309764376379098688673101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32413019168505464918230801 24309764376379098688673101)
                  ·
                    refine ⟨9116161641142162008252413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24309764376379098688673101 9116161641142162008252413)
                    ·
                      refine ⟨3418560615428310753094655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9116161641142162008252413 3418560615428310753094655)
                      ·
                        rfl

theorem cell23_6657623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 2, 2, 3, 3].length) (baseStart_6657623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6657623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6657623 prefixEnd_6657623 := by exact prefixLift 6657623
  have htrace : WordTrace (prefixWord ++ tailWord_6657623) baseStart_6657623 baseEnd_6657623 := by
    simpa [prefixWord, tailWord_6657623, baseEnd_6657623] using wordTrace_append hprefix tailTrace_6657623
  have hstable : (prefixWord ++ tailWord_6657623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6657623).length < 2 ^ (prefixWord ++ tailWord_6657623).sum := by decide
  have hdescent : baseEnd_6657623 < baseStart_6657623 := by decide
  rcases family_descends (prefixWord ++ tailWord_6657623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6657640 : List Nat := [2, 1, 4, 3, 1, 1, 2, 1, 2, 3, 3]
def baseStart_6657640 : Nat := 118140960795 + 6657640 * 2 ^ 59
def prefixEnd_6657640 : Nat := 4983230072969 + 3 ^ 40 * 6657640 * 2
def baseEnd_6657640 : Nat := 3418569344599437186582077

theorem tailTrace_6657640 : CollatzResearch.WordTrace tailWord_6657640 prefixEnd_6657640 3418569344599437186582077 := by
  unfold tailWord_6657640
  simp only [CollatzResearch.WordTrace]
  refine ⟨121412039800257394616589187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161882719733676526155452249 121412039800257394616589187)
  ·
    refine ⟨182118059700386091924883781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121412039800257394616589187 182118059700386091924883781)
    ·
      refine ⟨34147136193822392235915709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 182118059700386091924883781 34147136193822392235915709)
      ·
        refine ⟨12805176072683397088468391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34147136193822392235915709 12805176072683397088468391)
        ·
          refine ⟨19207764109025095632702587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12805176072683397088468391 19207764109025095632702587)
          ·
            refine ⟨28811646163537643449053881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19207764109025095632702587 28811646163537643449053881)
            ·
              refine ⟨21608734622653232586790411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28811646163537643449053881 21608734622653232586790411)
              ·
                refine ⟨32413101933979848880185617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21608734622653232586790411 32413101933979848880185617)
                ·
                  refine ⟨24309826450484886660139213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32413101933979848880185617 24309826450484886660139213)
                  ·
                    refine ⟨9116184918931832497552205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24309826450484886660139213 9116184918931832497552205)
                    ·
                      refine ⟨3418569344599437186582077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9116184918931832497552205 3418569344599437186582077)
                      ·
                        rfl

theorem cell23_6657640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_6657640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6657640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6657640 prefixEnd_6657640 := by exact prefixLift 6657640
  have htrace : WordTrace (prefixWord ++ tailWord_6657640) baseStart_6657640 baseEnd_6657640 := by
    simpa [prefixWord, tailWord_6657640, baseEnd_6657640] using wordTrace_append hprefix tailTrace_6657640
  have hstable : (prefixWord ++ tailWord_6657640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6657640).length < 2 ^ (prefixWord ++ tailWord_6657640).sum := by decide
  have hdescent : baseEnd_6657640 < baseStart_6657640 := by decide
  rcases family_descends (prefixWord ++ tailWord_6657640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6657673 : List Nat := [1, 2, 1, 1, 4, 1, 2, 2, 5, 4]
def baseStart_6657673 : Nat := 118140960795 + 6657673 * 2 ^ 59
def prefixEnd_6657673 : Nat := 4983230072969 + 3 ^ 40 * 6657673 * 2
def baseEnd_6657673 : Nat := 1139528763153678519156475

theorem tailTrace_6657673 : CollatzResearch.WordTrace tailWord_6657673 prefixEnd_6657673 1139528763153678519156475 := by
  unfold tailWord_6657673
  simp only [CollatzResearch.WordTrace]
  refine ⟨242825283209395235869129673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161883522139596823912753115 242825283209395235869129673)
  ·
    refine ⟨182118962407046426901847255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242825283209395235869129673 182118962407046426901847255)
    ·
      refine ⟨273178443610569640352770883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182118962407046426901847255 273178443610569640352770883)
      ·
        refine ⟨409767665415854460529156325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273178443610569640352770883 409767665415854460529156325)
        ·
          refine ⟨76831437265472711349216811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 409767665415854460529156325 76831437265472711349216811)
          ·
            refine ⟨115247155898209067023825217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76831437265472711349216811 115247155898209067023825217)
            ·
              refine ⟨86435366923656800267868913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115247155898209067023825217 86435366923656800267868913)
              ·
                refine ⟨64826525192742600200901685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86435366923656800267868913 64826525192742600200901685)
                ·
                  refine ⟨6077486736819618768834533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 64826525192742600200901685 6077486736819618768834533)
                  ·
                    refine ⟨1139528763153678519156475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6077486736819618768834533 1139528763153678519156475)
                    ·
                      rfl

theorem cell23_6657673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 2, 5, 4].length) (baseStart_6657673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6657673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6657673 prefixEnd_6657673 := by exact prefixLift 6657673
  have htrace : WordTrace (prefixWord ++ tailWord_6657673) baseStart_6657673 baseEnd_6657673 := by
    simpa [prefixWord, tailWord_6657673, baseEnd_6657673] using wordTrace_append hprefix tailTrace_6657673
  have hstable : (prefixWord ++ tailWord_6657673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6657673).length < 2 ^ (prefixWord ++ tailWord_6657673).sum := by decide
  have hdescent : baseEnd_6657673 < baseStart_6657673 := by decide
  rcases family_descends (prefixWord ++ tailWord_6657673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6657741 : List Nat := [1, 6, 2, 1, 1, 2, 1, 4, 1, 4]
def baseStart_6657741 : Nat := 118140960795 + 6657741 * 2 ^ 59
def prefixEnd_6657741 : Nat := 4983230072969 + 3 ^ 40 * 6657741 * 2
def baseEnd_6657741 : Nat := 1139540402048513763806371

theorem tailTrace_6657741 : CollatzResearch.WordTrace tailWord_6657741 prefixEnd_6657741 1139540402048513763806371 := by
  unfold tailWord_6657741
  simp only [CollatzResearch.WordTrace]
  refine ⟨242827763373148883482605077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161885175582099255655070051 242827763373148883482605077)
  ·
    refine ⟨11382551408116353913247113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 242827763373148883482605077 11382551408116353913247113)
    ·
      refine ⟨8536913556087265434935335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11382551408116353913247113 8536913556087265434935335)
      ·
        refine ⟨12805370334130898152403003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8536913556087265434935335 12805370334130898152403003)
        ·
          refine ⟨19208055501196347228604505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12805370334130898152403003 19208055501196347228604505)
          ·
            refine ⟨14406041625897260421453379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19208055501196347228604505 14406041625897260421453379)
            ·
              refine ⟨21609062438845890632180069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14406041625897260421453379 21609062438845890632180069)
              ·
                refine ⟨4051699207283604493533763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21609062438845890632180069 4051699207283604493533763)
                ·
                  refine ⟨6077548810925406740300645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4051699207283604493533763 6077548810925406740300645)
                  ·
                    refine ⟨1139540402048513763806371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6077548810925406740300645 1139540402048513763806371)
                    ·
                      rfl

theorem cell23_6657741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_6657741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6657741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6657741 prefixEnd_6657741 := by exact prefixLift 6657741
  have htrace : WordTrace (prefixWord ++ tailWord_6657741) baseStart_6657741 baseEnd_6657741 := by
    simpa [prefixWord, tailWord_6657741, baseEnd_6657741] using wordTrace_append hprefix tailTrace_6657741
  have hstable : (prefixWord ++ tailWord_6657741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6657741).length < 2 ^ (prefixWord ++ tailWord_6657741).sum := by decide
  have hdescent : baseEnd_6657741 < baseStart_6657741 := by decide
  rcases family_descends (prefixWord ++ tailWord_6657741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6657770 : List Nat := [3, 1, 3, 1, 1, 1, 4, 1, 3, 1, 4]
def baseStart_6657770 : Nat := 118140960795 + 6657770 * 2 ^ 59
def prefixEnd_6657770 : Nat := 4983230072969 + 3 ^ 40 * 6657770 * 2
def baseEnd_6657770 : Nat := 3418636097084521677956479

theorem tailTrace_6657770 : CollatzResearch.WordTrace tailWord_6657770 prefixEnd_6657770 3418636097084521677956479 := by
  unfold tailWord_6657770
  simp only [CollatzResearch.WordTrace]
  refine ⟨60707205272510955358852691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161885880726695880956940509 60707205272510955358852691)
  ·
    refine ⟨91060807908766433038279037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60707205272510955358852691 91060807908766433038279037)
    ·
      refine ⟨34147802965787412389354639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91060807908766433038279037 34147802965787412389354639)
      ·
        refine ⟨51221704448681118584031959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34147802965787412389354639 51221704448681118584031959)
        ·
          refine ⟨76832556673021677876047939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51221704448681118584031959 76832556673021677876047939)
          ·
            refine ⟨115248835009532516814071909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76832556673021677876047939 115248835009532516814071909)
            ·
              refine ⟨21609156564287346902638483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 115248835009532516814071909 21609156564287346902638483)
              ·
                refine ⟨32413734846431020353957725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21609156564287346902638483 32413734846431020353957725)
                ·
                  refine ⟨12155150567411632632734147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32413734846431020353957725 12155150567411632632734147)
                  ·
                    refine ⟨18232725851117448949101221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12155150567411632632734147 18232725851117448949101221)
                    ·
                      refine ⟨3418636097084521677956479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18232725851117448949101221 3418636097084521677956479)
                      ·
                        rfl

theorem cell23_6657770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 1, 3, 1, 4].length) (baseStart_6657770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6657770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6657770 prefixEnd_6657770 := by exact prefixLift 6657770
  have htrace : WordTrace (prefixWord ++ tailWord_6657770) baseStart_6657770 baseEnd_6657770 := by
    simpa [prefixWord, tailWord_6657770, baseEnd_6657770] using wordTrace_append hprefix tailTrace_6657770
  have hstable : (prefixWord ++ tailWord_6657770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6657770).length < 2 ^ (prefixWord ++ tailWord_6657770).sum := by decide
  have hdescent : baseEnd_6657770 < baseStart_6657770 := by decide
  rcases family_descends (prefixWord ++ tailWord_6657770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6657854 : List Nat := [4, 2, 1, 2, 2, 1, 2, 1, 4, 1, 3]
def baseStart_6657854 : Nat := 118140960795 + 6657854 * 2 ^ 59
def prefixEnd_6657854 : Nat := 4983230072969 + 3 ^ 40 * 6657854 * 2
def baseEnd_6657854 : Nat := 3418679229459499349306093

theorem tailTrace_6657854 : CollatzResearch.WordTrace tailWord_6657854 prefixEnd_6657854 3418679229459499349306093 := by
  unfold tailWord_6657854
  simp only [CollatzResearch.WordTrace]
  refine ⟨30353985602717437972683577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 161887923214493002520979077 30353985602717437972683577)
  ·
    refine ⟨22765489202038078479512683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30353985602717437972683577 22765489202038078479512683)
    ·
      refine ⟨34148233803057117719269025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22765489202038078479512683 34148233803057117719269025)
      ·
        refine ⟨25611175352292838289451769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34148233803057117719269025 25611175352292838289451769)
        ·
          refine ⟨19208381514219628717088827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25611175352292838289451769 19208381514219628717088827)
          ·
            refine ⟨28812572271329443075633241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19208381514219628717088827 28812572271329443075633241)
            ·
              refine ⟨21609429203497082306724931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28812572271329443075633241 21609429203497082306724931)
              ·
                refine ⟨32414143805245623460087397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21609429203497082306724931 32414143805245623460087397)
                ·
                  refine ⟨6077651963483554398766387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32414143805245623460087397 6077651963483554398766387)
                  ·
                    refine ⟨9116477945225331598149581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6077651963483554398766387 9116477945225331598149581)
                    ·
                      refine ⟨3418679229459499349306093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9116477945225331598149581 3418679229459499349306093)
                      ·
                        rfl

theorem cell23_6657854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 1, 4, 1, 3].length) (baseStart_6657854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6657854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6657854 prefixEnd_6657854 := by exact prefixLift 6657854
  have htrace : WordTrace (prefixWord ++ tailWord_6657854) baseStart_6657854 baseEnd_6657854 := by
    simpa [prefixWord, tailWord_6657854, baseEnd_6657854] using wordTrace_append hprefix tailTrace_6657854
  have hstable : (prefixWord ++ tailWord_6657854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6657854).length < 2 ^ (prefixWord ++ tailWord_6657854).sum := by decide
  have hdescent : baseEnd_6657854 < baseStart_6657854 := by decide
  rcases family_descends (prefixWord ++ tailWord_6657854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6657934 : List Nat := [4, 1, 1, 5, 1, 1, 1, 2, 7]
def baseStart_6657934 : Nat := 118140960795 + 6657934 * 2 ^ 59
def prefixEnd_6657934 : Nat := 4983230072969 + 3 ^ 40 * 6657934 * 2
def baseEnd_6657934 : Nat := 379857811990206559589525

theorem tailTrace_6657934 : CollatzResearch.WordTrace tailWord_6657934 prefixEnd_6657934 379857811990206559589525 := by
  unfold tailWord_6657934
  simp only [CollatzResearch.WordTrace]
  refine ⟨30354350332681209680547607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 161889868440966451629587237 30354350332681209680547607)
  ·
    refine ⟨45531525499021814520821411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30354350332681209680547607 45531525499021814520821411)
    ·
      refine ⟨68297288248532721781232117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45531525499021814520821411 68297288248532721781232117)
      ·
        refine ⟨6402870773299942666990511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 68297288248532721781232117 6402870773299942666990511)
        ·
          refine ⟨9604306159949914000485767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6402870773299942666990511 9604306159949914000485767)
          ·
            refine ⟨14406459239924871000728651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9604306159949914000485767 14406459239924871000728651)
            ·
              refine ⟨21609688859887306501092977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14406459239924871000728651 21609688859887306501092977)
              ·
                refine ⟨16207266644915479875819733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21609688859887306501092977 16207266644915479875819733)
                ·
                  refine ⟨379857811990206559589525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16207266644915479875819733 379857811990206559589525)
                  ·
                    rfl

theorem cell23_6657934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 2, 7].length) (baseStart_6657934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6657934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6657934 prefixEnd_6657934 := by exact prefixLift 6657934
  have htrace : WordTrace (prefixWord ++ tailWord_6657934) baseStart_6657934 baseEnd_6657934 := by
    simpa [prefixWord, tailWord_6657934, baseEnd_6657934] using wordTrace_append hprefix tailTrace_6657934
  have hstable : (prefixWord ++ tailWord_6657934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6657934).length < 2 ^ (prefixWord ++ tailWord_6657934).sum := by decide
  have hdescent : baseEnd_6657934 < baseStart_6657934 := by decide
  rcases family_descends (prefixWord ++ tailWord_6657934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6657967 : List Nat := [1, 1, 2, 1, 2, 2, 3, 1, 4, 4, 2]
def baseStart_6657967 : Nat := 118140960795 + 6657967 * 2 ^ 59
def prefixEnd_6657967 : Nat := 4983230072969 + 3 ^ 40 * 6657967 * 2
def baseEnd_6657967 : Nat := 3418737252773457407193073

theorem tailTrace_6657967 : CollatzResearch.WordTrace tailWord_6657967 prefixEnd_6657967 3418737252773457407193073 := by
  unfold tailWord_6657967
  simp only [CollatzResearch.WordTrace]
  refine ⟨242836006270330124080332155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161890670846886749386888103 242836006270330124080332155)
  ·
    refine ⟨364254009405495186120498233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242836006270330124080332155 364254009405495186120498233)
    ·
      refine ⟨273190507054121389590373675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 364254009405495186120498233 273190507054121389590373675)
      ·
        refine ⟨409785760581182084385560513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273190507054121389590373675 409785760581182084385560513)
        ·
          refine ⟨307339320435886563289170385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 409785760581182084385560513 307339320435886563289170385)
          ·
            refine ⟨230504490326914922466877789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 307339320435886563289170385 230504490326914922466877789)
            ·
              refine ⟨86439183872593095925079171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 230504490326914922466877789 86439183872593095925079171)
              ·
                refine ⟨129658775808889643887618757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86439183872593095925079171 129658775808889643887618757)
                ·
                  refine ⟨24311020464166808228928517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 129658775808889643887618757 24311020464166808228928517)
                  ·
                    refine ⟨4558316337031276542924097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24311020464166808228928517 4558316337031276542924097)
                    ·
                      refine ⟨3418737252773457407193073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4558316337031276542924097 3418737252773457407193073)
                      ·
                        rfl

theorem cell23_6657967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 1, 4, 4, 2].length) (baseStart_6657967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6657967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6657967 prefixEnd_6657967 := by exact prefixLift 6657967
  have htrace : WordTrace (prefixWord ++ tailWord_6657967) baseStart_6657967 baseEnd_6657967 := by
    simpa [prefixWord, tailWord_6657967, baseEnd_6657967] using wordTrace_append hprefix tailTrace_6657967
  have hstable : (prefixWord ++ tailWord_6657967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6657967).length < 2 ^ (prefixWord ++ tailWord_6657967).sum := by decide
  have hdescent : baseEnd_6657967 < baseStart_6657967 := by decide
  rcases family_descends (prefixWord ++ tailWord_6657967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6657970 : List Nat := [3, 2, 1, 1, 1, 1, 1, 3, 2, 3, 5]
def baseStart_6657970 : Nat := 118140960795 + 6657970 * 2 ^ 59
def prefixEnd_6657970 : Nat := 4983230072969 + 3 ^ 40 * 6657970 * 2
def baseEnd_6657970 : Nat := 3418738793215420895455559

theorem tailTrace_6657970 : CollatzResearch.WordTrace tailWord_6657970 prefixEnd_6657970 3418738793215420895455559 := by
  unfold tailWord_6657970
  simp only [CollatzResearch.WordTrace]
  refine ⟨60709028922329813898172841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161890743792879503728460909 60709028922329813898172841)
  ·
    refine ⟨45531771691747360423629631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60709028922329813898172841 45531771691747360423629631)
    ·
      refine ⟨68297657537621040635444447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45531771691747360423629631 68297657537621040635444447)
      ·
        refine ⟨102446486306431560953166671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68297657537621040635444447 102446486306431560953166671)
        ·
          refine ⟨153669729459647341429750007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102446486306431560953166671 153669729459647341429750007)
          ·
            refine ⟨230504594189471012144625011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153669729459647341429750007 230504594189471012144625011)
            ·
              refine ⟨345756891284206518216937517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 230504594189471012144625011 345756891284206518216937517)
              ·
                refine ⟨129658834231577444331351569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 345756891284206518216937517 129658834231577444331351569)
                ·
                  refine ⟨97244125673683083248513677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 129658834231577444331351569 97244125673683083248513677)
                  ·
                    refine ⟨36466547127631156218192629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 97244125673683083248513677 36466547127631156218192629)
                    ·
                      refine ⟨3418738793215420895455559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36466547127631156218192629 3418738793215420895455559)
                      ·
                        rfl

theorem cell23_6657970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 3, 2, 3, 5].length) (baseStart_6657970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6657970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6657970 prefixEnd_6657970 := by exact prefixLift 6657970
  have htrace : WordTrace (prefixWord ++ tailWord_6657970) baseStart_6657970 baseEnd_6657970 := by
    simpa [prefixWord, tailWord_6657970, baseEnd_6657970] using wordTrace_append hprefix tailTrace_6657970
  have hstable : (prefixWord ++ tailWord_6657970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6657970).length < 2 ^ (prefixWord ++ tailWord_6657970).sum := by decide
  have hdescent : baseEnd_6657970 < baseStart_6657970 := by decide
  rcases family_descends (prefixWord ++ tailWord_6657970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6658004 : List Nat := [2, 4, 1, 2, 1, 1, 2, 3, 2, 2, 3]
def baseStart_6658004 : Nat := 118140960795 + 6658004 * 2 ^ 59
def prefixEnd_6658004 : Nat := 4983230072969 + 3 ^ 40 * 6658004 * 2
def baseEnd_6658004 : Nat := 3418756251557673762430403

theorem tailTrace_6658004 : CollatzResearch.WordTrace tailWord_6658004 prefixEnd_6658004 3418756251557673762430403 := by
  unfold tailWord_6658004
  simp only [CollatzResearch.WordTrace]
  refine ⟨121418677885598039699714533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161891570514130719599619377 121418677885598039699714533)
  ·
    refine ⟨22766002103549632443696475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 121418677885598039699714533 22766002103549632443696475)
    ·
      refine ⟨34149003155324448665544713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22766002103549632443696475 34149003155324448665544713)
      ·
        refine ⟨25611752366493336499158535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34149003155324448665544713 25611752366493336499158535)
        ·
          refine ⟨38417628549740004748737803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25611752366493336499158535 38417628549740004748737803)
          ·
            refine ⟨57626442824610007123106705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38417628549740004748737803 57626442824610007123106705)
            ·
              refine ⟨43219832118457505342330029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57626442824610007123106705 43219832118457505342330029)
              ·
                refine ⟨16207437044421564503373761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43219832118457505342330029 16207437044421564503373761)
                ·
                  refine ⟨12155577783316173377530321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16207437044421564503373761 12155577783316173377530321)
                  ·
                    refine ⟨9116683337487130033147741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12155577783316173377530321 9116683337487130033147741)
                    ·
                      refine ⟨3418756251557673762430403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9116683337487130033147741 3418756251557673762430403)
                      ·
                        rfl

theorem cell23_6658004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 3, 2, 2, 3].length) (baseStart_6658004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6658004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6658004 prefixEnd_6658004 := by exact prefixLift 6658004
  have htrace : WordTrace (prefixWord ++ tailWord_6658004) baseStart_6658004 baseEnd_6658004 := by
    simpa [prefixWord, tailWord_6658004, baseEnd_6658004] using wordTrace_append hprefix tailTrace_6658004
  have hstable : (prefixWord ++ tailWord_6658004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6658004).length < 2 ^ (prefixWord ++ tailWord_6658004).sum := by decide
  have hdescent : baseEnd_6658004 < baseStart_6658004 := by decide
  rcases family_descends (prefixWord ++ tailWord_6658004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6658044 : List Nat := [2, 2, 2, 1, 2, 2, 1, 2, 4, 3, 2]
def baseStart_6658044 : Nat := 118140960795 + 6658044 * 2 ^ 59
def prefixEnd_6658044 : Nat := 4983230072969 + 3 ^ 40 * 6658044 * 2
def baseEnd_6658044 : Nat := 3418776790783853605930219

theorem tailTrace_6658044 : CollatzResearch.WordTrace tailWord_6658044 prefixEnd_6658044 3418776790783853605930219 := by
  unfold tailWord_6658044
  simp only [CollatzResearch.WordTrace]
  refine ⟨121419407345525583115442593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161892543127367444153923457 121419407345525583115442593)
  ·
    refine ⟨91064555509144187336581945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121419407345525583115442593 91064555509144187336581945)
    ·
      refine ⟨68298416631858140502436459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91064555509144187336581945 68298416631858140502436459)
      ·
        refine ⟨102447624947787210753654689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68298416631858140502436459 102447624947787210753654689)
        ·
          refine ⟨76835718710840408065241017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102447624947787210753654689 76835718710840408065241017)
          ·
            refine ⟨57626789033130306048930763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76835718710840408065241017 57626789033130306048930763)
            ·
              refine ⟨86440183549695459073396145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57626789033130306048930763 86440183549695459073396145)
              ·
                refine ⟨64830137662271594305047109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86440183549695459073396145 64830137662271594305047109)
                ·
                  refine ⟨12155650811675923932196333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64830137662271594305047109 12155650811675923932196333)
                  ·
                    refine ⟨4558369054378471474573625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12155650811675923932196333 4558369054378471474573625)
                    ·
                      refine ⟨3418776790783853605930219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4558369054378471474573625 3418776790783853605930219)
                      ·
                        rfl

theorem cell23_6658044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 2, 4, 3, 2].length) (baseStart_6658044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6658044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6658044 prefixEnd_6658044 := by exact prefixLift 6658044
  have htrace : WordTrace (prefixWord ++ tailWord_6658044) baseStart_6658044 baseEnd_6658044 := by
    simpa [prefixWord, tailWord_6658044, baseEnd_6658044] using wordTrace_append hprefix tailTrace_6658044
  have hstable : (prefixWord ++ tailWord_6658044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6658044).length < 2 ^ (prefixWord ++ tailWord_6658044).sum := by decide
  have hdescent : baseEnd_6658044 < baseStart_6658044 := by decide
  rcases family_descends (prefixWord ++ tailWord_6658044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6658067 : List Nat := [1, 1, 1, 2, 1, 4, 2, 1, 6, 4]
def baseStart_6658067 : Nat := 118140960795 + 6658067 * 2 ^ 59
def prefixEnd_6658067 : Nat := 4983230072969 + 3 ^ 40 * 6658067 * 2
def baseEnd_6658067 : Nat := 1139596200279635671980871

theorem tailTrace_6658067 : CollatzResearch.WordTrace tailWord_6658067 prefixEnd_6658067 1139596200279635671980871 := by
  unfold tailWord_6658067
  simp only [CollatzResearch.WordTrace]
  refine ⟨242839653569967841158972455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161893102379978560772648303 242839653569967841158972455)
  ·
    refine ⟨364259480354951761738458683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242839653569967841158972455 364259480354951761738458683)
    ·
      refine ⟨546389220532427642607688025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 364259480354951761738458683 546389220532427642607688025)
      ·
        refine ⟨409791915399320731955766019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 546389220532427642607688025 409791915399320731955766019)
        ·
          refine ⟨614687873098981097933649029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 409791915399320731955766019 614687873098981097933649029)
          ·
            refine ⟨115253976206058955862559193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 614687873098981097933649029 115253976206058955862559193)
            ·
              refine ⟨86440482154544216896919395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115253976206058955862559193 86440482154544216896919395)
              ·
                refine ⟨129660723231816325345379093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86440482154544216896919395 129660723231816325345379093)
                ·
                  refine ⟨6077846401491390250564645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 129660723231816325345379093 6077846401491390250564645)
                  ·
                    refine ⟨1139596200279635671980871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6077846401491390250564645 1139596200279635671980871)
                    ·
                      rfl

theorem cell23_6658067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 1, 6, 4].length) (baseStart_6658067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6658067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6658067 prefixEnd_6658067 := by exact prefixLift 6658067
  have htrace : WordTrace (prefixWord ++ tailWord_6658067) baseStart_6658067 baseEnd_6658067 := by
    simpa [prefixWord, tailWord_6658067, baseEnd_6658067] using wordTrace_append hprefix tailTrace_6658067
  have hstable : (prefixWord ++ tailWord_6658067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6658067).length < 2 ^ (prefixWord ++ tailWord_6658067).sum := by decide
  have hdescent : baseEnd_6658067 < baseStart_6658067 := by decide
  rcases family_descends (prefixWord ++ tailWord_6658067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6658080 : List Nat := [2, 1, 1, 19]
def baseStart_6658080 : Nat := 118140960795 + 6658080 * 2 ^ 59
def prefixEnd_6658080 : Nat := 4983230072969 + 3 ^ 40 * 6658080 * 2
def baseEnd_6658080 : Nat := 1563235151388850235519

theorem tailTrace_6658080 : CollatzResearch.WordTrace tailWord_6658080 prefixEnd_6658080 1563235151388850235519 := by
  unfold tailWord_6658080
  simp only [CollatzResearch.WordTrace]
  refine ⟨121420063859460372189597847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161893418479280496252797129 121420063859460372189597847)
  ·
    refine ⟨182130095789190558284396771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121420063859460372189597847 182130095789190558284396771)
    ·
      refine ⟨273195143683785837426595157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182130095789190558284396771 273195143683785837426595157)
      ·
        refine ⟨1563235151388850235519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 19 273195143683785837426595157 1563235151388850235519)
        ·
          rfl

theorem cell23_6658080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 19].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 19].length) (baseStart_6658080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6658080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6658080 prefixEnd_6658080 := by exact prefixLift 6658080
  have htrace : WordTrace (prefixWord ++ tailWord_6658080) baseStart_6658080 baseEnd_6658080 := by
    simpa [prefixWord, tailWord_6658080, baseEnd_6658080] using wordTrace_append hprefix tailTrace_6658080
  have hstable : (prefixWord ++ tailWord_6658080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6658080).length < 2 ^ (prefixWord ++ tailWord_6658080).sum := by decide
  have hdescent : baseEnd_6658080 < baseStart_6658080 := by decide
  rcases family_descends (prefixWord ++ tailWord_6658080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6658085 : List Nat := [1, 3, 1, 2, 2, 5, 2, 2, 1, 1, 3]
def baseStart_6658085 : Nat := 118140960795 + 6658085 * 2 ^ 59
def prefixEnd_6658085 : Nat := 4983230072969 + 3 ^ 40 * 6658085 * 2
def baseEnd_6658085 : Nat := 3418797843490687945517531

theorem tailTrace_6658085 : CollatzResearch.WordTrace tailWord_6658085 prefixEnd_6658085 3418797843490687945517531 := by
  unfold tailWord_6658085
  simp only [CollatzResearch.WordTrace]
  refine ⟨242840310083902630233127709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161893540055935086822085139 242840310083902630233127709)
  ·
    refine ⟨91065116281463486337422891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 242840310083902630233127709 91065116281463486337422891)
    ·
      refine ⟨136597674422195229506134337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91065116281463486337422891 136597674422195229506134337)
      ·
        refine ⟨102448255816646422129600753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136597674422195229506134337 102448255816646422129600753)
        ·
          refine ⟨76836191862484816597200565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102448255816646422129600753 76836191862484816597200565)
          ·
            refine ⟨7203392987107951555987553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 76836191862484816597200565 7203392987107951555987553)
            ·
              refine ⟨5402544740330963666990665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7203392987107951555987553 5402544740330963666990665)
              ·
                refine ⟨4051908555248222750242999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5402544740330963666990665 4051908555248222750242999)
                ·
                  refine ⟨6077862832872334125364499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4051908555248222750242999 6077862832872334125364499)
                  ·
                    refine ⟨9116794249308501188046749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6077862832872334125364499 9116794249308501188046749)
                    ·
                      refine ⟨3418797843490687945517531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9116794249308501188046749 3418797843490687945517531)
                      ·
                        rfl

theorem cell23_6658085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 2, 2, 1, 1, 3].length) (baseStart_6658085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6658085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6658085 prefixEnd_6658085 := by exact prefixLift 6658085
  have htrace : WordTrace (prefixWord ++ tailWord_6658085) baseStart_6658085 baseEnd_6658085 := by
    simpa [prefixWord, tailWord_6658085, baseEnd_6658085] using wordTrace_append hprefix tailTrace_6658085
  have hstable : (prefixWord ++ tailWord_6658085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6658085).length < 2 ^ (prefixWord ++ tailWord_6658085).sum := by decide
  have hdescent : baseEnd_6658085 < baseStart_6658085 := by decide
  rcases family_descends (prefixWord ++ tailWord_6658085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6658097 : List Nat := [1, 2, 2, 3, 1, 3, 3, 8]
def baseStart_6658097 : Nat := 118140960795 + 6658097 * 2 ^ 59
def prefixEnd_6658097 : Nat := 4983230072969 + 3 ^ 40 * 6658097 * 2
def baseEnd_6658097 : Nat := 126622370565131181428425

theorem tailTrace_6658097 : CollatzResearch.WordTrace tailWord_6658097 prefixEnd_6658097 126622370565131181428425 := by
  unfold tailWord_6658097
  simp only [CollatzResearch.WordTrace]
  refine ⟨242840747759859156282564545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161893831839906104188376363 242840747759859156282564545)
  ·
    refine ⟨182130560819894367211923409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242840747759859156282564545 182130560819894367211923409)
    ·
      refine ⟨136597920614920775408942557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182130560819894367211923409 136597920614920775408942557)
      ·
        refine ⟨51224220230595290778353459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136597920614920775408942557 51224220230595290778353459)
        ·
          refine ⟨76836330345892936167530189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51224220230595290778353459 76836330345892936167530189)
          ·
            refine ⟨28813623879709851062823821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76836330345892936167530189 28813623879709851062823821)
            ·
              refine ⟨10805108954891194148558933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28813623879709851062823821 10805108954891194148558933)
              ·
                refine ⟨126622370565131181428425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10805108954891194148558933 126622370565131181428425)
                ·
                  rfl

theorem cell23_6658097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 3, 8].length) (baseStart_6658097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6658097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6658097 prefixEnd_6658097 := by exact prefixLift 6658097
  have htrace : WordTrace (prefixWord ++ tailWord_6658097) baseStart_6658097 baseEnd_6658097 := by
    simpa [prefixWord, tailWord_6658097, baseEnd_6658097] using wordTrace_append hprefix tailTrace_6658097
  have hstable : (prefixWord ++ tailWord_6658097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6658097).length < 2 ^ (prefixWord ++ tailWord_6658097).sum := by decide
  have hdescent : baseEnd_6658097 < baseStart_6658097 := by decide
  rcases family_descends (prefixWord ++ tailWord_6658097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6658107 : List Nat := [1, 1, 1, 1, 1, 2, 1, 4, 5, 3, 3]
def baseStart_6658107 : Nat := 118140960795 + 6658107 * 2 ^ 59
def prefixEnd_6658107 : Nat := 4983230072969 + 3 ^ 40 * 6658107 * 2
def baseEnd_6658107 : Nat := 3418809140065086859442429

theorem tailTrace_6658107 : CollatzResearch.WordTrace tailWord_6658107 prefixEnd_6658107 3418809140065086859442429 := by
  unfold tailWord_6658107
  simp only [CollatzResearch.WordTrace]
  refine ⟨242841112489822927990428575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161894074993215285326952383 242841112489822927990428575)
  ·
    refine ⟨364261668734734391985642863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242841112489822927990428575 364261668734734391985642863)
    ·
      refine ⟨546392503102101587978464295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 364261668734734391985642863 546392503102101587978464295)
      ·
        refine ⟨819588754653152381967696443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 546392503102101587978464295 819588754653152381967696443)
        ·
          refine ⟨1229383131979728572951544665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 819588754653152381967696443 1229383131979728572951544665)
          ·
            refine ⟨922037348984796429713658499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1229383131979728572951544665 922037348984796429713658499)
            ·
              refine ⟨1383056023477194644570487749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 922037348984796429713658499 1383056023477194644570487749)
              ·
                refine ⟨259323004401973995856966453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1383056023477194644570487749 259323004401973995856966453)
                ·
                  refine ⟨24311531662685062111590605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 259323004401973995856966453 24311531662685062111590605)
                  ·
                    refine ⟨9116824373506898291846477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24311531662685062111590605 9116824373506898291846477)
                    ·
                      refine ⟨3418809140065086859442429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9116824373506898291846477 3418809140065086859442429)
                      ·
                        rfl

theorem cell23_6658107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 5, 3, 3].length) (baseStart_6658107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6658107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6658107 prefixEnd_6658107 := by exact prefixLift 6658107
  have htrace : WordTrace (prefixWord ++ tailWord_6658107) baseStart_6658107 baseEnd_6658107 := by
    simpa [prefixWord, tailWord_6658107, baseEnd_6658107] using wordTrace_append hprefix tailTrace_6658107
  have hstable : (prefixWord ++ tailWord_6658107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6658107).length < 2 ^ (prefixWord ++ tailWord_6658107).sum := by decide
  have hdescent : baseEnd_6658107 < baseStart_6658107 := by decide
  rcases family_descends (prefixWord ++ tailWord_6658107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6658124 : List Nat := [2, 2, 1, 3, 1, 1, 4, 2, 1, 3, 3]
def baseStart_6658124 : Nat := 118140960795 + 6658124 * 2 ^ 59
def prefixEnd_6658124 : Nat := 4983230072969 + 3 ^ 40 * 6658124 * 2
def baseEnd_6658124 : Nat := 3418817869236213292929851

theorem tailTrace_6658124 : CollatzResearch.WordTrace tailWord_6658124 prefixEnd_6658124 3418817869236213292929851 := by
  unfold tailWord_6658124
  simp only [CollatzResearch.WordTrace]
  refine ⟨121420866265380669946898713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161894488353840893262531617 121420866265380669946898713)
  ·
    refine ⟨91065649699035502460174035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121420866265380669946898713 91065649699035502460174035)
    ·
      refine ⟨136598474548553253690261053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91065649699035502460174035 136598474548553253690261053)
      ·
        refine ⟨51224427955707470133847895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136598474548553253690261053 51224427955707470133847895)
        ·
          refine ⟨76836641933561205200771843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51224427955707470133847895 76836641933561205200771843)
          ·
            refine ⟨115254962900341807801157765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76836641933561205200771843 115254962900341807801157765)
            ·
              refine ⟨21610305543814088962717081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 115254962900341807801157765 21610305543814088962717081)
              ·
                refine ⟨16207729157860566722037811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21610305543814088962717081 16207729157860566722037811)
                ·
                  refine ⟨24311593736790850083056717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16207729157860566722037811 24311593736790850083056717)
                  ·
                    refine ⟨9116847651296568781146269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24311593736790850083056717 9116847651296568781146269)
                    ·
                      refine ⟨3418817869236213292929851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9116847651296568781146269 3418817869236213292929851)
                      ·
                        rfl

theorem cell23_6658124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 2, 1, 3, 3].length) (baseStart_6658124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6658124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6658124 prefixEnd_6658124 := by exact prefixLift 6658124
  have htrace : WordTrace (prefixWord ++ tailWord_6658124) baseStart_6658124 baseEnd_6658124 := by
    simpa [prefixWord, tailWord_6658124, baseEnd_6658124] using wordTrace_append hprefix tailTrace_6658124
  have hstable : (prefixWord ++ tailWord_6658124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6658124).length < 2 ^ (prefixWord ++ tailWord_6658124).sum := by decide
  have hdescent : baseEnd_6658124 < baseStart_6658124 := by decide
  rcases family_descends (prefixWord ++ tailWord_6658124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6658147 : List Nat := [1, 1, 1, 5, 1, 1, 2, 1, 1, 5, 4]
def baseStart_6658147 : Nat := 118140960795 + 6658147 * 2 ^ 59
def prefixEnd_6658147 : Nat := 4983230072969 + 3 ^ 40 * 6658147 * 2
def baseEnd_6658147 : Nat := 3418829679291266702942245

theorem tailTrace_6658147 : CollatzResearch.WordTrace tailWord_6658147 prefixEnd_6658147 3418829679291266702942245 := by
  unfold tailWord_6658147
  simp only [CollatzResearch.WordTrace]
  refine ⟨242842571409678014821884695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161895047606452009881256463 242842571409678014821884695)
  ·
    refine ⟨364263857114517022232827043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242842571409678014821884695 364263857114517022232827043)
    ·
      refine ⟨546395785671775533349240565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 364263857114517022232827043 546395785671775533349240565)
      ·
        refine ⟨51224604906728956251491303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 546395785671775533349240565 51224604906728956251491303)
        ·
          refine ⟨76836907360093434377236955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51224604906728956251491303 76836907360093434377236955)
          ·
            refine ⟨115255361040140151565855433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76836907360093434377236955 115255361040140151565855433)
            ·
              refine ⟨86441520780105113674391575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115255361040140151565855433 86441520780105113674391575)
              ·
                refine ⟨129662281170157670511587363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86441520780105113674391575 129662281170157670511587363)
                ·
                  refine ⟨194493421755236505767381045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 129662281170157670511587363 194493421755236505767381045)
                  ·
                    refine ⟨18233758289553422415691973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 194493421755236505767381045 18233758289553422415691973)
                    ·
                      refine ⟨3418829679291266702942245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18233758289553422415691973 3418829679291266702942245)
                      ·
                        rfl

theorem cell23_6658147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 1, 1, 5, 4].length) (baseStart_6658147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6658147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6658147 prefixEnd_6658147 := by exact prefixLift 6658147
  have htrace : WordTrace (prefixWord ++ tailWord_6658147) baseStart_6658147 baseEnd_6658147 := by
    simpa [prefixWord, tailWord_6658147, baseEnd_6658147] using wordTrace_append hprefix tailTrace_6658147
  have hstable : (prefixWord ++ tailWord_6658147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6658147).length < 2 ^ (prefixWord ++ tailWord_6658147).sum := by decide
  have hdescent : baseEnd_6658147 < baseStart_6658147 := by decide
  rcases family_descends (prefixWord ++ tailWord_6658147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6658184 : List Nat := [2, 1, 3, 4, 1, 1, 1, 1, 1, 3, 5]
def baseStart_6658184 : Nat := 118140960795 + 6658184 * 2 ^ 59
def prefixEnd_6658184 : Nat := 4983230072969 + 3 ^ 40 * 6658184 * 2
def baseEnd_6658184 : Nat := 3418848678075483058179575

theorem tailTrace_6658184 : CollatzResearch.WordTrace tailWord_6658184 prefixEnd_6658184 3418848678075483058179575 := by
  unfold tailWord_6658184
  simp only [CollatzResearch.WordTrace]
  refine ⟨121421960455271985070490803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161895947273695980093987737 121421960455271985070490803)
  ·
    refine ⟨182132940682907977605736205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121421960455271985070490803 182132940682907977605736205)
    ·
      refine ⟨68299852756090491602151077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182132940682907977605736205 68299852756090491602151077)
      ·
        refine ⟨12806222391766967175403327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68299852756090491602151077 12806222391766967175403327)
        ·
          refine ⟨19209333587650450763104991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12806222391766967175403327 19209333587650450763104991)
          ·
            refine ⟨28814000381475676144657487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19209333587650450763104991 28814000381475676144657487)
            ·
              refine ⟨43221000572213514216986231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28814000381475676144657487 43221000572213514216986231)
              ·
                refine ⟨64831500858320271325479347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43221000572213514216986231 64831500858320271325479347)
                ·
                  refine ⟨97247251287480406988219021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64831500858320271325479347 97247251287480406988219021)
                  ·
                    refine ⟨36467719232805152620582133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 97247251287480406988219021 36467719232805152620582133)
                    ·
                      refine ⟨3418848678075483058179575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36467719232805152620582133 3418848678075483058179575)
                      ·
                        rfl

theorem cell23_6658184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_6658184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6658184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6658184 prefixEnd_6658184 := by exact prefixLift 6658184
  have htrace : WordTrace (prefixWord ++ tailWord_6658184) baseStart_6658184 baseEnd_6658184 := by
    simpa [prefixWord, tailWord_6658184, baseEnd_6658184] using wordTrace_append hprefix tailTrace_6658184
  have hstable : (prefixWord ++ tailWord_6658184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6658184).length < 2 ^ (prefixWord ++ tailWord_6658184).sum := by decide
  have hdescent : baseEnd_6658184 < baseStart_6658184 := by decide
  rcases family_descends (prefixWord ++ tailWord_6658184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6658197 : List Nat := [1, 3, 2, 1, 1, 1, 3, 1, 1, 2, 7]
def baseStart_6658197 : Nat := 118140960795 + 6658197 * 2 ^ 59
def prefixEnd_6658197 : Nat := 4983230072969 + 3 ^ 40 * 6658197 * 2
def baseEnd_6658197 : Nat := 3418855353323991507317015

theorem tailTrace_6658197 : CollatzResearch.WordTrace tailWord_6658197 prefixEnd_6658197 3418855353323991507317015 := by
  unfold tailWord_6658197
  simp only [CollatzResearch.WordTrace]
  refine ⟨242844395059496873361204845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161896263372997915574136563 242844395059496873361204845)
  ·
    refine ⟨91066648147311327510451817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 242844395059496873361204845 91066648147311327510451817)
    ·
      refine ⟨68299986110483495632838863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91066648147311327510451817 68299986110483495632838863)
      ·
        refine ⟨102449979165725243449258295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68299986110483495632838863 102449979165725243449258295)
        ·
          refine ⟨153674968748587865173887443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102449979165725243449258295 153674968748587865173887443)
          ·
            refine ⟨230512453122881797760831165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153674968748587865173887443 230512453122881797760831165)
            ·
              refine ⟨86442169921080674160311687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 230512453122881797760831165 86442169921080674160311687)
              ·
                refine ⟨129663254881621011240467531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86442169921080674160311687 129663254881621011240467531)
                ·
                  refine ⟨194494882322431516860701297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 129663254881621011240467531 194494882322431516860701297)
                  ·
                    refine ⟨145871161741823637645525973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 194494882322431516860701297 145871161741823637645525973)
                    ·
                      refine ⟨3418855353323991507317015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 145871161741823637645525973 3418855353323991507317015)
                      ·
                        rfl

theorem cell23_6658197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 1, 1, 2, 7].length) (baseStart_6658197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6658197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6658197 prefixEnd_6658197 := by exact prefixLift 6658197
  have htrace : WordTrace (prefixWord ++ tailWord_6658197) baseStart_6658197 baseEnd_6658197 := by
    simpa [prefixWord, tailWord_6658197, baseEnd_6658197] using wordTrace_append hprefix tailTrace_6658197
  have hstable : (prefixWord ++ tailWord_6658197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6658197).length < 2 ^ (prefixWord ++ tailWord_6658197).sum := by decide
  have hdescent : baseEnd_6658197 < baseStart_6658197 := by decide
  rcases family_descends (prefixWord ++ tailWord_6658197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6658227 : List Nat := [1, 1, 1, 2, 3, 2, 1, 1, 3, 1, 7]
def baseStart_6658227 : Nat := 118140960795 + 6658227 * 2 ^ 59
def prefixEnd_6658227 : Nat := 4983230072969 + 3 ^ 40 * 6658227 * 2
def baseEnd_6658227 : Nat := 3418870757743626389941877

theorem tailTrace_6658227 : CollatzResearch.WordTrace tailWord_6658227 prefixEnd_6658227 3418870757743626389941877 := by
  unfold tailWord_6658227
  simp only [CollatzResearch.WordTrace]
  refine ⟨242845489249388188484796935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161896992832925458989864623 242845489249388188484796935)
  ·
    refine ⟨364268233874082282727195403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242845489249388188484796935 364268233874082282727195403)
    ·
      refine ⟨546402350811123424090793105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 364268233874082282727195403 546402350811123424090793105)
      ·
        refine ⟨409801763108342568068094829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 546402350811123424090793105 409801763108342568068094829)
        ·
          refine ⟨153675661165628463025535561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 409801763108342568068094829 153675661165628463025535561)
          ·
            refine ⟨115256745874221347269151671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153675661165628463025535561 115256745874221347269151671)
            ·
              refine ⟨172885118811332020903727507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115256745874221347269151671 172885118811332020903727507)
              ·
                refine ⟨259327678216998031355591261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 172885118811332020903727507 259327678216998031355591261)
                ·
                  refine ⟨97247879331374261758346723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 259327678216998031355591261 97247879331374261758346723)
                  ·
                    refine ⟨145871818997061392637520085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 97247879331374261758346723 145871818997061392637520085)
                    ·
                      refine ⟨3418870757743626389941877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 145871818997061392637520085 3418870757743626389941877)
                      ·
                        rfl

theorem cell23_6658227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 3, 1, 7].length) (baseStart_6658227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6658227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6658227 prefixEnd_6658227 := by exact prefixLift 6658227
  have htrace : WordTrace (prefixWord ++ tailWord_6658227) baseStart_6658227 baseEnd_6658227 := by
    simpa [prefixWord, tailWord_6658227, baseEnd_6658227] using wordTrace_append hprefix tailTrace_6658227
  have hstable : (prefixWord ++ tailWord_6658227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6658227).length < 2 ^ (prefixWord ++ tailWord_6658227).sum := by decide
  have hdescent : baseEnd_6658227 < baseStart_6658227 := by decide
  rcases family_descends (prefixWord ++ tailWord_6658227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6658234 : List Nat := [3, 1, 1, 1, 2, 2, 3, 3, 2, 5]
def baseStart_6658234 : Nat := 118140960795 + 6658234 * 2 ^ 59
def prefixEnd_6658234 : Nat := 4983230072969 + 3 ^ 40 * 6658234 * 2
def baseEnd_6658234 : Nat := 1139624784036069287518115

theorem tailTrace_6658234 : CollatzResearch.WordTrace tailWord_6658234 prefixEnd_6658234 1139624784036069287518115 := by
  unfold tailWord_6658234
  simp only [CollatzResearch.WordTrace]
  refine ⟨60711436140090707170075439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161897163040241885786867837 60711436140090707170075439)
  ·
    refine ⟨91067154210136060755113159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60711436140090707170075439 91067154210136060755113159)
    ·
      refine ⟨136600731315204091132669739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91067154210136060755113159 136600731315204091132669739)
      ·
        refine ⟨204901096972806136699004609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136600731315204091132669739 204901096972806136699004609)
        ·
          refine ⟨153675822729604602524253457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 204901096972806136699004609 153675822729604602524253457)
          ·
            refine ⟨115256867047203451893190093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153675822729604602524253457 115256867047203451893190093)
            ·
              refine ⟨43221325142701294459946285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 115256867047203451893190093 43221325142701294459946285)
              ·
                refine ⟨16207996928512985422479857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43221325142701294459946285 16207996928512985422479857)
                ·
                  refine ⟨12155997696384739066859893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16207996928512985422479857 12155997696384739066859893)
                  ·
                    refine ⟨1139624784036069287518115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12155997696384739066859893 1139624784036069287518115)
                    ·
                      rfl

theorem cell23_6658234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 3, 2, 5].length) (baseStart_6658234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6658234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6658234 prefixEnd_6658234 := by exact prefixLift 6658234
  have htrace : WordTrace (prefixWord ++ tailWord_6658234) baseStart_6658234 baseEnd_6658234 := by
    simpa [prefixWord, tailWord_6658234, baseEnd_6658234] using wordTrace_append hprefix tailTrace_6658234
  have hstable : (prefixWord ++ tailWord_6658234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6658234).length < 2 ^ (prefixWord ++ tailWord_6658234).sum := by decide
  have hdescent : baseEnd_6658234 < baseStart_6658234 := by decide
  rcases family_descends (prefixWord ++ tailWord_6658234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6658285 : List Nat := [1, 5, 1, 2, 4, 1, 1, 1, 2, 5]
def baseStart_6658285 : Nat := 118140960795 + 6658285 * 2 ^ 59
def prefixEnd_6658285 : Nat := 4983230072969 + 3 ^ 40 * 6658285 * 2
def baseEnd_6658285 : Nat := 1139633513207195721005537

theorem tailTrace_6658285 : CollatzResearch.WordTrace tailWord_6658285 prefixEnd_6658285 1139633513207195721005537 := by
  unfold tailWord_6658285
  simp only [CollatzResearch.WordTrace]
  refine ⟨242847604683178064390408309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161898403122118709593605539 242847604683178064390408309)
  ·
    refine ⟨22766962939047943536600779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 242847604683178064390408309 22766962939047943536600779)
    ·
      refine ⟨34150444408571915304901169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22766962939047943536600779 34150444408571915304901169)
      ·
        refine ⟨25612833306428936478675877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34150444408571915304901169 25612833306428936478675877)
        ·
          refine ⟨4802406244955425589751727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25612833306428936478675877 4802406244955425589751727)
          ·
            refine ⟨7203609367433138384627591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4802406244955425589751727 7203609367433138384627591)
            ·
              refine ⟨10805414051149707576941387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7203609367433138384627591 10805414051149707576941387)
              ·
                refine ⟨16208121076724561365412081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10805414051149707576941387 16208121076724561365412081)
                ·
                  refine ⟨12156090807543421024059061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16208121076724561365412081 12156090807543421024059061)
                  ·
                    refine ⟨1139633513207195721005537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12156090807543421024059061 1139633513207195721005537)
                    ·
                      rfl

theorem cell23_6658285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 1, 1, 2, 5].length) (baseStart_6658285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6658285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6658285 prefixEnd_6658285 := by exact prefixLift 6658285
  have htrace : WordTrace (prefixWord ++ tailWord_6658285) baseStart_6658285 baseEnd_6658285 := by
    simpa [prefixWord, tailWord_6658285, baseEnd_6658285] using wordTrace_append hprefix tailTrace_6658285
  have hstable : (prefixWord ++ tailWord_6658285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6658285).length < 2 ^ (prefixWord ++ tailWord_6658285).sum := by decide
  have hdescent : baseEnd_6658285 < baseStart_6658285 := by decide
  rcases family_descends (prefixWord ++ tailWord_6658285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6658298 : List Nat := [3, 1, 1, 1, 1, 5, 1, 5, 1, 4]
def baseStart_6658298 : Nat := 118140960795 + 6658298 * 2 ^ 59
def prefixEnd_6658298 : Nat := 4983230072969 + 3 ^ 40 * 6658298 * 2
def baseEnd_6658298 : Nat := 1139635738290031870718017

theorem tailTrace_6658298 : CollatzResearch.WordTrace tailWord_6658298 prefixEnd_6658298 1139635738290031870718017 := by
  unfold tailWord_6658298
  simp only [CollatzResearch.WordTrace]
  refine ⟨60712019708032741902657887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161898719221420645073754365 60712019708032741902657887)
  ·
    refine ⟨91068029562049112853986831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60712019708032741902657887 91068029562049112853986831)
    ·
      refine ⟨136602044343073669280980247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91068029562049112853986831 136602044343073669280980247)
      ·
        refine ⟨204903066514610503921470371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136602044343073669280980247 204903066514610503921470371)
        ·
          refine ⟨307354599771915755882205557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204903066514610503921470371 307354599771915755882205557)
          ·
            refine ⟨28814493728617102113956771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 307354599771915755882205557 28814493728617102113956771)
            ·
              refine ⟨43221740592925653170935157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28814493728617102113956771 43221740592925653170935157)
              ·
                refine ⟨4052038180586779984775171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43221740592925653170935157 4052038180586779984775171)
                ·
                  refine ⟨6078057270880169977162757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4052038180586779984775171 6078057270880169977162757)
                  ·
                    refine ⟨1139635738290031870718017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6078057270880169977162757 1139635738290031870718017)
                    ·
                      rfl

theorem cell23_6658298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 5, 1, 4].length) (baseStart_6658298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6658298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6658298 prefixEnd_6658298 := by exact prefixLift 6658298
  have htrace : WordTrace (prefixWord ++ tailWord_6658298) baseStart_6658298 baseEnd_6658298 := by
    simpa [prefixWord, tailWord_6658298, baseEnd_6658298] using wordTrace_append hprefix tailTrace_6658298
  have hstable : (prefixWord ++ tailWord_6658298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6658298).length < 2 ^ (prefixWord ++ tailWord_6658298).sum := by decide
  have hdescent : baseEnd_6658298 < baseStart_6658298 := by decide
  rcases family_descends (prefixWord ++ tailWord_6658298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6658314 : List Nat := [3, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6]
def baseStart_6658314 : Nat := 118140960795 + 6658314 * 2 ^ 59
def prefixEnd_6658314 : Nat := 4983230072969 + 3 ^ 40 * 6658314 * 2
def baseEnd_6658314 : Nat := 3418915430560567549553977

theorem tailTrace_6658314 : CollatzResearch.WordTrace tailWord_6658314 prefixEnd_6658314 3418915430560567549553977 := by
  unfold tailWord_6658314
  simp only [CollatzResearch.WordTrace]
  refine ⟨60712165600018250585803499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161899108266715334895475997 60712165600018250585803499)
  ·
    refine ⟨91068248400027375878705249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60712165600018250585803499 91068248400027375878705249)
    ·
      refine ⟨68301186300020531909028937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91068248400027375878705249 68301186300020531909028937)
      ·
        refine ⟨51225889725015398931771703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68301186300020531909028937 51225889725015398931771703)
        ·
          refine ⟨76838834587523098397657555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51225889725015398931771703 76838834587523098397657555)
          ·
            refine ⟨115258251881284647596486333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76838834587523098397657555 115258251881284647596486333)
            ·
              refine ⟨43221844455481742848682375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 115258251881284647596486333 43221844455481742848682375)
              ·
                refine ⟨64832766683222614273023563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43221844455481742848682375 64832766683222614273023563)
                ·
                  refine ⟨97249150024833921409535345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64832766683222614273023563 97249150024833921409535345)
                  ·
                    refine ⟨72936862518625441057151509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 97249150024833921409535345 72936862518625441057151509)
                    ·
                      refine ⟨3418915430560567549553977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72936862518625441057151509 3418915430560567549553977)
                      ·
                        rfl

theorem cell23_6658314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6].length) (baseStart_6658314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6658314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6658314 prefixEnd_6658314 := by exact prefixLift 6658314
  have htrace : WordTrace (prefixWord ++ tailWord_6658314) baseStart_6658314 baseEnd_6658314 := by
    simpa [prefixWord, tailWord_6658314, baseEnd_6658314] using wordTrace_append hprefix tailTrace_6658314
  have hstable : (prefixWord ++ tailWord_6658314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6658314).length < 2 ^ (prefixWord ++ tailWord_6658314).sum := by decide
  have hdescent : baseEnd_6658314 < baseStart_6658314 := by decide
  rcases family_descends (prefixWord ++ tailWord_6658314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6658331 : List Nat := [1, 1, 1, 1, 1, 1, 7, 2, 1, 5, 2]
def baseStart_6658331 : Nat := 118140960795 + 6658331 * 2 ^ 59
def prefixEnd_6658331 : Nat := 4983230072969 + 3 ^ 40 * 6658331 * 2
def baseEnd_6658331 : Nat := 3418924159731693983041399

theorem tailTrace_6658331 : CollatzResearch.WordTrace tailWord_6658331 prefixEnd_6658331 3418924159731693983041399 := by
  unfold tailWord_6658331
  simp only [CollatzResearch.WordTrace]
  refine ⟨242849282441011414246582847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161899521627340942831055231 242849282441011414246582847)
  ·
    refine ⟨364273923661517121369874271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242849282441011414246582847 364273923661517121369874271)
    ·
      refine ⟨546410885492275682054811407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 364273923661517121369874271 546410885492275682054811407)
      ·
        refine ⟨819616328238413523082217111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 546410885492275682054811407 819616328238413523082217111)
        ·
          refine ⟨1229424492357620284623325667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 819616328238413523082217111 1229424492357620284623325667)
          ·
            refine ⟨1844136738536430426934988501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1229424492357620284623325667 1844136738536430426934988501)
            ·
              refine ⟨43221954809447588131288793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1844136738536430426934988501 43221954809447588131288793)
              ·
                refine ⟨32416466107085691098466595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43221954809447588131288793 32416466107085691098466595)
                ·
                  refine ⟨48624699160628536647699893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32416466107085691098466595 48624699160628536647699893)
                  ·
                    refine ⟨4558565546308925310721865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48624699160628536647699893 4558565546308925310721865)
                    ·
                      refine ⟨3418924159731693983041399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4558565546308925310721865 3418924159731693983041399)
                      ·
                        rfl

theorem cell23_6658331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 2, 1, 5, 2].length) (baseStart_6658331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6658331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6658331 prefixEnd_6658331 := by exact prefixLift 6658331
  have htrace : WordTrace (prefixWord ++ tailWord_6658331) baseStart_6658331 baseEnd_6658331 := by
    simpa [prefixWord, tailWord_6658331, baseEnd_6658331] using wordTrace_append hprefix tailTrace_6658331
  have hstable : (prefixWord ++ tailWord_6658331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6658331).length < 2 ^ (prefixWord ++ tailWord_6658331).sum := by decide
  have hdescent : baseEnd_6658331 < baseStart_6658331 := by decide
  rcases family_descends (prefixWord ++ tailWord_6658331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6658349 : List Nat := [1, 5, 3, 1, 2, 2, 1, 3, 1, 4]
def baseStart_6658349 : Nat := 118140960795 + 6658349 * 2 ^ 59
def prefixEnd_6658349 : Nat := 4983230072969 + 3 ^ 40 * 6658349 * 2
def baseEnd_6658349 : Nat := 1139644467461158304205439

theorem tailTrace_6658349 : CollatzResearch.WordTrace tailWord_6658349 prefixEnd_6658349 1139644467461158304205439 := by
  unfold tailWord_6658349
  simp only [CollatzResearch.WordTrace]
  refine ⟨242849938954946203320738101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161899959303297468880492067 242849938954946203320738101)
  ·
    refine ⟨22767181777026206561319197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 242849938954946203320738101 22767181777026206561319197)
    ·
      refine ⟨8537693166384827460494699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22767181777026206561319197 8537693166384827460494699)
      ·
        refine ⟨12806539749577241190742049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8537693166384827460494699 12806539749577241190742049)
        ·
          refine ⟨9604904812182930893056537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12806539749577241190742049 9604904812182930893056537)
          ·
            refine ⟨7203678609137198169792403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9604904812182930893056537 7203678609137198169792403)
            ·
              refine ⟨10805517913705797254688605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7203678609137198169792403 10805517913705797254688605)
              ·
                refine ⟨4052069217639673970508227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10805517913705797254688605 4052069217639673970508227)
                ·
                  refine ⟨6078103826459510955762341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4052069217639673970508227 6078103826459510955762341)
                  ·
                    refine ⟨1139644467461158304205439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6078103826459510955762341 1139644467461158304205439)
                    ·
                      rfl

theorem cell23_6658349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_6658349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6658349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6658349 prefixEnd_6658349 := by exact prefixLift 6658349
  have htrace : WordTrace (prefixWord ++ tailWord_6658349) baseStart_6658349 baseEnd_6658349 := by
    simpa [prefixWord, tailWord_6658349, baseEnd_6658349] using wordTrace_append hprefix tailTrace_6658349
  have hstable : (prefixWord ++ tailWord_6658349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6658349).length < 2 ^ (prefixWord ++ tailWord_6658349).sum := by decide
  have hdescent : baseEnd_6658349 < baseStart_6658349 := by decide
  rcases family_descends (prefixWord ++ tailWord_6658349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6658371 : List Nat := [1, 1, 1, 3, 1, 3, 4, 1, 4, 4]
def baseStart_6658371 : Nat := 118140960795 + 6658371 * 2 ^ 59
def prefixEnd_6658371 : Nat := 4983230072969 + 3 ^ 40 * 6658371 * 2
def baseEnd_6658371 : Nat := 1139648232985957942180405

theorem tailTrace_6658371 : CollatzResearch.WordTrace tailWord_6658371 prefixEnd_6658371 1139648232985957942180405 := by
  unfold tailWord_6658371
  simp only [CollatzResearch.WordTrace]
  refine ⟨242850741360866501078038967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161900494240577667385359311 242850741360866501078038967)
  ·
    refine ⟨364276112041299751617058451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242850741360866501078038967 364276112041299751617058451)
    ·
      refine ⟨546414168061949627425587677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 364276112041299751617058451 546414168061949627425587677)
      ·
        refine ⟨204905313023231110284595379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 546414168061949627425587677 204905313023231110284595379)
        ·
          refine ⟨307357969534846665426893069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204905313023231110284595379 307357969534846665426893069)
          ·
            refine ⟨115259238575567499535084901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 307357969534846665426893069 115259238575567499535084901)
            ·
              refine ⟨21611107232918906162828419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 115259238575567499535084901 21611107232918906162828419)
              ·
                refine ⟨32416660849378359244242629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21611107232918906162828419 32416660849378359244242629)
                ·
                  refine ⟨6078123909258442358295493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32416660849378359244242629 6078123909258442358295493)
                  ·
                    refine ⟨1139648232985957942180405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6078123909258442358295493 1139648232985957942180405)
                    ·
                      rfl

theorem cell23_6658371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 1, 4, 4].length) (baseStart_6658371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6658371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6658371 prefixEnd_6658371 := by exact prefixLift 6658371
  have htrace : WordTrace (prefixWord ++ tailWord_6658371) baseStart_6658371 baseEnd_6658371 := by
    simpa [prefixWord, tailWord_6658371, baseEnd_6658371] using wordTrace_append hprefix tailTrace_6658371
  have hstable : (prefixWord ++ tailWord_6658371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6658371).length < 2 ^ (prefixWord ++ tailWord_6658371).sum := by decide
  have hdescent : baseEnd_6658371 < baseStart_6658371 := by decide
  rcases family_descends (prefixWord ++ tailWord_6658371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6658384 : List Nat := [2, 1, 1, 1, 1, 6, 1, 10]
def baseStart_6658384 : Nat := 118140960795 + 6658384 * 2 ^ 59
def prefixEnd_6658384 : Nat := 4983230072969 + 3 ^ 40 * 6658384 * 2
def baseEnd_6658384 : Nat := 126627828674310454654765

theorem tailTrace_6658384 : CollatzResearch.WordTrace tailWord_6658384 prefixEnd_6658384 126627828674310454654765 := by
  unfold tailWord_6658384
  simp only [CollatzResearch.WordTrace]
  refine ⟨121425607754909702149131103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161900810339879602865508137 121425607754909702149131103)
  ·
    refine ⟨182138411632364553223696655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121425607754909702149131103 182138411632364553223696655)
    ·
      refine ⟨273207617448546829835544983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182138411632364553223696655 273207617448546829835544983)
      ·
        refine ⟨409811426172820244753317475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273207617448546829835544983 409811426172820244753317475)
        ·
          refine ⟨614717139259230367129976213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 409811426172820244753317475 614717139259230367129976213)
          ·
            refine ⟨28814865902776423459217635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 614717139259230367129976213 28814865902776423459217635)
            ·
              refine ⟨43222298854164635188826453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28814865902776423459217635 43222298854164635188826453)
              ·
                refine ⟨126627828674310454654765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 43222298854164635188826453 126627828674310454654765)
                ·
                  rfl

theorem cell23_6658384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 10].length) (baseStart_6658384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6658384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6658384 prefixEnd_6658384 := by exact prefixLift 6658384
  have htrace : WordTrace (prefixWord ++ tailWord_6658384) baseStart_6658384 baseEnd_6658384 := by
    simpa [prefixWord, tailWord_6658384, baseEnd_6658384] using wordTrace_append hprefix tailTrace_6658384
  have hstable : (prefixWord ++ tailWord_6658384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6658384).length < 2 ^ (prefixWord ++ tailWord_6658384).sum := by decide
  have hdescent : baseEnd_6658384 < baseStart_6658384 := by decide
  rcases family_descends (prefixWord ++ tailWord_6658384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6658391 : List Nat := [1, 1, 3, 2, 3, 1, 2, 3, 1, 2, 4]
def baseStart_6658391 : Nat := 118140960795 + 6658391 * 2 ^ 59
def prefixEnd_6658391 : Nat := 4983230072969 + 3 ^ 40 * 6658391 * 2
def baseEnd_6658391 : Nat := 3418954968570963748291123

theorem tailTrace_6658391 : CollatzResearch.WordTrace tailWord_6658391 prefixEnd_6658391 3418954968570963748291123 := by
  unfold tailWord_6658391
  simp only [CollatzResearch.WordTrace]
  refine ⟨242851470820794044493767027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161900980547196029662511351 242851470820794044493767027)
  ·
    refine ⟨364277206231191066740650541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242851470820794044493767027 364277206231191066740650541)
    ·
      refine ⟨136603952336696650027743953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 364277206231191066740650541 136603952336696650027743953)
      ·
        refine ⟨102452964252522487520807965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136603952336696650027743953 102452964252522487520807965)
        ·
          refine ⟨38419861594695932820302987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102452964252522487520807965 38419861594695932820302987)
          ·
            refine ⟨57629792392043899230454481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38419861594695932820302987 57629792392043899230454481)
            ·
              refine ⟨43222344294032924422840861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57629792392043899230454481 43222344294032924422840861)
              ·
                refine ⟨16208379110262346658565323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43222344294032924422840861 16208379110262346658565323)
                ·
                  refine ⟨24312568665393519987847985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16208379110262346658565323 24312568665393519987847985)
                  ·
                    refine ⟨18234426499045139990885989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24312568665393519987847985 18234426499045139990885989)
                    ·
                      refine ⟨3418954968570963748291123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18234426499045139990885989 3418954968570963748291123)
                      ·
                        rfl

theorem cell23_6658391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 3, 1, 2, 4].length) (baseStart_6658391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6658391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6658391 prefixEnd_6658391 := by exact prefixLift 6658391
  have htrace : WordTrace (prefixWord ++ tailWord_6658391) baseStart_6658391 baseEnd_6658391 := by
    simpa [prefixWord, tailWord_6658391, baseEnd_6658391] using wordTrace_append hprefix tailTrace_6658391
  have hstable : (prefixWord ++ tailWord_6658391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6658391).length < 2 ^ (prefixWord ++ tailWord_6658391).sum := by decide
  have hdescent : baseEnd_6658391 < baseStart_6658391 := by decide
  rcases family_descends (prefixWord ++ tailWord_6658391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6658408 : List Nat := [2, 1, 4, 2, 2, 2, 1, 2, 1, 2, 4]
def baseStart_6658408 : Nat := 118140960795 + 6658408 * 2 ^ 59
def prefixEnd_6658408 : Nat := 4983230072969 + 3 ^ 40 * 6658408 * 2
def baseEnd_6658408 : Nat := 3418963697742090181778545

theorem tailTrace_6658408 : CollatzResearch.WordTrace tailWord_6658408 prefixEnd_6658408 3418963697742090181778545 := by
  unfold tailWord_6658408
  simp only [CollatzResearch.WordTrace]
  refine ⟨121426045430866228198567939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161901393907821637598090585 121426045430866228198567939)
  ·
    refine ⟨182139068146299342297851909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121426045430866228198567939 182139068146299342297851909)
    ·
      refine ⟨34151075277431126680847233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 182139068146299342297851909 34151075277431126680847233)
      ·
        refine ⟨25613306458073345010635425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34151075277431126680847233 25613306458073345010635425)
        ·
          refine ⟨19209979843555008757976569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25613306458073345010635425 19209979843555008757976569)
          ·
            refine ⟨14407484882666256568482427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19209979843555008757976569 14407484882666256568482427)
            ·
              refine ⟨21611227323999384852723641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14407484882666256568482427 21611227323999384852723641)
              ·
                refine ⟨16208420492999538639542731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21611227323999384852723641 16208420492999538639542731)
                ·
                  refine ⟨24312630739499307959314097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16208420492999538639542731 24312630739499307959314097)
                  ·
                    refine ⟨18234473054624480969485573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24312630739499307959314097 18234473054624480969485573)
                    ·
                      refine ⟨3418963697742090181778545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18234473054624480969485573 3418963697742090181778545)
                      ·
                        rfl

theorem cell23_6658408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_6658408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6658408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6658408 prefixEnd_6658408 := by exact prefixLift 6658408
  have htrace : WordTrace (prefixWord ++ tailWord_6658408) baseStart_6658408 baseEnd_6658408 := by
    simpa [prefixWord, tailWord_6658408, baseEnd_6658408] using wordTrace_append hprefix tailTrace_6658408
  have hstable : (prefixWord ++ tailWord_6658408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6658408).length < 2 ^ (prefixWord ++ tailWord_6658408).sum := by decide
  have hdescent : baseEnd_6658408 < baseStart_6658408 := by decide
  rcases family_descends (prefixWord ++ tailWord_6658408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6658411 : List Nat := [1, 1, 1, 1, 2, 2, 2, 6, 1, 3, 3]
def baseStart_6658411 : Nat := 118140960795 + 6658411 * 2 ^ 59
def prefixEnd_6658411 : Nat := 4983230072969 + 3 ^ 40 * 6658411 * 2
def baseEnd_6658411 : Nat := 3418965238184053670041031

theorem tailTrace_6658411 : CollatzResearch.WordTrace tailWord_6658411 prefixEnd_6658411 3418965238184053670041031 := by
  unfold tailWord_6658411
  simp only [CollatzResearch.WordTrace]
  refine ⟨242852200280721587909495087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161901466853814391939663391 242852200280721587909495087)
  ·
    refine ⟨364278300421082381864242631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242852200280721587909495087 364278300421082381864242631)
    ·
      refine ⟨546417450631623572796363947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 364278300421082381864242631 546417450631623572796363947)
      ·
        refine ⟨819626175947435359194545921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 546417450631623572796363947 819626175947435359194545921)
        ·
          refine ⟨614719631960576519395909441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 819626175947435359194545921 614719631960576519395909441)
          ·
            refine ⟨461039723970432389546932081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 614719631960576519395909441 461039723970432389546932081)
            ·
              refine ⟨345779792977824292160199061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 461039723970432389546932081 345779792977824292160199061)
              ·
                refine ⟨16208427795835513695009331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 345779792977824292160199061 16208427795835513695009331)
                ·
                  refine ⟨24312641693753270542513997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16208427795835513695009331 24312641693753270542513997)
                  ·
                    refine ⟨9117240635157476453442749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24312641693753270542513997 9117240635157476453442749)
                    ·
                      refine ⟨3418965238184053670041031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9117240635157476453442749 3418965238184053670041031)
                      ·
                        rfl

theorem cell23_6658411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 6, 1, 3, 3].length) (baseStart_6658411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6658411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6658411 prefixEnd_6658411 := by exact prefixLift 6658411
  have htrace : WordTrace (prefixWord ++ tailWord_6658411) baseStart_6658411 baseEnd_6658411 := by
    simpa [prefixWord, tailWord_6658411, baseEnd_6658411] using wordTrace_append hprefix tailTrace_6658411
  have hstable : (prefixWord ++ tailWord_6658411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6658411).length < 2 ^ (prefixWord ++ tailWord_6658411).sum := by decide
  have hdescent : baseEnd_6658411 < baseStart_6658411 := by decide
  rcases family_descends (prefixWord ++ tailWord_6658411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6658424 : List Nat := [2, 1, 2, 1, 1, 1, 1, 1, 1, 5, 7]
def baseStart_6658424 : Nat := 118140960795 + 6658424 * 2 ^ 59
def prefixEnd_6658424 : Nat := 4983230072969 + 3 ^ 40 * 6658424 * 2
def baseEnd_6658424 : Nat := 3418971913432562119178471

theorem tailTrace_6658424 : CollatzResearch.WordTrace tailWord_6658424 prefixEnd_6658424 3418971913432562119178471 := by
  unfold tailWord_6658424
  simp only [CollatzResearch.WordTrace]
  refine ⟨121426337214837245564859163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161901782953116327419812217 121426337214837245564859163)
  ·
    refine ⟨182139505822255868347288745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121426337214837245564859163 182139505822255868347288745)
    ·
      refine ⟨136604629366691901260466559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182139505822255868347288745 136604629366691901260466559)
      ·
        refine ⟨204906944050037851890699839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136604629366691901260466559 204906944050037851890699839)
        ·
          refine ⟨307360416075056777836049759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204906944050037851890699839 307360416075056777836049759)
          ·
            refine ⟨461040624112585166754074639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 307360416075056777836049759 461040624112585166754074639)
            ·
              refine ⟨691560936168877750131111959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 461040624112585166754074639 691560936168877750131111959)
              ·
                refine ⟨1037341404253316625196667939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 691560936168877750131111959 1037341404253316625196667939)
                ·
                  refine ⟨1556012106379974937795001909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1037341404253316625196667939 1556012106379974937795001909)
                  ·
                    refine ⟨145876134973122650418281429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1556012106379974937795001909 145876134973122650418281429)
                    ·
                      refine ⟨3418971913432562119178471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 145876134973122650418281429 3418971913432562119178471)
                      ·
                        rfl

theorem cell23_6658424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 1, 5, 7].length) (baseStart_6658424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6658424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6658424 prefixEnd_6658424 := by exact prefixLift 6658424
  have htrace : WordTrace (prefixWord ++ tailWord_6658424) baseStart_6658424 baseEnd_6658424 := by
    simpa [prefixWord, tailWord_6658424, baseEnd_6658424] using wordTrace_append hprefix tailTrace_6658424
  have hstable : (prefixWord ++ tailWord_6658424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6658424).length < 2 ^ (prefixWord ++ tailWord_6658424).sum := by decide
  have hdescent : baseEnd_6658424 < baseStart_6658424 := by decide
  rcases family_descends (prefixWord ++ tailWord_6658424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6658429 : List Nat := [1, 4, 1, 1, 2, 3, 4, 2, 1, 2, 2]
def baseStart_6658429 : Nat := 118140960795 + 6658429 * 2 ^ 59
def prefixEnd_6658429 : Nat := 4983230072969 + 3 ^ 40 * 6658429 * 2
def baseEnd_6658429 : Nat := 3418974480835834599615949

theorem tailTrace_6658429 : CollatzResearch.WordTrace tailWord_6658429 prefixEnd_6658429 3418974480835834599615949 := by
  unfold tailWord_6658429
  simp only [CollatzResearch.WordTrace]
  refine ⟨242852856794656376983650341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161901904529770917989100227 242852856794656376983650341)
  ·
    refine ⟨45534910648998070684434439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 242852856794656376983650341 45534910648998070684434439)
    ·
      refine ⟨68302365973497106026651659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45534910648998070684434439 68302365973497106026651659)
      ·
        refine ⟨102453548960245659039977489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68302365973497106026651659 102453548960245659039977489)
        ·
          refine ⟨76840161720184244279983117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102453548960245659039977489 76840161720184244279983117)
          ·
            refine ⟨28815060645069091604993669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76840161720184244279983117 28815060645069091604993669)
            ·
              refine ⟨5402823870950454675936313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28815060645069091604993669 5402823870950454675936313)
              ·
                refine ⟨4052117903212841006952235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5402823870950454675936313 4052117903212841006952235)
                ·
                  refine ⟨6078176854819261510428353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4052117903212841006952235 6078176854819261510428353)
                  ·
                    refine ⟨4558632641114446132821265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6078176854819261510428353 4558632641114446132821265)
                    ·
                      refine ⟨3418974480835834599615949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4558632641114446132821265 3418974480835834599615949)
                      ·
                        rfl

theorem cell23_6658429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 4, 2, 1, 2, 2].length) (baseStart_6658429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6658429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6658429 prefixEnd_6658429 := by exact prefixLift 6658429
  have htrace : WordTrace (prefixWord ++ tailWord_6658429) baseStart_6658429 baseEnd_6658429 := by
    simpa [prefixWord, tailWord_6658429, baseEnd_6658429] using wordTrace_append hprefix tailTrace_6658429
  have hstable : (prefixWord ++ tailWord_6658429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6658429).length < 2 ^ (prefixWord ++ tailWord_6658429).sum := by decide
  have hdescent : baseEnd_6658429 < baseStart_6658429 := by decide
  rcases family_descends (prefixWord ++ tailWord_6658429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6658521 : List Nat := [1, 2, 1, 2, 4, 1, 1, 3, 1, 7]
def baseStart_6658521 : Nat := 118140960795 + 6658521 * 2 ^ 59
def prefixEnd_6658521 : Nat := 4983230072969 + 3 ^ 40 * 6658521 * 2
def baseEnd_6658521 : Nat := 1139673907018682746555175

theorem tailTrace_6658521 : CollatzResearch.WordTrace tailWord_6658521 prefixEnd_6658521 1139673907018682746555175 := by
  unfold tailWord_6658521
  simp only [CollatzResearch.WordTrace]
  refine ⟨242856212310323076695999417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161904141540215384463999611 242856212310323076695999417)
  ·
    refine ⟨182142159232742307521999563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242856212310323076695999417 182142159232742307521999563)
    ·
      refine ⟨273213238849113461282999345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182142159232742307521999563 273213238849113461282999345)
      ·
        refine ⟨204909929136835095962249509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 273213238849113461282999345 204909929136835095962249509)
        ·
          refine ⟨38420611713156580492921783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 204909929136835095962249509 38420611713156580492921783)
          ·
            refine ⟨57630917569734870739382675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38420611713156580492921783 57630917569734870739382675)
            ·
              refine ⟨86446376354602306109074013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57630917569734870739382675 86446376354602306109074013)
              ·
                refine ⟨32417391132975864790902755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86446376354602306109074013 32417391132975864790902755)
                ·
                  refine ⟨48626086699463797186354133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32417391132975864790902755 48626086699463797186354133)
                  ·
                    refine ⟨1139673907018682746555175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48626086699463797186354133 1139673907018682746555175)
                    ·
                      rfl

theorem cell23_6658521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 3, 1, 7].length) (baseStart_6658521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6658521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6658521 prefixEnd_6658521 := by exact prefixLift 6658521
  have htrace : WordTrace (prefixWord ++ tailWord_6658521) baseStart_6658521 baseEnd_6658521 := by
    simpa [prefixWord, tailWord_6658521, baseEnd_6658521] using wordTrace_append hprefix tailTrace_6658521
  have hstable : (prefixWord ++ tailWord_6658521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6658521).length < 2 ^ (prefixWord ++ tailWord_6658521).sum := by decide
  have hdescent : baseEnd_6658521 < baseStart_6658521 := by decide
  rcases family_descends (prefixWord ++ tailWord_6658521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6658538 : List Nat := [3, 1, 3, 1, 3, 1, 1, 1, 4, 5]
def baseStart_6658538 : Nat := 118140960795 + 6658538 * 2 ^ 59
def prefixEnd_6658538 : Nat := 4983230072969 + 3 ^ 40 * 6658538 * 2
def baseEnd_6658538 : Nat := 1139676816742391557717649

theorem tailTrace_6658538 : CollatzResearch.WordTrace tailWord_6658538 prefixEnd_6658538 1139676816742391557717649 := by
  unfold tailWord_6658538
  simp only [CollatzResearch.WordTrace]
  refine ⟨60714208087815372149842067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161904554900840992399578845 60714208087815372149842067)
  ·
    refine ⟨91071312131723058224763101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60714208087815372149842067 91071312131723058224763101)
    ·
      refine ⟨34151742049396146834286163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91071312131723058224763101 34151742049396146834286163)
      ·
        refine ⟨51227613074094220251429245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34151742049396146834286163 51227613074094220251429245)
        ·
          refine ⟨19210354902785332594285967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51227613074094220251429245 19210354902785332594285967)
          ·
            refine ⟨28815532354177998891428951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19210354902785332594285967 28815532354177998891428951)
            ·
              refine ⟨43223298531266998337143427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28815532354177998891428951 43223298531266998337143427)
              ·
                refine ⟨64834947796900497505715141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43223298531266998337143427 64834947796900497505715141)
                ·
                  refine ⟨12156552711918843282321589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64834947796900497505715141 12156552711918843282321589)
                  ·
                    refine ⟨1139676816742391557717649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12156552711918843282321589 1139676816742391557717649)
                    ·
                      rfl

theorem cell23_6658538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 1, 4, 5].length) (baseStart_6658538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6658538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6658538 prefixEnd_6658538 := by exact prefixLift 6658538
  have htrace : WordTrace (prefixWord ++ tailWord_6658538) baseStart_6658538 baseEnd_6658538 := by
    simpa [prefixWord, tailWord_6658538, baseEnd_6658538] using wordTrace_append hprefix tailTrace_6658538
  have hstable : (prefixWord ++ tailWord_6658538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6658538).length < 2 ^ (prefixWord ++ tailWord_6658538).sum := by decide
  have hdescent : baseEnd_6658538 < baseStart_6658538 := by decide
  rcases family_descends (prefixWord ++ tailWord_6658538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6658542 : List Nat := [4, 1, 2, 1, 2, 3, 3, 2, 5]
def baseStart_6658542 : Nat := 118140960795 + 6658542 * 2 ^ 59
def prefixEnd_6658542 : Nat := 4983230072969 + 3 ^ 40 * 6658542 * 2
def baseEnd_6658542 : Nat := 379892500461088073055881

theorem tailTrace_6658542 : CollatzResearch.WordTrace tailWord_6658542 prefixEnd_6658542 379892500461088073055881 := by
  unfold tailWord_6658542
  simp only [CollatzResearch.WordTrace]
  refine ⟨30357122280405874660314235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 161904652162164664855009253 30357122280405874660314235)
  ·
    refine ⟨45535683420608811990471353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30357122280405874660314235 45535683420608811990471353)
    ·
      refine ⟨34151762565456608992853515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45535683420608811990471353 34151762565456608992853515)
      ·
        refine ⟨51227643848184913489280273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34151762565456608992853515 51227643848184913489280273)
        ·
          refine ⟨38420732886138685116960205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51227643848184913489280273 38420732886138685116960205)
          ·
            refine ⟨14407774832302006918860077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38420732886138685116960205 14407774832302006918860077)
            ·
              refine ⟨5402915562113252594572529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14407774832302006918860077 5402915562113252594572529)
              ·
                refine ⟨4052186671584939445929397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5402915562113252594572529 4052186671584939445929397)
                ·
                  refine ⟨379892500461088073055881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4052186671584939445929397 379892500461088073055881)
                  ·
                    rfl

theorem cell23_6658542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 3, 2, 5].length) (baseStart_6658542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6658542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6658542 prefixEnd_6658542 := by exact prefixLift 6658542
  have htrace : WordTrace (prefixWord ++ tailWord_6658542) baseStart_6658542 baseEnd_6658542 := by
    simpa [prefixWord, tailWord_6658542, baseEnd_6658542] using wordTrace_append hprefix tailTrace_6658542
  have hstable : (prefixWord ++ tailWord_6658542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6658542).length < 2 ^ (prefixWord ++ tailWord_6658542).sum := by decide
  have hdescent : baseEnd_6658542 < baseStart_6658542 := by decide
  rcases family_descends (prefixWord ++ tailWord_6658542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6658568 : List Nat := [2, 1, 3, 2, 1, 1, 1, 3, 5, 4]
def baseStart_6658568 : Nat := 118140960795 + 6658568 * 2 ^ 59
def prefixEnd_6658568 : Nat := 4983230072969 + 3 ^ 40 * 6658568 * 2
def baseEnd_6658568 : Nat := 1139681951548936518592603

theorem tailTrace_6658568 : CollatzResearch.WordTrace tailWord_6658568 prefixEnd_6658568 1139681951548936518592603 := by
  unfold tailWord_6658568
  simp only [CollatzResearch.WordTrace]
  refine ⟨121428963270576401861480179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161905284360768535815306905 121428963270576401861480179)
  ·
    refine ⟨182143444905864602792220269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121428963270576401861480179 182143444905864602792220269)
    ·
      refine ⟨68303791839699226047082601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182143444905864602792220269 68303791839699226047082601)
      ·
        refine ⟨51227843879774419535311951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68303791839699226047082601 51227843879774419535311951)
        ·
          refine ⟨76841765819661629302967927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51227843879774419535311951 76841765819661629302967927)
          ·
            refine ⟨115262648729492443954451891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76841765819661629302967927 115262648729492443954451891)
            ·
              refine ⟨172893973094238665931677837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115262648729492443954451891 172893973094238665931677837)
              ·
                refine ⟨64835239910339499724379189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 172893973094238665931677837 64835239910339499724379189)
                ·
                  refine ⟨6078303741594328099160549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 64835239910339499724379189 6078303741594328099160549)
                  ·
                    refine ⟨1139681951548936518592603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6078303741594328099160549 1139681951548936518592603)
                    ·
                      rfl

theorem cell23_6658568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 3, 5, 4].length) (baseStart_6658568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6658568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6658568 prefixEnd_6658568 := by exact prefixLift 6658568
  have htrace : WordTrace (prefixWord ++ tailWord_6658568) baseStart_6658568 baseEnd_6658568 := by
    simpa [prefixWord, tailWord_6658568, baseEnd_6658568] using wordTrace_append hprefix tailTrace_6658568
  have hstable : (prefixWord ++ tailWord_6658568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6658568).length < 2 ^ (prefixWord ++ tailWord_6658568).sum := by decide
  have hdescent : baseEnd_6658568 < baseStart_6658568 := by decide
  rcases family_descends (prefixWord ++ tailWord_6658568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6658595 : List Nat := [1, 1, 1, 4, 4, 1, 2, 2, 2, 2, 3]
def baseStart_6658595 : Nat := 118140960795 + 6658595 * 2 ^ 59
def prefixEnd_6658595 : Nat := 4983230072969 + 3 ^ 40 * 6658595 * 2
def baseEnd_6658595 : Nat := 3419059718624480950140185

theorem tailTrace_6658595 : CollatzResearch.WordTrace tailWord_6658595 prefixEnd_6658595 3419059718624480950140185 := by
  unfold tailWord_6658595
  simp only [CollatzResearch.WordTrace]
  refine ⟨242858911312054987334193239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161905940874703324889462159 242858911312054987334193239)
  ·
    refine ⟨364288366968082481001289859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242858911312054987334193239 364288366968082481001289859)
    ·
      refine ⟨546432550452123721501934789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 364288366968082481001289859 546432550452123721501934789)
      ·
        refine ⟨102456103209773197781612773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 546432550452123721501934789 102456103209773197781612773)
        ·
          refine ⟨19210519351832474584052395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102456103209773197781612773 19210519351832474584052395)
          ·
            refine ⟨28815779027748711876078593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19210519351832474584052395 28815779027748711876078593)
            ·
              refine ⟨21611834270811533907058945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28815779027748711876078593 21611834270811533907058945)
              ·
                refine ⟨16208875703108650430294209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21611834270811533907058945 16208875703108650430294209)
                ·
                  refine ⟨12156656777331487822720657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16208875703108650430294209 12156656777331487822720657)
                  ·
                    refine ⟨9117492582998615867040493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12156656777331487822720657 9117492582998615867040493)
                    ·
                      refine ⟨3419059718624480950140185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9117492582998615867040493 3419059718624480950140185)
                      ·
                        rfl

theorem cell23_6658595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 2, 2, 2, 3].length) (baseStart_6658595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6658595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6658595 prefixEnd_6658595 := by exact prefixLift 6658595
  have htrace : WordTrace (prefixWord ++ tailWord_6658595) baseStart_6658595 baseEnd_6658595 := by
    simpa [prefixWord, tailWord_6658595, baseEnd_6658595] using wordTrace_append hprefix tailTrace_6658595
  have hstable : (prefixWord ++ tailWord_6658595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6658595).length < 2 ^ (prefixWord ++ tailWord_6658595).sum := by decide
  have hdescent : baseEnd_6658595 < baseStart_6658595 := by decide
  rcases family_descends (prefixWord ++ tailWord_6658595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6658668 : List Nat := [2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 5]
def baseStart_6658668 : Nat := 118140960795 + 6658668 * 2 ^ 59
def prefixEnd_6658668 : Nat := 4983230072969 + 3 ^ 40 * 6658668 * 2
def baseEnd_6658668 : Nat := 3419097202712259164527349

theorem tailTrace_6658668 : CollatzResearch.WordTrace tailWord_6658668 prefixEnd_6658668 3419097202712259164527349 := by
  unfold tailWord_6658668
  simp only [CollatzResearch.WordTrace]
  refine ⟨121430786920395260400800329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161907715893860347201067105 121430786920395260400800329)
  ·
    refine ⟨91073090190296445300600247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121430786920395260400800329 91073090190296445300600247)
    ·
      refine ⟨136609635285444667950900371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91073090190296445300600247 136609635285444667950900371)
      ·
        refine ⟨204914452928167001926350557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136609635285444667950900371 204914452928167001926350557)
        ·
          refine ⟨76842919848062625722381459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 204914452928167001926350557 76842919848062625722381459)
          ·
            refine ⟨115264379772093938583572189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76842919848062625722381459 115264379772093938583572189)
            ·
              refine ⟨43224142414535226968839571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 115264379772093938583572189 43224142414535226968839571)
              ·
                refine ⟨64836213621802840453259357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43224142414535226968839571 64836213621802840453259357)
                ·
                  refine ⟨24313580108176065169972259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64836213621802840453259357 24313580108176065169972259)
                  ·
                    refine ⟨36470370162264097754958389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24313580108176065169972259 36470370162264097754958389)
                    ·
                      refine ⟨3419097202712259164527349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36470370162264097754958389 3419097202712259164527349)
                      ·
                        rfl

theorem cell23_6658668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 5].length) (baseStart_6658668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6658668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6658668 prefixEnd_6658668 := by exact prefixLift 6658668
  have htrace : WordTrace (prefixWord ++ tailWord_6658668) baseStart_6658668 baseEnd_6658668 := by
    simpa [prefixWord, tailWord_6658668, baseEnd_6658668] using wordTrace_append hprefix tailTrace_6658668
  have hstable : (prefixWord ++ tailWord_6658668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6658668).length < 2 ^ (prefixWord ++ tailWord_6658668).sum := by decide
  have hdescent : baseEnd_6658668 < baseStart_6658668 := by decide
  rcases family_descends (prefixWord ++ tailWord_6658668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6658688 : List Nat := [2, 1, 1, 2, 1, 6, 1, 9]
def baseStart_6658688 : Nat := 118140960795 + 6658688 * 2 ^ 59
def prefixEnd_6658688 : Nat := 4983230072969 + 3 ^ 40 * 6658688 * 2
def baseEnd_6658688 : Nat := 126633610086124040232491

theorem tailTrace_6658688 : CollatzResearch.WordTrace tailWord_6658688 prefixEnd_6658688 126633610086124040232491 := by
  unfold tailWord_6658688
  simp only [CollatzResearch.WordTrace]
  refine ⟨121431151650359032108664359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161908202200478709478219145 121431151650359032108664359)
  ·
    refine ⟨182146727475538548162996539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121431151650359032108664359 182146727475538548162996539)
    ·
      refine ⟨273220091213307822244494809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182146727475538548162996539 273220091213307822244494809)
      ·
        refine ⟨204915068409980866683371107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 273220091213307822244494809 204915068409980866683371107)
        ·
          refine ⟨307372602614971300025056661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204915068409980866683371107 307372602614971300025056661)
          ·
            refine ⟨14408090747576779688674531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 307372602614971300025056661 14408090747576779688674531)
            ·
              refine ⟨21612136121365169533011797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14408090747576779688674531 21612136121365169533011797)
              ·
                refine ⟨126633610086124040232491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21612136121365169533011797 126633610086124040232491)
                ·
                  rfl

theorem cell23_6658688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 9].length) (baseStart_6658688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6658688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6658688 prefixEnd_6658688 := by exact prefixLift 6658688
  have htrace : WordTrace (prefixWord ++ tailWord_6658688) baseStart_6658688 baseEnd_6658688 := by
    simpa [prefixWord, tailWord_6658688, baseEnd_6658688] using wordTrace_append hprefix tailTrace_6658688
  have hstable : (prefixWord ++ tailWord_6658688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6658688).length < 2 ^ (prefixWord ++ tailWord_6658688).sum := by decide
  have hdescent : baseEnd_6658688 < baseStart_6658688 := by decide
  rcases family_descends (prefixWord ++ tailWord_6658688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6658699 : List Nat := [1, 1, 1, 1, 4, 1, 2, 7, 1, 2, 2]
def baseStart_6658699 : Nat := 118140960795 + 6658699 * 2 ^ 59
def prefixEnd_6658699 : Nat := 4983230072969 + 3 ^ 40 * 6658699 * 2
def baseEnd_6658699 : Nat := 3419113120612548543239707

theorem tailTrace_6658699 : CollatzResearch.WordTrace tailWord_6658699 prefixEnd_6658699 3419113120612548543239707 := by
  unfold tailWord_6658699
  simp only [CollatzResearch.WordTrace]
  refine ⟨242862704503678213095979151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161908469669118808730652767 242862704503678213095979151)
  ·
    refine ⟨364294056755517319643968727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242862704503678213095979151 364294056755517319643968727)
    ·
      refine ⟨546441085133275979465953091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 364294056755517319643968727 546441085133275979465953091)
      ·
        refine ⟨819661627699913969198929637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 546441085133275979465953091 819661627699913969198929637)
        ·
          refine ⟨153686555193733869224799307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 819661627699913969198929637 153686555193733869224799307)
          ·
            refine ⟨230529832790600803837198961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153686555193733869224799307 230529832790600803837198961)
            ·
              refine ⟨172897374592950602877899221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 230529832790600803837198961 172897374592950602877899221)
              ·
                refine ⟨4052282217022279754950763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 172897374592950602877899221 4052282217022279754950763)
                ·
                  refine ⟨6078423325533419632426145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4052282217022279754950763 6078423325533419632426145)
                  ·
                    refine ⟨4558817494150064724319609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6078423325533419632426145 4558817494150064724319609)
                    ·
                      refine ⟨3419113120612548543239707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4558817494150064724319609 3419113120612548543239707)
                      ·
                        rfl

theorem cell23_6658699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 7, 1, 2, 2].length) (baseStart_6658699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6658699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6658699 prefixEnd_6658699 := by exact prefixLift 6658699
  have htrace : WordTrace (prefixWord ++ tailWord_6658699) baseStart_6658699 baseEnd_6658699 := by
    simpa [prefixWord, tailWord_6658699, baseEnd_6658699] using wordTrace_append hprefix tailTrace_6658699
  have hstable : (prefixWord ++ tailWord_6658699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6658699).length < 2 ^ (prefixWord ++ tailWord_6658699).sum := by decide
  have hdescent : baseEnd_6658699 < baseStart_6658699 := by decide
  rcases family_descends (prefixWord ++ tailWord_6658699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6658702 : List Nat := [4, 1, 1, 3, 1, 1, 1, 5, 1, 2, 3]
def baseStart_6658702 : Nat := 118140960795 + 6658702 * 2 ^ 59
def prefixEnd_6658702 : Nat := 4983230072969 + 3 ^ 40 * 6658702 * 2
def baseEnd_6658702 : Nat := 3419114661054512031502193

theorem tailTrace_6658702 : CollatzResearch.WordTrace tailWord_6658702 prefixEnd_6658702 3419114661054512031502193 := by
  unfold tailWord_6658702
  simp only [CollatzResearch.WordTrace]
  refine ⟨30357851740333418076042295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 161908542615111563072225573 30357851740333418076042295)
  ·
    refine ⟨45536777610500127114063443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30357851740333418076042295 45536777610500127114063443)
    ·
      refine ⟨68305166415750190671095165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45536777610500127114063443 68305166415750190671095165)
      ·
        refine ⟨25614437405906321501660687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68305166415750190671095165 25614437405906321501660687)
        ·
          refine ⟨38421656108859482252491031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25614437405906321501660687 38421656108859482252491031)
          ·
            refine ⟨57632484163289223378736547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38421656108859482252491031 57632484163289223378736547)
            ·
              refine ⟨86448726244933835068104821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57632484163289223378736547 86448726244933835068104821)
              ·
                refine ⟨8104568085462547037634827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 86448726244933835068104821 8104568085462547037634827)
                ·
                  refine ⟨12156852128193820556452241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8104568085462547037634827 12156852128193820556452241)
                  ·
                    refine ⟨9117639096145365417339181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12156852128193820556452241 9117639096145365417339181)
                    ·
                      refine ⟨3419114661054512031502193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9117639096145365417339181 3419114661054512031502193)
                      ·
                        rfl

theorem cell23_6658702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 5, 1, 2, 3].length) (baseStart_6658702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6658702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6658702 prefixEnd_6658702 := by exact prefixLift 6658702
  have htrace : WordTrace (prefixWord ++ tailWord_6658702) baseStart_6658702 baseEnd_6658702 := by
    simpa [prefixWord, tailWord_6658702, baseEnd_6658702] using wordTrace_append hprefix tailTrace_6658702
  have hstable : (prefixWord ++ tailWord_6658702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6658702).length < 2 ^ (prefixWord ++ tailWord_6658702).sum := by decide
  have hdescent : baseEnd_6658702 < baseStart_6658702 := by decide
  rcases family_descends (prefixWord ++ tailWord_6658702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6658716 : List Nat := [2, 2, 3, 2, 2, 3, 1, 1, 3, 2, 2]
def baseStart_6658716 : Nat := 118140960795 + 6658716 * 2 ^ 59
def prefixEnd_6658716 : Nat := 4983230072969 + 3 ^ 40 * 6658716 * 2
def baseEnd_6658716 : Nat := 3419121849783674976727129

theorem tailTrace_6658716 : CollatzResearch.WordTrace tailWord_6658716 prefixEnd_6658716 3419121849783674976727129 := by
  unfold tailWord_6658716
  simp only [CollatzResearch.WordTrace]
  refine ⟨121431662272308312499674001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161908883029744416666232001 121431662272308312499674001)
  ·
    refine ⟨91073746704231234374755501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121431662272308312499674001 91073746704231234374755501)
    ·
      refine ⟨34152655014086712890533313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91073746704231234374755501 34152655014086712890533313)
      ·
        refine ⟨25614491260565034667899985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34152655014086712890533313 25614491260565034667899985)
        ·
          refine ⟨19210868445423776000924989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25614491260565034667899985 19210868445423776000924989)
          ·
            refine ⟨7204075667033916000346871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19210868445423776000924989 7204075667033916000346871)
            ·
              refine ⟨10806113500550874000520307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7204075667033916000346871 10806113500550874000520307)
              ·
                refine ⟨16209170250826311000780461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10806113500550874000520307 16209170250826311000780461)
                ·
                  refine ⟨6078438844059866625292673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16209170250826311000780461 6078438844059866625292673)
                  ·
                    refine ⟨4558829133044899968969505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6078438844059866625292673 4558829133044899968969505)
                    ·
                      refine ⟨3419121849783674976727129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4558829133044899968969505 3419121849783674976727129)
                      ·
                        rfl

theorem cell23_6658716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 1, 1, 3, 2, 2].length) (baseStart_6658716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6658716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6658716 prefixEnd_6658716 := by exact prefixLift 6658716
  have htrace : WordTrace (prefixWord ++ tailWord_6658716) baseStart_6658716 baseEnd_6658716 := by
    simpa [prefixWord, tailWord_6658716, baseEnd_6658716] using wordTrace_append hprefix tailTrace_6658716
  have hstable : (prefixWord ++ tailWord_6658716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6658716).length < 2 ^ (prefixWord ++ tailWord_6658716).sum := by decide
  have hdescent : baseEnd_6658716 < baseStart_6658716 := by decide
  rcases family_descends (prefixWord ++ tailWord_6658716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6658725 : List Nat := [1, 3, 1, 2, 1, 2, 1, 1, 2, 7, 2]
def baseStart_6658725 : Nat := 118140960795 + 6658725 * 2 ^ 59
def prefixEnd_6658725 : Nat := 4983230072969 + 3 ^ 40 * 6658725 * 2
def baseEnd_6658725 : Nat := 3419126471109565441514587

theorem tailTrace_6658725 : CollatzResearch.WordTrace tailWord_6658725 prefixEnd_6658725 3419126471109565441514587 := by
  unfold tailWord_6658725
  simp only [CollatzResearch.WordTrace]
  refine ⟨242863652801584019536425629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161909101867722679690950419 242863652801584019536425629)
  ·
    refine ⟨91073869800594007326159611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 242863652801584019536425629 91073869800594007326159611)
    ·
      refine ⟨136610804700891010989239417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91073869800594007326159611 136610804700891010989239417)
      ·
        refine ⟨102458103525668258241929563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136610804700891010989239417 102458103525668258241929563)
        ·
          refine ⟨153687155288502387362894345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102458103525668258241929563 153687155288502387362894345)
          ·
            refine ⟨115265366466376790522170759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153687155288502387362894345 115265366466376790522170759)
            ·
              refine ⟨172898049699565185783256139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115265366466376790522170759 172898049699565185783256139)
              ·
                refine ⟨259347074549347778674884209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 172898049699565185783256139 259347074549347778674884209)
                ·
                  refine ⟨194510305912010834006163157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 259347074549347778674884209 194510305912010834006163157)
                  ·
                    refine ⟨4558835294812753922019449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 194510305912010834006163157 4558835294812753922019449)
                    ·
                      refine ⟨3419126471109565441514587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4558835294812753922019449 3419126471109565441514587)
                      ·
                        rfl

theorem cell23_6658725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 2, 7, 2].length) (baseStart_6658725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6658725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6658725 prefixEnd_6658725 := by exact prefixLift 6658725
  have htrace : WordTrace (prefixWord ++ tailWord_6658725) baseStart_6658725 baseEnd_6658725 := by
    simpa [prefixWord, tailWord_6658725, baseEnd_6658725] using wordTrace_append hprefix tailTrace_6658725
  have hstable : (prefixWord ++ tailWord_6658725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6658725).length < 2 ^ (prefixWord ++ tailWord_6658725).sum := by decide
  have hdescent : baseEnd_6658725 < baseStart_6658725 := by decide
  rcases family_descends (prefixWord ++ tailWord_6658725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6658738 : List Nat := [3, 2, 1, 1, 1, 2, 1, 1, 1, 2, 8]
def baseStart_6658738 : Nat := 118140960795 + 6658738 * 2 ^ 59
def prefixEnd_6658738 : Nat := 4983230072969 + 3 ^ 40 * 6658738 * 2
def baseEnd_6658738 : Nat := 3419133146358073890652027

theorem tailTrace_6658738 : CollatzResearch.WordTrace tailWord_6658738 prefixEnd_6658738 3419133146358073890652027 := by
  unfold tailWord_6658738
  simp only [CollatzResearch.WordTrace]
  refine ⟨60716031737634230689162217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161909417967024615171099245 60716031737634230689162217)
  ·
    refine ⟨45537023803225673016871663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60716031737634230689162217 45537023803225673016871663)
    ·
      refine ⟨68305535704838509525307495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45537023803225673016871663 68305535704838509525307495)
      ·
        refine ⟨102458303557257764287961243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68305535704838509525307495 102458303557257764287961243)
        ·
          refine ⟨153687455335886646431941865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102458303557257764287961243 153687455335886646431941865)
          ·
            refine ⟨115265591501914984823956399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153687455335886646431941865 115265591501914984823956399)
            ·
              refine ⟨172898387252872477235934599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115265591501914984823956399 172898387252872477235934599)
              ·
                refine ⟨259347580879308715853901899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 172898387252872477235934599 259347580879308715853901899)
                ·
                  refine ⟨389021371318963073780852849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 259347580879308715853901899 389021371318963073780852849)
                  ·
                    refine ⟨291766028489222305335639637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 389021371318963073780852849 291766028489222305335639637)
                    ·
                      refine ⟨3419133146358073890652027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 291766028489222305335639637 3419133146358073890652027)
                      ·
                        rfl

theorem cell23_6658738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 1, 2, 8].length) (baseStart_6658738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6658738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6658738 prefixEnd_6658738 := by exact prefixLift 6658738
  have htrace : WordTrace (prefixWord ++ tailWord_6658738) baseStart_6658738 baseEnd_6658738 := by
    simpa [prefixWord, tailWord_6658738, baseEnd_6658738] using wordTrace_append hprefix tailTrace_6658738
  have hstable : (prefixWord ++ tailWord_6658738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6658738).length < 2 ^ (prefixWord ++ tailWord_6658738).sum := by decide
  have hdescent : baseEnd_6658738 < baseStart_6658738 := by decide
  rcases family_descends (prefixWord ++ tailWord_6658738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6658753 : List Nat := [1, 2, 6, 2, 1, 1, 3, 1, 1, 2, 3]
def baseStart_6658753 : Nat := 118140960795 + 6658753 * 2 ^ 59
def prefixEnd_6658753 : Nat := 4983230072969 + 3 ^ 40 * 6658753 * 2
def baseEnd_6658753 : Nat := 3419140848567891331964459

theorem tailTrace_6658753 : CollatzResearch.WordTrace tailWord_6658753 prefixEnd_6658753 3419140848567891331964459 := by
  unfold tailWord_6658753
  simp only [CollatzResearch.WordTrace]
  refine ⟨242864674045482580318444913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161909782696988386878963275 242864674045482580318444913)
  ·
    refine ⟨182148505534111935238833685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242864674045482580318444913 182148505534111935238833685)
    ·
      refine ⟨8538211196911496964320329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 182148505534111935238833685 8538211196911496964320329)
      ·
        refine ⟨6403658397683622723240247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8538211196911496964320329 6403658397683622723240247)
        ·
          refine ⟨9605487596525434084860371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6403658397683622723240247 9605487596525434084860371)
          ·
            refine ⟨14408231394788151127290557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9605487596525434084860371 14408231394788151127290557)
            ·
              refine ⟨5403086773045556672733959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14408231394788151127290557 5403086773045556672733959)
              ·
                refine ⟨8104630159568335009100939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5403086773045556672733959 8104630159568335009100939)
                ·
                  refine ⟨12156945239352502513651409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8104630159568335009100939 12156945239352502513651409)
                  ·
                    refine ⟨9117708929514376885238557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12156945239352502513651409 9117708929514376885238557)
                    ·
                      refine ⟨3419140848567891331964459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9117708929514376885238557 3419140848567891331964459)
                      ·
                        rfl

theorem cell23_6658753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_6658753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6658753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6658753 prefixEnd_6658753 := by exact prefixLift 6658753
  have htrace : WordTrace (prefixWord ++ tailWord_6658753) baseStart_6658753 baseEnd_6658753 := by
    simpa [prefixWord, tailWord_6658753, baseEnd_6658753] using wordTrace_append hprefix tailTrace_6658753
  have hstable : (prefixWord ++ tailWord_6658753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6658753).length < 2 ^ (prefixWord ++ tailWord_6658753).sum := by decide
  have hdescent : baseEnd_6658753 < baseStart_6658753 := by decide
  rcases family_descends (prefixWord ++ tailWord_6658753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6658775 : List Nat := [1, 1, 3, 2, 1, 4, 1, 1, 2, 4, 3]
def baseStart_6658775 : Nat := 118140960795 + 6658775 * 2 ^ 59
def prefixEnd_6658775 : Nat := 4983230072969 + 3 ^ 40 * 6658775 * 2
def baseEnd_6658775 : Nat := 3419152145142290245889357

theorem tailTrace_6658775 : CollatzResearch.WordTrace tailWord_6658775 prefixEnd_6658775 3419152145142290245889357 := by
  unfold tailWord_6658775
  simp only [CollatzResearch.WordTrace]
  refine ⟨242865476451402878075745779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161910317634268585383830519 242865476451402878075745779)
  ·
    refine ⟨364298214677104317113618669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242865476451402878075745779 364298214677104317113618669)
    ·
      refine ⟨136611830503914118917607001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 364298214677104317113618669 136611830503914118917607001)
      ·
        refine ⟨102458872877935589188205251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136611830503914118917607001 102458872877935589188205251)
        ·
          refine ⟨153688309316903383782307877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102458872877935589188205251 153688309316903383782307877)
          ·
            refine ⟨28816557996919384459182727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 153688309316903383782307877 28816557996919384459182727)
            ·
              refine ⟨43224836995379076688774091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28816557996919384459182727 43224836995379076688774091)
              ·
                refine ⟨64837255493068615033161137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43224836995379076688774091 64837255493068615033161137)
                ·
                  refine ⟨48627941619801461274870853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64837255493068615033161137 48627941619801461274870853)
                  ·
                    refine ⟨9117739053712773989038285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48627941619801461274870853 9117739053712773989038285)
                    ·
                      refine ⟨3419152145142290245889357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9117739053712773989038285 3419152145142290245889357)
                      ·
                        rfl

theorem cell23_6658775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 1, 2, 4, 3].length) (baseStart_6658775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6658775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6658775 prefixEnd_6658775 := by exact prefixLift 6658775
  have htrace : WordTrace (prefixWord ++ tailWord_6658775) baseStart_6658775 baseEnd_6658775 := by
    simpa [prefixWord, tailWord_6658775, baseEnd_6658775] using wordTrace_append hprefix tailTrace_6658775
  have hstable : (prefixWord ++ tailWord_6658775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6658775).length < 2 ^ (prefixWord ++ tailWord_6658775).sum := by decide
  have hdescent : baseEnd_6658775 < baseStart_6658775 := by decide
  rcases family_descends (prefixWord ++ tailWord_6658775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6658785 : List Nat := [1, 2, 3, 1, 4, 1, 1, 1, 1, 4, 4]
def baseStart_6658785 : Nat := 118140960795 + 6658785 * 2 ^ 59
def prefixEnd_6658785 : Nat := 4983230072969 + 3 ^ 40 * 6658785 * 2
def baseEnd_6658785 : Nat := 3419157279948835206764311

theorem tailTrace_6658785 : CollatzResearch.WordTrace tailWord_6658785 prefixEnd_6658785 3419157279948835206764311 := by
  unfold tailWord_6658785
  simp only [CollatzResearch.WordTrace]
  refine ⟨242865841181366649783609809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161910560787577766522406539 242865841181366649783609809)
  ·
    refine ⟨182149380886024987337707357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242865841181366649783609809 182149380886024987337707357)
    ·
      refine ⟨68306017832259370251640259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182149380886024987337707357 68306017832259370251640259)
      ·
        refine ⟨102459026748389055377460389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68306017832259370251640259 102459026748389055377460389)
        ·
          refine ⟨19211067515322947883273823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102459026748389055377460389 19211067515322947883273823)
          ·
            refine ⟨28816601272984421824910735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19211067515322947883273823 28816601272984421824910735)
            ·
              refine ⟨43224901909476632737366103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28816601272984421824910735 43224901909476632737366103)
              ·
                refine ⟨64837352864214949106049155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43224901909476632737366103 64837352864214949106049155)
                ·
                  refine ⟨97256029296322423659073733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64837352864214949106049155 97256029296322423659073733)
                  ·
                    refine ⟨18235505493060454436076325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 97256029296322423659073733 18235505493060454436076325)
                    ·
                      refine ⟨3419157279948835206764311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18235505493060454436076325 3419157279948835206764311)
                      ·
                        rfl

theorem cell23_6658785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 1, 1, 4, 4].length) (baseStart_6658785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6658785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6658785 prefixEnd_6658785 := by exact prefixLift 6658785
  have htrace : WordTrace (prefixWord ++ tailWord_6658785) baseStart_6658785 baseEnd_6658785 := by
    simpa [prefixWord, tailWord_6658785, baseEnd_6658785] using wordTrace_append hprefix tailTrace_6658785
  have hstable : (prefixWord ++ tailWord_6658785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6658785).length < 2 ^ (prefixWord ++ tailWord_6658785).sum := by decide
  have hdescent : baseEnd_6658785 < baseStart_6658785 := by decide
  rcases family_descends (prefixWord ++ tailWord_6658785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6658789 : List Nat := [1, 3, 1, 4, 1, 3, 2, 1, 1, 4, 2]
def baseStart_6658789 : Nat := 118140960795 + 6658789 * 2 ^ 59
def prefixEnd_6658789 : Nat := 4983230072969 + 3 ^ 40 * 6658789 * 2
def baseEnd_6658789 : Nat := 3419159333871453191114293

theorem tailTrace_6658789 : CollatzResearch.WordTrace tailWord_6658789 prefixEnd_6658789 3419159333871453191114293 := by
  unfold tailWord_6658789
  simp only [CollatzResearch.WordTrace]
  refine ⟨242865987073352158466755421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161910658048901438977836947 242865987073352158466755421)
  ·
    refine ⟨91074745152507059425033283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 242865987073352158466755421 91074745152507059425033283)
    ·
      refine ⟨136612117728760589137549925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91074745152507059425033283 136612117728760589137549925)
      ·
        refine ⟨25614772074142610463290611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 136612117728760589137549925 25614772074142610463290611)
        ·
          refine ⟨38422158111213915694935917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25614772074142610463290611 38422158111213915694935917)
          ·
            refine ⟨14408309291705218385600969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38422158111213915694935917 14408309291705218385600969)
            ·
              refine ⟨10806231968778913789200727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14408309291705218385600969 10806231968778913789200727)
              ·
                refine ⟨16209347953168370683801091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10806231968778913789200727 16209347953168370683801091)
                ·
                  refine ⟨24314021929752556025701637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16209347953168370683801091 24314021929752556025701637)
                  ·
                    refine ⟨4558879111828604254819057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24314021929752556025701637 4558879111828604254819057)
                    ·
                      refine ⟨3419159333871453191114293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4558879111828604254819057 3419159333871453191114293)
                      ·
                        rfl

theorem cell23_6658789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 2, 1, 1, 4, 2].length) (baseStart_6658789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6658789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6658789 prefixEnd_6658789 := by exact prefixLift 6658789
  have htrace : WordTrace (prefixWord ++ tailWord_6658789) baseStart_6658789 baseEnd_6658789 := by
    simpa [prefixWord, tailWord_6658789, baseEnd_6658789] using wordTrace_append hprefix tailTrace_6658789
  have hstable : (prefixWord ++ tailWord_6658789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6658789).length < 2 ^ (prefixWord ++ tailWord_6658789).sum := by decide
  have hdescent : baseEnd_6658789 < baseStart_6658789 := by decide
  rcases family_descends (prefixWord ++ tailWord_6658789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6658812 : List Nat := [2, 2, 2, 1, 3, 2, 1, 5, 5]
def baseStart_6658812 : Nat := 118140960795 + 6658812 * 2 ^ 59
def prefixEnd_6658812 : Nat := 4983230072969 + 3 ^ 40 * 6658812 * 2
def baseEnd_6658812 : Nat := 379907904880722955680743

theorem tailTrace_6658812 : CollatzResearch.WordTrace tailWord_6658812 prefixEnd_6658812 379907904880722955680743 := by
  unfold tailWord_6658812
  simp only [CollatzResearch.WordTrace]
  refine ⟨121433412976134416697421345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161911217301512555596561793 121433412976134416697421345)
  ·
    refine ⟨91075059732100812523066009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121433412976134416697421345 91075059732100812523066009)
    ·
      refine ⟨68306294799075609392299507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91075059732100812523066009 68306294799075609392299507)
      ·
        refine ⟨102459442198613414088449261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68306294799075609392299507 102459442198613414088449261)
        ·
          refine ⟨38422290824480030283168473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102459442198613414088449261 38422290824480030283168473)
          ·
            refine ⟨28816718118360022712376355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38422290824480030283168473 28816718118360022712376355)
            ·
              refine ⟨43225077177540034068564533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28816718118360022712376355 43225077177540034068564533)
              ·
                refine ⟨4052350985394378193927925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43225077177540034068564533 4052350985394378193927925)
                ·
                  refine ⟨379907904880722955680743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4052350985394378193927925 379907904880722955680743)
                  ·
                    rfl

theorem cell23_6658812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 5, 5].length) (baseStart_6658812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6658812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6658812 prefixEnd_6658812 := by exact prefixLift 6658812
  have htrace : WordTrace (prefixWord ++ tailWord_6658812) baseStart_6658812 baseEnd_6658812 := by
    simpa [prefixWord, tailWord_6658812, baseEnd_6658812] using wordTrace_append hprefix tailTrace_6658812
  have hstable : (prefixWord ++ tailWord_6658812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6658812).length < 2 ^ (prefixWord ++ tailWord_6658812).sum := by decide
  have hdescent : baseEnd_6658812 < baseStart_6658812 := by decide
  rcases family_descends (prefixWord ++ tailWord_6658812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6658823 : List Nat := [1, 1, 4, 4, 1, 3, 1, 2, 2, 2, 2]
def baseStart_6658823 : Nat := 118140960795 + 6658823 * 2 ^ 59
def prefixEnd_6658823 : Nat := 4983230072969 + 3 ^ 40 * 6658823 * 2
def baseEnd_6658823 : Nat := 3419176792213706058089137

theorem tailTrace_6658823 : CollatzResearch.WordTrace tailWord_6658823 prefixEnd_6658823 3419176792213706058089137 := by
  unfold tailWord_6658823
  simp only [CollatzResearch.WordTrace]
  refine ⟨242867227155228982273493123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161911484770152654848995415 242867227155228982273493123)
  ·
    refine ⟨364300840732843473410239685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242867227155228982273493123 364300840732843473410239685)
    ·
      refine ⟨68306407637408151264419941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 364300840732843473410239685 68306407637408151264419941)
      ·
        refine ⟨12807451432014028362078739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68306407637408151264419941 12807451432014028362078739)
        ·
          refine ⟨19211177148021042543118109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12807451432014028362078739 19211177148021042543118109)
          ·
            refine ⟨7204191430507890953669291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19211177148021042543118109 7204191430507890953669291)
            ·
              refine ⟨10806287145761836430503937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7204191430507890953669291 10806287145761836430503937)
              ·
                refine ⟨8104715359321377322877953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10806287145761836430503937 8104715359321377322877953)
                ·
                  refine ⟨6078536519491032992158465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8104715359321377322877953 6078536519491032992158465)
                  ·
                    refine ⟨4558902389618274744118849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6078536519491032992158465 4558902389618274744118849)
                    ·
                      refine ⟨3419176792213706058089137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4558902389618274744118849 3419176792213706058089137)
                      ·
                        rfl

theorem cell23_6658823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 1, 2, 2, 2, 2].length) (baseStart_6658823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6658823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6658823 prefixEnd_6658823 := by exact prefixLift 6658823
  have htrace : WordTrace (prefixWord ++ tailWord_6658823) baseStart_6658823 baseEnd_6658823 := by
    simpa [prefixWord, tailWord_6658823, baseEnd_6658823] using wordTrace_append hprefix tailTrace_6658823
  have hstable : (prefixWord ++ tailWord_6658823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6658823).length < 2 ^ (prefixWord ++ tailWord_6658823).sum := by decide
  have hdescent : baseEnd_6658823 < baseStart_6658823 := by decide
  rcases family_descends (prefixWord ++ tailWord_6658823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6658825 : List Nat := [1, 2, 1, 1, 3, 2, 2, 4, 2, 5]
def baseStart_6658825 : Nat := 118140960795 + 6658825 * 2 ^ 59
def prefixEnd_6658825 : Nat := 4983230072969 + 3 ^ 40 * 6658825 * 2
def baseEnd_6658825 : Nat := 1139725939725005016754709

theorem tailTrace_6658825 : CollatzResearch.WordTrace tailWord_6658825 prefixEnd_6658825 1139725939725005016754709 := by
  unfold tailWord_6658825
  simp only [CollatzResearch.WordTrace]
  refine ⟨242867300101221736615065929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161911533400814491076710619 242867300101221736615065929)
  ·
    refine ⟨182150475075916302461299447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242867300101221736615065929 182150475075916302461299447)
    ·
      refine ⟨273225712613874453691949171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182150475075916302461299447 273225712613874453691949171)
      ·
        refine ⟨409838568920811680537923757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273225712613874453691949171 409838568920811680537923757)
        ·
          refine ⟨153689463345304380201721409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 409838568920811680537923757 153689463345304380201721409)
          ·
            refine ⟨115267097508978285151291057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153689463345304380201721409 115267097508978285151291057)
            ·
              refine ⟨86450323131733713863468293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115267097508978285151291057 86450323131733713863468293)
              ·
                refine ⟨16209435587200071349400305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 86450323131733713863468293 16209435587200071349400305)
                ·
                  refine ⟨12157076690400053512050229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16209435587200071349400305 12157076690400053512050229)
                  ·
                    refine ⟨1139725939725005016754709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12157076690400053512050229 1139725939725005016754709)
                    ·
                      rfl

theorem cell23_6658825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 4, 2, 5].length) (baseStart_6658825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6658825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6658825 prefixEnd_6658825 := by exact prefixLift 6658825
  have htrace : WordTrace (prefixWord ++ tailWord_6658825) baseStart_6658825 baseEnd_6658825 := by
    simpa [prefixWord, tailWord_6658825, baseEnd_6658825] using wordTrace_append hprefix tailTrace_6658825
  have hstable : (prefixWord ++ tailWord_6658825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6658825).length < 2 ^ (prefixWord ++ tailWord_6658825).sum := by decide
  have hdescent : baseEnd_6658825 < baseStart_6658825 := by decide
  rcases family_descends (prefixWord ++ tailWord_6658825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6658886 : List Nat := [6, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5]
def baseStart_6658886 : Nat := 118140960795 + 6658886 * 2 ^ 59
def prefixEnd_6658886 : Nat := 4983230072969 + 3 ^ 40 * 6658886 * 2
def baseEnd_6658886 : Nat := 3419209141494939311601347

theorem tailTrace_6658886 : CollatzResearch.WordTrace tailWord_6658886 prefixEnd_6658886 3419209141494939311601347 := by
  unfold tailWord_6658886
  simp only [CollatzResearch.WordTrace]
  refine ⟨7589672654812523251032391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 161913016636000496022024341 7589672654812523251032391)
  ·
    refine ⟨11384508982218784876548587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7589672654812523251032391 11384508982218784876548587)
    ·
      refine ⟨17076763473328177314822881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11384508982218784876548587 17076763473328177314822881)
      ·
        refine ⟨12807572604996132986117161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17076763473328177314822881 12807572604996132986117161)
        ·
          refine ⟨9605679453747099739587871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12807572604996132986117161 9605679453747099739587871)
          ·
            refine ⟨14408519180620649609381807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9605679453747099739587871 14408519180620649609381807)
            ·
              refine ⟨21612778770930974414072711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14408519180620649609381807 21612778770930974414072711)
              ·
                refine ⟨32419168156396461621109067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21612778770930974414072711 32419168156396461621109067)
                ·
                  refine ⟨48628752234594692431663601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32419168156396461621109067 48628752234594692431663601)
                  ·
                    refine ⟨36471564175946019323747701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48628752234594692431663601 36471564175946019323747701)
                    ·
                      refine ⟨3419209141494939311601347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36471564175946019323747701 3419209141494939311601347)
                      ·
                        rfl

theorem cell23_6658886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_6658886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6658886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6658886 prefixEnd_6658886 := by exact prefixLift 6658886
  have htrace : WordTrace (prefixWord ++ tailWord_6658886) baseStart_6658886 baseEnd_6658886 := by
    simpa [prefixWord, tailWord_6658886, baseEnd_6658886] using wordTrace_append hprefix tailTrace_6658886
  have hstable : (prefixWord ++ tailWord_6658886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6658886).length < 2 ^ (prefixWord ++ tailWord_6658886).sum := by decide
  have hdescent : baseEnd_6658886 < baseStart_6658886 := by decide
  rcases family_descends (prefixWord ++ tailWord_6658886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6658889 : List Nat := [1, 2, 1, 1, 2, 7, 1, 1, 3, 4]
def baseStart_6658889 : Nat := 118140960795 + 6658889 * 2 ^ 59
def prefixEnd_6658889 : Nat := 4983230072969 + 3 ^ 40 * 6658889 * 2
def baseEnd_6658889 : Nat := 1139736893978967599954611

theorem tailTrace_6658889 : CollatzResearch.WordTrace tailWord_6658889 prefixEnd_6658889 1139736893978967599954611 := by
  unfold tailWord_6658889
  simp only [CollatzResearch.WordTrace]
  refine ⟨242869634372989875545395721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161913089581993250363597147 242869634372989875545395721)
  ·
    refine ⟨182152225779742406659046791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242869634372989875545395721 182152225779742406659046791)
    ·
      refine ⟨273228338669613609988570187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182152225779742406659046791 273228338669613609988570187)
      ·
        refine ⟨409842508004420414982855281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273228338669613609988570187 409842508004420414982855281)
        ·
          refine ⟨307381881003315311237141461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 409842508004420414982855281 307381881003315311237141461)
          ·
            refine ⟨7204262836015202607120503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 307381881003315311237141461 7204262836015202607120503)
            ·
              refine ⟨10806394254022803910680755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7204262836015202607120503 10806394254022803910680755)
              ·
                refine ⟨16209591381034205866021133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10806394254022803910680755 16209591381034205866021133)
                ·
                  refine ⟨6078596767887827199757925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16209591381034205866021133 6078596767887827199757925)
                  ·
                    refine ⟨1139736893978967599954611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6078596767887827199757925 1139736893978967599954611)
                    ·
                      rfl

theorem cell23_6658889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 1, 1, 3, 4].length) (baseStart_6658889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6658889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6658889 prefixEnd_6658889 := by exact prefixLift 6658889
  have htrace : WordTrace (prefixWord ++ tailWord_6658889) baseStart_6658889 baseEnd_6658889 := by
    simpa [prefixWord, tailWord_6658889, baseEnd_6658889] using wordTrace_append hprefix tailTrace_6658889
  have hstable : (prefixWord ++ tailWord_6658889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6658889).length < 2 ^ (prefixWord ++ tailWord_6658889).sum := by decide
  have hdescent : baseEnd_6658889 < baseStart_6658889 := by decide
  rcases family_descends (prefixWord ++ tailWord_6658889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6658939 : List Nat := [1, 1, 1, 1, 1, 5, 4, 2, 2, 3, 2]
def baseStart_6658939 : Nat := 118140960795 + 6658939 * 2 ^ 59
def prefixEnd_6658939 : Nat := 4983230072969 + 3 ^ 40 * 6658939 * 2
def baseEnd_6658939 : Nat := 3419236355969627604238603

theorem tailTrace_6658939 : CollatzResearch.WordTrace tailWord_6658939 prefixEnd_6658939 3419236355969627604238603 := by
  unfold tailWord_6658939
  simp only [CollatzResearch.WordTrace]
  refine ⟨242871458022808734084715871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161914305348539156056477247 242871458022808734084715871)
  ·
    refine ⟨364307187034213101127073807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242871458022808734084715871 364307187034213101127073807)
    ·
      refine ⟨546460780551319651690610711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 364307187034213101127073807 546460780551319651690610711)
      ·
        refine ⟨819691170826979477535916067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 546460780551319651690610711 819691170826979477535916067)
        ·
          refine ⟨1229536756240469216303874101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 819691170826979477535916067 1229536756240469216303874101)
          ·
            refine ⟨115269070897543989028488197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1229536756240469216303874101 115269070897543989028488197)
            ·
              refine ⟨21612950793289497942841537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 115269070897543989028488197 21612950793289497942841537)
              ·
                refine ⟨16209713094967123457131153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21612950793289497942841537 16209713094967123457131153)
                ·
                  refine ⟨12157284821225342592848365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16209713094967123457131153 12157284821225342592848365)
                  ·
                    refine ⟨4558981807959503472318137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12157284821225342592848365 4558981807959503472318137)
                    ·
                      refine ⟨3419236355969627604238603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4558981807959503472318137 3419236355969627604238603)
                      ·
                        rfl

theorem cell23_6658939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 2, 2, 3, 2].length) (baseStart_6658939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6658939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6658939 prefixEnd_6658939 := by exact prefixLift 6658939
  have htrace : WordTrace (prefixWord ++ tailWord_6658939) baseStart_6658939 baseEnd_6658939 := by
    simpa [prefixWord, tailWord_6658939, baseEnd_6658939] using wordTrace_append hprefix tailTrace_6658939
  have hstable : (prefixWord ++ tailWord_6658939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6658939).length < 2 ^ (prefixWord ++ tailWord_6658939).sum := by decide
  have hdescent : baseEnd_6658939 < baseStart_6658939 := by decide
  rcases family_descends (prefixWord ++ tailWord_6658939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6658983 : List Nat := [1, 1, 6, 1, 3, 2, 2, 1, 1, 5]
def baseStart_6658983 : Nat := 118140960795 + 6658983 * 2 ^ 59
def prefixEnd_6658983 : Nat := 4983230072969 + 3 ^ 40 * 6658983 * 2
def baseEnd_6658983 : Nat := 1139752983039475144029467

theorem tailTrace_6658983 : CollatzResearch.WordTrace tailWord_6658983 prefixEnd_6658983 1139752983039475144029467 := by
  unfold tailWord_6658983
  simp only [CollatzResearch.WordTrace]
  refine ⟨242873062834649329599317603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161915375223099553066211735 242873062834649329599317603)
  ·
    refine ⟨364309594251973994398976405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242873062834649329599317603 364309594251973994398976405)
    ·
      refine ⟨17077012230561280987452019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 364309594251973994398976405 17077012230561280987452019)
      ·
        refine ⟨25615518345841921481178029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17077012230561280987452019 25615518345841921481178029)
        ·
          refine ⟨9605819379690720555441761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25615518345841921481178029 9605819379690720555441761)
          ·
            refine ⟨7204364534768040416581321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9605819379690720555441761 7204364534768040416581321)
            ·
              refine ⟨5403273401076030312435991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7204364534768040416581321 5403273401076030312435991)
              ·
                refine ⟨8104910101614045468653987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5403273401076030312435991 8104910101614045468653987)
                ·
                  refine ⟨12157365152421068202980981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8104910101614045468653987 12157365152421068202980981)
                  ·
                    refine ⟨1139752983039475144029467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12157365152421068202980981 1139752983039475144029467)
                    ·
                      rfl

theorem cell23_6658983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 2, 1, 1, 5].length) (baseStart_6658983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6658983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6658983 prefixEnd_6658983 := by exact prefixLift 6658983
  have htrace : WordTrace (prefixWord ++ tailWord_6658983) baseStart_6658983 baseEnd_6658983 := by
    simpa [prefixWord, tailWord_6658983, baseEnd_6658983] using wordTrace_append hprefix tailTrace_6658983
  have hstable : (prefixWord ++ tailWord_6658983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6658983).length < 2 ^ (prefixWord ++ tailWord_6658983).sum := by decide
  have hdescent : baseEnd_6658983 < baseStart_6658983 := by decide
  rcases family_descends (prefixWord ++ tailWord_6658983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6659016 : List Nat := [2, 1, 3, 1, 5, 2, 1, 1, 1, 2, 4]
def baseStart_6659016 : Nat := 118140960795 + 6659016 * 2 ^ 59
def prefixEnd_6659016 : Nat := 4983230072969 + 3 ^ 40 * 6659016 * 2
def baseEnd_6659016 : Nat := 3419275893980023802975749

theorem tailTrace_6659016 : CollatzResearch.WordTrace tailWord_6659016 prefixEnd_6659016 3419275893980023802975749 := by
  unfold tailWord_6659016
  simp only [CollatzResearch.WordTrace]
  refine ⟨121437133221764888117634451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161916177629019850823512601 121437133221764888117634451)
  ·
    refine ⟨182155699832647332176451677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121437133221764888117634451 182155699832647332176451677)
    ·
      refine ⟨68308387437242749566169379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182155699832647332176451677 68308387437242749566169379)
      ·
        refine ⟨102462581155864124349254069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68308387437242749566169379 102462581155864124349254069)
        ·
          refine ⟨9605866983362261657742569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 102462581155864124349254069 9605866983362261657742569)
          ·
            refine ⟨7204400237521696243306927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9605866983362261657742569 7204400237521696243306927)
            ·
              refine ⟨10806600356282544364960391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7204400237521696243306927 10806600356282544364960391)
              ·
                refine ⟨16209900534423816547440587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10806600356282544364960391 16209900534423816547440587)
                ·
                  refine ⟨24314850801635724821160881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16209900534423816547440587 24314850801635724821160881)
                  ·
                    refine ⟨18236138101226793615870661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24314850801635724821160881 18236138101226793615870661)
                    ·
                      refine ⟨3419275893980023802975749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18236138101226793615870661 3419275893980023802975749)
                      ·
                        rfl

theorem cell23_6659016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 1, 1, 1, 2, 4].length) (baseStart_6659016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6659016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6659016 prefixEnd_6659016 := by exact prefixLift 6659016
  have htrace : WordTrace (prefixWord ++ tailWord_6659016) baseStart_6659016 baseEnd_6659016 := by
    simpa [prefixWord, tailWord_6659016, baseEnd_6659016] using wordTrace_append hprefix tailTrace_6659016
  have hstable : (prefixWord ++ tailWord_6659016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6659016).length < 2 ^ (prefixWord ++ tailWord_6659016).sum := by decide
  have hdescent : baseEnd_6659016 < baseStart_6659016 := by decide
  rcases family_descends (prefixWord ++ tailWord_6659016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6659019 : List Nat := [1, 1, 1, 1, 3, 5, 3, 1, 1, 3, 3]
def baseStart_6659019 : Nat := 118140960795 + 6659019 * 2 ^ 59
def prefixEnd_6659019 : Nat := 4983230072969 + 3 ^ 40 * 6659019 * 2
def baseEnd_6659019 : Nat := 3419277434421987291238235

theorem tailTrace_6659019 : CollatzResearch.WordTrace tailWord_6659019 prefixEnd_6659019 3419277434421987291238235 := by
  unfold tailWord_6659019
  simp only [CollatzResearch.WordTrace]
  refine ⟨242874375862518907747628111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161916250575012605165085407 242874375862518907747628111)
  ·
    refine ⟨364311563793778361621442167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242874375862518907747628111 364311563793778361621442167)
    ·
      refine ⟨546467345690667542432163251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 364311563793778361621442167 546467345690667542432163251)
      ·
        refine ⟨819701018536001313648244877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 546467345690667542432163251 819701018536001313648244877)
        ·
          refine ⟨307387881951000492618091829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 819701018536001313648244877 307387881951000492618091829)
          ·
            refine ⟨28817613932906296182946109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 307387881951000492618091829 28817613932906296182946109)
            ·
              refine ⟨10806605224839861068604791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28817613932906296182946109 10806605224839861068604791)
              ·
                refine ⟨16209907837259791602907187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10806605224839861068604791 16209907837259791602907187)
                ·
                  refine ⟨24314861755889687404360781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16209907837259791602907187 24314861755889687404360781)
                  ·
                    refine ⟨9118073158458632776635293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24314861755889687404360781 9118073158458632776635293)
                    ·
                      refine ⟨3419277434421987291238235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9118073158458632776635293 3419277434421987291238235)
                      ·
                        rfl

theorem cell23_6659019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 3, 1, 1, 3, 3].length) (baseStart_6659019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6659019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6659019 prefixEnd_6659019 := by exact prefixLift 6659019
  have htrace : WordTrace (prefixWord ++ tailWord_6659019) baseStart_6659019 baseEnd_6659019 := by
    simpa [prefixWord, tailWord_6659019, baseEnd_6659019] using wordTrace_append hprefix tailTrace_6659019
  have hstable : (prefixWord ++ tailWord_6659019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6659019).length < 2 ^ (prefixWord ++ tailWord_6659019).sum := by decide
  have hdescent : baseEnd_6659019 < baseStart_6659019 := by decide
  rcases family_descends (prefixWord ++ tailWord_6659019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6659026 : List Nat := [3, 2, 2, 3, 1, 3, 2, 7]
def baseStart_6659026 : Nat := 118140960795 + 6659026 * 2 ^ 59
def prefixEnd_6659026 : Nat := 4983230072969 + 3 ^ 40 * 6659026 * 2
def baseEnd_6659026 : Nat := 126640038103206250512989

theorem tailTrace_6659026 : CollatzResearch.WordTrace tailWord_6659026 prefixEnd_6659026 126640038103206250512989 := by
  unfold tailWord_6659026
  simp only [CollatzResearch.WordTrace]
  refine ⟨60718657793373386985783233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161916420782329031962088621 60718657793373386985783233)
  ·
    refine ⟨45538993345030040239337425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60718657793373386985783233 45538993345030040239337425)
    ·
      refine ⟨34154245008772530179503069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45538993345030040239337425 34154245008772530179503069)
      ·
        refine ⟨12807841878289698817313651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34154245008772530179503069 12807841878289698817313651)
        ·
          refine ⟨19211762817434548225970477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12807841878289698817313651 19211762817434548225970477)
          ·
            refine ⟨7204411056537955584738929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19211762817434548225970477 7204411056537955584738929)
            ·
              refine ⟨5403308292403466688554197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7204411056537955584738929 5403308292403466688554197)
              ·
                refine ⟨126640038103206250512989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5403308292403466688554197 126640038103206250512989)
                ·
                  rfl

theorem cell23_6659026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 2, 7].length) (baseStart_6659026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6659026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6659026 prefixEnd_6659026 := by exact prefixLift 6659026
  have htrace : WordTrace (prefixWord ++ tailWord_6659026) baseStart_6659026 baseEnd_6659026 := by
    simpa [prefixWord, tailWord_6659026, baseEnd_6659026] using wordTrace_append hprefix tailTrace_6659026
  have hstable : (prefixWord ++ tailWord_6659026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6659026).length < 2 ^ (prefixWord ++ tailWord_6659026).sum := by decide
  have hdescent : baseEnd_6659026 < baseStart_6659026 := by decide
  rcases family_descends (prefixWord ++ tailWord_6659026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6659032 : List Nat := [2, 1, 2, 2, 2, 3, 1, 1, 2, 2, 5]
def baseStart_6659032 : Nat := 118140960795 + 6659032 * 2 ^ 59
def prefixEnd_6659032 : Nat := 4983230072969 + 3 ^ 40 * 6659032 * 2
def baseEnd_6659032 : Nat := 3419284109670495740375675

theorem tailTrace_6659032 : CollatzResearch.WordTrace tailWord_6659032 prefixEnd_6659032 3419284109670495740375675 := by
  unfold tailWord_6659032
  simp only [CollatzResearch.WordTrace]
  refine ⟨121437425005735905483925675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161916566674314540645234233 121437425005735905483925675)
  ·
    refine ⟨182156137508603858225888513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121437425005735905483925675 182156137508603858225888513)
    ·
      refine ⟨136617103131452893669416385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182156137508603858225888513 136617103131452893669416385)
      ·
        refine ⟨102462827348589670252062289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136617103131452893669416385 102462827348589670252062289)
        ·
          refine ⟨76847120511442252689046717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102462827348589670252062289 76847120511442252689046717)
          ·
            refine ⟨28817670191790844758392519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76847120511442252689046717 28817670191790844758392519)
            ·
              refine ⟨43226505287686267137588779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28817670191790844758392519 43226505287686267137588779)
              ·
                refine ⟨64839757931529400706383169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43226505287686267137588779 64839757931529400706383169)
                ·
                  refine ⟨48629818448647050529787377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64839757931529400706383169 48629818448647050529787377)
                  ·
                    refine ⟨36472363836485287897340533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48629818448647050529787377 36472363836485287897340533)
                    ·
                      refine ⟨3419284109670495740375675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36472363836485287897340533 3419284109670495740375675)
                      ·
                        rfl

theorem cell23_6659032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 1, 2, 2, 5].length) (baseStart_6659032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6659032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6659032 prefixEnd_6659032 := by exact prefixLift 6659032
  have htrace : WordTrace (prefixWord ++ tailWord_6659032) baseStart_6659032 baseEnd_6659032 := by
    simpa [prefixWord, tailWord_6659032, baseEnd_6659032] using wordTrace_append hprefix tailTrace_6659032
  have hstable : (prefixWord ++ tailWord_6659032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6659032).length < 2 ^ (prefixWord ++ tailWord_6659032).sum := by decide
  have hdescent : baseEnd_6659032 < baseStart_6659032 := by decide
  rcases family_descends (prefixWord ++ tailWord_6659032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6659037 : List Nat := [1, 4, 3, 1, 2, 3, 1, 3, 1, 2, 2]
def baseStart_6659037 : Nat := 118140960795 + 6659037 * 2 ^ 59
def prefixEnd_6659037 : Nat := 4983230072969 + 3 ^ 40 * 6659037 * 2
def baseEnd_6659037 : Nat := 3419286677073768220813153

theorem tailTrace_6659037 : CollatzResearch.WordTrace tailWord_6659037 prefixEnd_6659037 3419286677073768220813153 := by
  unfold tailWord_6659037
  simp only [CollatzResearch.WordTrace]
  refine ⟨242875032376453696821783365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161916688250969131214522243 242875032376453696821783365)
  ·
    refine ⟨45539068570585068154084381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 242875032376453696821783365 45539068570585068154084381)
    ·
      refine ⟨17077150713969400557781643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45539068570585068154084381 17077150713969400557781643)
      ·
        refine ⟨25615726070954100836672465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17077150713969400557781643 25615726070954100836672465)
        ·
          refine ⟨19211794553215575627504349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25615726070954100836672465 19211794553215575627504349)
          ·
            refine ⟨7204422957455840860314131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19211794553215575627504349 7204422957455840860314131)
            ·
              refine ⟨10806634436183761290471197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7204422957455840860314131 10806634436183761290471197)
              ·
                refine ⟨4052487913568910483926699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10806634436183761290471197 4052487913568910483926699)
                ·
                  refine ⟨6078731870353365725890049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4052487913568910483926699 6078731870353365725890049)
                  ·
                    refine ⟨4559048902765024294417537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6078731870353365725890049 4559048902765024294417537)
                    ·
                      refine ⟨3419286677073768220813153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4559048902765024294417537 3419286677073768220813153)
                      ·
                        rfl

theorem cell23_6659037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 1, 3, 1, 2, 2].length) (baseStart_6659037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6659037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6659037 prefixEnd_6659037 := by exact prefixLift 6659037
  have htrace : WordTrace (prefixWord ++ tailWord_6659037) baseStart_6659037 baseEnd_6659037 := by
    simpa [prefixWord, tailWord_6659037, baseEnd_6659037] using wordTrace_append hprefix tailTrace_6659037
  have hstable : (prefixWord ++ tailWord_6659037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6659037).length < 2 ^ (prefixWord ++ tailWord_6659037).sum := by decide
  have hdescent : baseEnd_6659037 < baseStart_6659037 := by decide
  rcases family_descends (prefixWord ++ tailWord_6659037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6659060 : List Nat := [2, 6, 2, 1, 1, 1, 2, 8]
def baseStart_6659060 : Nat := 118140960795 + 6659060 * 2 ^ 59
def prefixEnd_6659060 : Nat := 4983230072969 + 3 ^ 40 * 6659060 * 2
def baseEnd_6659060 : Nat := 126640684708474875215761

theorem tailTrace_6659060 : CollatzResearch.WordTrace tailWord_6659060 prefixEnd_6659060 126640684708474875215761 := by
  unfold tailWord_6659060
  simp only [CollatzResearch.WordTrace]
  refine ⟨121437935627685185874935317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161917247503580247833247089 121437935627685185874935317)
  ·
    refine ⟨5692403232547743087887593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 121437935627685185874935317 5692403232547743087887593)
    ·
      refine ⟨4269302424410807315915695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5692403232547743087887593 4269302424410807315915695)
      ·
        refine ⟨6403953636616210973873543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4269302424410807315915695 6403953636616210973873543)
        ·
          refine ⟨9605930454924316460810315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6403953636616210973873543 9605930454924316460810315)
          ·
            refine ⟨14408895682386474691215473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9605930454924316460810315 14408895682386474691215473)
            ·
              refine ⟨10806671761789856018411605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14408895682386474691215473 10806671761789856018411605)
              ·
                refine ⟨126640684708474875215761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10806671761789856018411605 126640684708474875215761)
                ·
                  rfl

theorem cell23_6659060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 2, 8].length) (baseStart_6659060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6659060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6659060 prefixEnd_6659060 := by exact prefixLift 6659060
  have htrace : WordTrace (prefixWord ++ tailWord_6659060) baseStart_6659060 baseEnd_6659060 := by
    simpa [prefixWord, tailWord_6659060, baseEnd_6659060] using wordTrace_append hprefix tailTrace_6659060
  have hstable : (prefixWord ++ tailWord_6659060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6659060).length < 2 ^ (prefixWord ++ tailWord_6659060).sum := by decide
  have hdescent : baseEnd_6659060 < baseStart_6659060 := by decide
  rcases family_descends (prefixWord ++ tailWord_6659060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6659070 : List Nat := [4, 2, 2, 2, 2, 1, 1, 3, 2, 1, 3]
def baseStart_6659070 : Nat := 118140960795 + 6659070 * 2 ^ 59
def prefixEnd_6659070 : Nat := 4983230072969 + 3 ^ 40 * 6659070 * 2
def baseEnd_6659070 : Nat := 3419303621935366591700501

theorem tailTrace_6659070 : CollatzResearch.WordTrace tailWord_6659070 prefixEnd_6659070 3419303621935366591700501 := by
  unfold tailWord_6659070
  simp only [CollatzResearch.WordTrace]
  refine ⟨30359529498166767932216833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 161917490656889428971823109 30359529498166767932216833)
  ·
    refine ⟨22769647123625075949162625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30359529498166767932216833 22769647123625075949162625)
    ·
      refine ⟨17077235342718806961871969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22769647123625075949162625 17077235342718806961871969)
      ·
        refine ⟨12807926507039105221403977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17077235342718806961871969 12807926507039105221403977)
        ·
          refine ⟨9605944880279328916052983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12807926507039105221403977 9605944880279328916052983)
          ·
            refine ⟨14408917320418993374079475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9605944880279328916052983 14408917320418993374079475)
            ·
              refine ⟨21613375980628490061119213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14408917320418993374079475 21613375980628490061119213)
              ·
                refine ⟨8105015992735683772919705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21613375980628490061119213 8105015992735683772919705)
                ·
                  refine ⟨6078761994551762829689779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8105015992735683772919705 6078761994551762829689779)
                  ·
                    refine ⟨9118142991827644244534669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6078761994551762829689779 9118142991827644244534669)
                    ·
                      refine ⟨3419303621935366591700501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9118142991827644244534669 3419303621935366591700501)
                      ·
                        rfl

theorem cell23_6659070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_6659070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6659070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6659070 prefixEnd_6659070 := by exact prefixLift 6659070
  have htrace : WordTrace (prefixWord ++ tailWord_6659070) baseStart_6659070 baseEnd_6659070 := by
    simpa [prefixWord, tailWord_6659070, baseEnd_6659070] using wordTrace_append hprefix tailTrace_6659070
  have hstable : (prefixWord ++ tailWord_6659070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6659070).length < 2 ^ (prefixWord ++ tailWord_6659070).sum := by decide
  have hdescent : baseEnd_6659070 < baseStart_6659070 := by decide
  rcases family_descends (prefixWord ++ tailWord_6659070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6659072 : List Nat := [2, 1, 1, 2, 1, 1, 1, 2, 6, 2, 4]
def baseStart_6659072 : Nat := 118140960795 + 6659072 * 2 ^ 59
def prefixEnd_6659072 : Nat := 4983230072969 + 3 ^ 40 * 6659072 * 2
def baseEnd_6659072 : Nat := 3419304648896675583875491

theorem tailTrace_6659072 : CollatzResearch.WordTrace tailWord_6659072 prefixEnd_6659072 3419304648896675583875491 := by
  unfold tailWord_6659072
  simp only [CollatzResearch.WordTrace]
  refine ⟨121438154465663448899653735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161917539287551265199538313 121438154465663448899653735)
  ·
    refine ⟨182157231698495173349480603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121438154465663448899653735 182157231698495173349480603)
    ·
      refine ⟨273235847547742760024220905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182157231698495173349480603 273235847547742760024220905)
      ·
        refine ⟨204926885660807070018165679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 273235847547742760024220905 204926885660807070018165679)
        ·
          refine ⟨307390328491210605027248519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204926885660807070018165679 307390328491210605027248519)
          ·
            refine ⟨461085492736815907540872779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 307390328491210605027248519 461085492736815907540872779)
            ·
              refine ⟨691628239105223861311309169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 461085492736815907540872779 691628239105223861311309169)
              ·
                refine ⟨518721179328917895983481877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 691628239105223861311309169 518721179328917895983481877)
                ·
                  refine ⟨24315055281043026374225713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 518721179328917895983481877 24315055281043026374225713)
                  ·
                    refine ⟨18236291460782269780669285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24315055281043026374225713 18236291460782269780669285)
                    ·
                      refine ⟨3419304648896675583875491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18236291460782269780669285 3419304648896675583875491)
                      ·
                        rfl

theorem cell23_6659072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 6, 2, 4].length) (baseStart_6659072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6659072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6659072 prefixEnd_6659072 := by exact prefixLift 6659072
  have htrace : WordTrace (prefixWord ++ tailWord_6659072) baseStart_6659072 baseEnd_6659072 := by
    simpa [prefixWord, tailWord_6659072, baseEnd_6659072] using wordTrace_append hprefix tailTrace_6659072
  have hstable : (prefixWord ++ tailWord_6659072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6659072).length < 2 ^ (prefixWord ++ tailWord_6659072).sum := by decide
  have hdescent : baseEnd_6659072 < baseStart_6659072 := by decide
  rcases family_descends (prefixWord ++ tailWord_6659072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6659109 : List Nat := [1, 3, 1, 2, 2, 2, 2, 2, 2, 3, 3]
def baseStart_6659109 : Nat := 118140960795 + 6659109 * 2 ^ 59
def prefixEnd_6659109 : Nat := 4983230072969 + 3 ^ 40 * 6659109 * 2
def baseEnd_6659109 : Nat := 3419323647680891939112821

theorem tailTrace_6659109 : CollatzResearch.WordTrace tailWord_6659109 prefixEnd_6659109 3419323647680891939112821 := by
  unfold tailWord_6659109
  simp only [CollatzResearch.WordTrace]
  refine ⟨242877658432192853118404381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161918438954795235412269587 242877658432192853118404381)
  ·
    refine ⟨91079121912072319919401643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 242877658432192853118404381 91079121912072319919401643)
    ·
      refine ⟨136618682868108479879102465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91079121912072319919401643 136618682868108479879102465)
      ·
        refine ⟨102464012151081359909326849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136618682868108479879102465 102464012151081359909326849)
        ·
          refine ⟨76848009113311019931995137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102464012151081359909326849 76848009113311019931995137)
          ·
            refine ⟨57636006834983264948996353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76848009113311019931995137 57636006834983264948996353)
            ·
              refine ⟨43227005126237448711747265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57636006834983264948996353 43227005126237448711747265)
              ·
                refine ⟨32420253844678086533810449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43227005126237448711747265 32420253844678086533810449)
                ·
                  refine ⟨24315190383508564900357837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32420253844678086533810449 24315190383508564900357837)
                  ·
                    refine ⟨9118196393815711837634189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24315190383508564900357837 9118196393815711837634189)
                    ·
                      refine ⟨3419323647680891939112821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9118196393815711837634189 3419323647680891939112821)
                      ·
                        rfl

theorem cell23_6659109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 2, 2, 3, 3].length) (baseStart_6659109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6659109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6659109 prefixEnd_6659109 := by exact prefixLift 6659109
  have htrace : WordTrace (prefixWord ++ tailWord_6659109) baseStart_6659109 baseEnd_6659109 := by
    simpa [prefixWord, tailWord_6659109, baseEnd_6659109] using wordTrace_append hprefix tailTrace_6659109
  have hstable : (prefixWord ++ tailWord_6659109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6659109).length < 2 ^ (prefixWord ++ tailWord_6659109).sum := by decide
  have hdescent : baseEnd_6659109 < baseStart_6659109 := by decide
  rcases family_descends (prefixWord ++ tailWord_6659109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6659126 : List Nat := [5, 1, 2, 1, 1, 2, 1, 1, 1, 5, 3]
def baseStart_6659126 : Nat := 118140960795 + 6659126 * 2 ^ 59
def prefixEnd_6659126 : Nat := 4983230072969 + 3 ^ 40 * 6659126 * 2
def baseEnd_6659126 : Nat := 3419332376852018372600243

theorem tailTrace_6659126 : CollatzResearch.WordTrace tailWord_6659126 prefixEnd_6659126 3419332376852018372600243 := by
  unfold tailWord_6659126
  simp only [CollatzResearch.WordTrace]
  refine ⟨15179892404570704063860827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 161918852315420843347848821 15179892404570704063860827)
  ·
    refine ⟨22769838606856056095791241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15179892404570704063860827 22769838606856056095791241)
    ·
      refine ⟨17077378955142042071843431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22769838606856056095791241 17077378955142042071843431)
      ·
        refine ⟨25616068432713063107765147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17077378955142042071843431 25616068432713063107765147)
        ·
          refine ⟨38424102649069594661647721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25616068432713063107765147 38424102649069594661647721)
          ·
            refine ⟨28818076986802195996235791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38424102649069594661647721 28818076986802195996235791)
            ·
              refine ⟨43227115480203293994353687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28818076986802195996235791 43227115480203293994353687)
              ·
                refine ⟨64840673220304940991530531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43227115480203293994353687 64840673220304940991530531)
                ·
                  refine ⟨97261009830457411487295797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64840673220304940991530531 97261009830457411487295797)
                  ·
                    refine ⟨9118219671605382326933981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 97261009830457411487295797 9118219671605382326933981)
                    ·
                      refine ⟨3419332376852018372600243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9118219671605382326933981 3419332376852018372600243)
                      ·
                        rfl

theorem cell23_6659126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 1, 1, 5, 3].length) (baseStart_6659126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6659126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6659126 prefixEnd_6659126 := by exact prefixLift 6659126
  have htrace : WordTrace (prefixWord ++ tailWord_6659126) baseStart_6659126 baseEnd_6659126 := by
    simpa [prefixWord, tailWord_6659126, baseEnd_6659126] using wordTrace_append hprefix tailTrace_6659126
  have hstable : (prefixWord ++ tailWord_6659126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6659126).length < 2 ^ (prefixWord ++ tailWord_6659126).sum := by decide
  have hdescent : baseEnd_6659126 < baseStart_6659126 := by decide
  rcases family_descends (prefixWord ++ tailWord_6659126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6659159 : List Nat := [1, 1, 3, 2, 2, 1, 1, 1, 7, 4]
def baseStart_6659159 : Nat := 118140960795 + 6659159 * 2 ^ 59
def prefixEnd_6659159 : Nat := 4983230072969 + 3 ^ 40 * 6659159 * 2
def baseEnd_6659159 : Nat := 1139783107237872247829197

theorem tailTrace_6659159 : CollatzResearch.WordTrace tailWord_6659159 prefixEnd_6659159 1139783107237872247829197 := by
  unfold tailWord_6659159
  simp only [CollatzResearch.WordTrace]
  refine ⟨242879482082011711657724531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161919654721341141105149687 242879482082011711657724531)
  ·
    refine ⟨364319223123017567486586797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242879482082011711657724531 364319223123017567486586797)
    ·
      refine ⟨136619708671131587807470049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 364319223123017567486586797 136619708671131587807470049)
      ·
        refine ⟨102464781503348690855602537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136619708671131587807470049 102464781503348690855602537)
        ·
          refine ⟨76848586127511518141701903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102464781503348690855602537 76848586127511518141701903)
          ·
            refine ⟨115272879191267277212552855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76848586127511518141701903 115272879191267277212552855)
            ·
              refine ⟨172909318786900915818829283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115272879191267277212552855 172909318786900915818829283)
              ·
                refine ⟨259363978180351373728243925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 172909318786900915818829283 259363978180351373728243925)
                ·
                  refine ⟨6078843238601985321755717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 259363978180351373728243925 6078843238601985321755717)
                  ·
                    refine ⟨1139783107237872247829197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6078843238601985321755717 1139783107237872247829197)
                    ·
                      rfl

theorem cell23_6659159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 7, 4].length) (baseStart_6659159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6659159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6659159 prefixEnd_6659159 := by exact prefixLift 6659159
  have htrace : WordTrace (prefixWord ++ tailWord_6659159) baseStart_6659159 baseEnd_6659159 := by
    simpa [prefixWord, tailWord_6659159, baseEnd_6659159] using wordTrace_append hprefix tailTrace_6659159
  have hstable : (prefixWord ++ tailWord_6659159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6659159).length < 2 ^ (prefixWord ++ tailWord_6659159).sum := by decide
  have hdescent : baseEnd_6659159 < baseStart_6659159 := by decide
  rcases family_descends (prefixWord ++ tailWord_6659159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6659256 : List Nat := [2, 1, 2, 1, 2, 1, 2, 6, 1, 1, 4]
def baseStart_6659256 : Nat := 118140960795 + 6659256 * 2 ^ 59
def prefixEnd_6659256 : Nat := 4983230072969 + 3 ^ 40 * 6659256 * 2
def baseEnd_6659256 : Nat := 3419399129337102863974645

theorem tailTrace_6659256 : CollatzResearch.WordTrace tailWord_6659256 prefixEnd_6659256 3419399129337102863974645 := by
  unfold tailWord_6659256
  simp only [CollatzResearch.WordTrace]
  refine ⟨121441509981330148612002811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161922013308440198149337081 121441509981330148612002811)
  ·
    refine ⟨182162264971995222918004217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121441509981330148612002811 182162264971995222918004217)
    ·
      refine ⟨136621698728996417188503163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182162264971995222918004217 136621698728996417188503163)
      ·
        refine ⟨204932548093494625782754745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136621698728996417188503163 204932548093494625782754745)
        ·
          refine ⟨153699411070120969337066059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 204932548093494625782754745 153699411070120969337066059)
          ·
            refine ⟨230549116605181454005599089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153699411070120969337066059 230549116605181454005599089)
            ·
              refine ⟨172911837453886090504199317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 230549116605181454005599089 172911837453886090504199317)
              ·
                refine ⟨8105242380650910492384343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 172911837453886090504199317 8105242380650910492384343)
                ·
                  refine ⟨12157863570976365738576515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8105242380650910492384343 12157863570976365738576515)
                  ·
                    refine ⟨18236795356464548607864773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12157863570976365738576515 18236795356464548607864773)
                    ·
                      refine ⟨3419399129337102863974645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18236795356464548607864773 3419399129337102863974645)
                      ·
                        rfl

theorem cell23_6659256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 6, 1, 1, 4].length) (baseStart_6659256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6659256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6659256 prefixEnd_6659256 := by exact prefixLift 6659256
  have htrace : WordTrace (prefixWord ++ tailWord_6659256) baseStart_6659256 baseEnd_6659256 := by
    simpa [prefixWord, tailWord_6659256, baseEnd_6659256] using wordTrace_append hprefix tailTrace_6659256
  have hstable : (prefixWord ++ tailWord_6659256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6659256).length < 2 ^ (prefixWord ++ tailWord_6659256).sum := by decide
  have hdescent : baseEnd_6659256 < baseStart_6659256 := by decide
  rcases family_descends (prefixWord ++ tailWord_6659256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6659260 : List Nat := [2, 2, 2, 3, 2, 2, 2, 1, 2, 3, 2]
def baseStart_6659260 : Nat := 118140960795 + 6659260 * 2 ^ 59
def prefixEnd_6659260 : Nat := 4983230072969 + 3 ^ 40 * 6659260 * 2
def baseEnd_6659260 : Nat := 3419401183259720848324627

theorem tailTrace_6659260 : CollatzResearch.WordTrace tailWord_6659260 prefixEnd_6659260 3419401183259720848324627 := by
  unfold tailWord_6659260
  simp only [CollatzResearch.WordTrace]
  refine ⟨121441582927322902953575617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161922110569763870604767489 121441582927322902953575617)
  ·
    refine ⟨91081187195492177215181713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121441582927322902953575617 91081187195492177215181713)
    ·
      refine ⟨68310890396619132911386285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91081187195492177215181713 68310890396619132911386285)
      ·
        refine ⟨25616583898732174841769857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68310890396619132911386285 25616583898732174841769857)
        ·
          refine ⟨19212437924049131131327393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25616583898732174841769857 19212437924049131131327393)
          ·
            refine ⟨14409328443036848348495545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19212437924049131131327393 14409328443036848348495545)
            ·
              refine ⟨10806996332277636261371659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14409328443036848348495545 10806996332277636261371659)
              ·
                refine ⟨16210494498416454392057489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10806996332277636261371659 16210494498416454392057489)
                ·
                  refine ⟨12157870873812340794043117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16210494498416454392057489 12157870873812340794043117)
                  ·
                    refine ⟨4559201577679627797766169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12157870873812340794043117 4559201577679627797766169)
                    ·
                      refine ⟨3419401183259720848324627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4559201577679627797766169 3419401183259720848324627)
                      ·
                        rfl

theorem cell23_6659260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 2, 1, 2, 3, 2].length) (baseStart_6659260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6659260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6659260 prefixEnd_6659260 := by exact prefixLift 6659260
  have htrace : WordTrace (prefixWord ++ tailWord_6659260) baseStart_6659260 baseEnd_6659260 := by
    simpa [prefixWord, tailWord_6659260, baseEnd_6659260] using wordTrace_append hprefix tailTrace_6659260
  have hstable : (prefixWord ++ tailWord_6659260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6659260).length < 2 ^ (prefixWord ++ tailWord_6659260).sum := by decide
  have hdescent : baseEnd_6659260 < baseStart_6659260 := by decide
  rcases family_descends (prefixWord ++ tailWord_6659260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6659284 : List Nat := [2, 4, 1, 4, 1, 1, 1, 4, 1, 1, 3]
def baseStart_6659284 : Nat := 118140960795 + 6659284 * 2 ^ 59
def prefixEnd_6659284 : Nat := 4983230072969 + 3 ^ 40 * 6659284 * 2
def baseEnd_6659284 : Nat := 3419413506795428754424517

theorem tailTrace_6659284 : CollatzResearch.WordTrace tailWord_6659284 prefixEnd_6659284 3419413506795428754424517 := by
  unfold tailWord_6659284
  simp only [CollatzResearch.WordTrace]
  refine ⟨121442020603279429003012453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161922694137705905337349937 121442020603279429003012453)
  ·
    refine ⟨22770378863114892938064835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 121442020603279429003012453 22770378863114892938064835)
    ·
      refine ⟨34155568294672339407097253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22770378863114892938064835 34155568294672339407097253)
      ·
        refine ⟨6404169055251063638830735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34155568294672339407097253 6404169055251063638830735)
        ·
          refine ⟨9606253582876595458246103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6404169055251063638830735 9606253582876595458246103)
          ·
            refine ⟨14409380374314893187369155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9606253582876595458246103 14409380374314893187369155)
            ·
              refine ⟨21614070561472339781053733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14409380374314893187369155 21614070561472339781053733)
              ·
                refine ⟨4052638230276063708947575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21614070561472339781053733 4052638230276063708947575)
                ·
                  refine ⟨6078957345414095563421363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4052638230276063708947575 6078957345414095563421363)
                  ·
                    refine ⟨9118436018121143345132045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6078957345414095563421363 9118436018121143345132045)
                    ·
                      refine ⟨3419413506795428754424517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9118436018121143345132045 3419413506795428754424517)
                      ·
                        rfl

theorem cell23_6659284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 4, 1, 1, 3].length) (baseStart_6659284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6659284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6659284 prefixEnd_6659284 := by exact prefixLift 6659284
  have htrace : WordTrace (prefixWord ++ tailWord_6659284) baseStart_6659284 baseEnd_6659284 := by
    simpa [prefixWord, tailWord_6659284, baseEnd_6659284] using wordTrace_append hprefix tailTrace_6659284
  have hstable : (prefixWord ++ tailWord_6659284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6659284).length < 2 ^ (prefixWord ++ tailWord_6659284).sum := by decide
  have hdescent : baseEnd_6659284 < baseStart_6659284 := by decide
  rcases family_descends (prefixWord ++ tailWord_6659284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6659296 : List Nat := [2, 1, 1, 3, 1, 6, 1, 8]
def baseStart_6659296 : Nat := 118140960795 + 6659296 * 2 ^ 59
def prefixEnd_6659296 : Nat := 4983230072969 + 3 ^ 40 * 6659296 * 2
def baseEnd_6659296 : Nat := 126645172909751211387943

theorem tailTrace_6659296 : CollatzResearch.WordTrace tailWord_6659296 prefixEnd_6659296 126645172909751211387943 := by
  unfold tailWord_6659296
  simp only [CollatzResearch.WordTrace]
  refine ⟨121442239441257692027730871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161922985921676922703641161 121442239441257692027730871)
  ·
    refine ⟨182163359161886538041596307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121442239441257692027730871 182163359161886538041596307)
    ·
      refine ⟨273245038742829807062394461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182163359161886538041596307 273245038742829807062394461)
      ·
        refine ⟨102466889528561177648397923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 273245038742829807062394461 102466889528561177648397923)
        ·
          refine ⟨153700334292841766472596885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102466889528561177648397923 153700334292841766472596885)
          ·
            refine ⟨7204703169976957803402979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 153700334292841766472596885 7204703169976957803402979)
            ·
              refine ⟨10807054754965436705104469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7204703169976957803402979 10807054754965436705104469)
              ·
                refine ⟨126645172909751211387943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10807054754965436705104469 126645172909751211387943)
                ·
                  rfl

theorem cell23_6659296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 1, 8].length) (baseStart_6659296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6659296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6659296 prefixEnd_6659296 := by exact prefixLift 6659296
  have htrace : WordTrace (prefixWord ++ tailWord_6659296) baseStart_6659296 baseEnd_6659296 := by
    simpa [prefixWord, tailWord_6659296, baseEnd_6659296] using wordTrace_append hprefix tailTrace_6659296
  have hstable : (prefixWord ++ tailWord_6659296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6659296).length < 2 ^ (prefixWord ++ tailWord_6659296).sum := by decide
  have hdescent : baseEnd_6659296 < baseStart_6659296 := by decide
  rcases family_descends (prefixWord ++ tailWord_6659296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6659319 : List Nat := [1, 1, 3, 1, 1, 1, 2, 3, 1, 4, 5]
def baseStart_6659319 : Nat := 118140960795 + 6659319 * 2 ^ 59
def prefixEnd_6659319 : Nat := 4983230072969 + 3 ^ 40 * 6659319 * 2
def baseEnd_6659319 : Nat := 3419431478618336117486855

theorem tailTrace_6659319 : CollatzResearch.WordTrace tailWord_6659319 prefixEnd_6659319 3419431478618336117486855 := by
  unfold tailWord_6659319
  simp only [CollatzResearch.WordTrace]
  refine ⟨242885317761432058983549011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161923545174288039322366007 242885317761432058983549011)
  ·
    refine ⟨364327976642148088475323517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242885317761432058983549011 364327976642148088475323517)
    ·
      refine ⟨136622991240805533178246319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 364327976642148088475323517 136622991240805533178246319)
      ·
        refine ⟨204934486861208299767369479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136622991240805533178246319 204934486861208299767369479)
        ·
          refine ⟨307401730291812449651054219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204934486861208299767369479 307401730291812449651054219)
          ·
            refine ⟨461102595437718674476581329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 307401730291812449651054219 461102595437718674476581329)
            ·
              refine ⟨345826946578289005857435997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 461102595437718674476581329 345826946578289005857435997)
              ·
                refine ⟨129685104966858377196538499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 345826946578289005857435997 129685104966858377196538499)
                ·
                  refine ⟨194527657450287565794807749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 129685104966858377196538499 194527657450287565794807749)
                  ·
                    refine ⟨36473935771928918586526453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 194527657450287565794807749 36473935771928918586526453)
                    ·
                      refine ⟨3419431478618336117486855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36473935771928918586526453 3419431478618336117486855)
                      ·
                        rfl

theorem cell23_6659319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 3, 1, 4, 5].length) (baseStart_6659319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6659319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6659319 prefixEnd_6659319 := by exact prefixLift 6659319
  have htrace : WordTrace (prefixWord ++ tailWord_6659319) baseStart_6659319 baseEnd_6659319 := by
    simpa [prefixWord, tailWord_6659319, baseEnd_6659319] using wordTrace_append hprefix tailTrace_6659319
  have hstable : (prefixWord ++ tailWord_6659319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6659319).length < 2 ^ (prefixWord ++ tailWord_6659319).sum := by decide
  have hdescent : baseEnd_6659319 < baseStart_6659319 := by decide
  rcases family_descends (prefixWord ++ tailWord_6659319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6659324 : List Nat := [2, 2, 2, 1, 5, 1, 2, 3, 1, 2, 2]
def baseStart_6659324 : Nat := 118140960795 + 6659324 * 2 ^ 59
def prefixEnd_6659324 : Nat := 4983230072969 + 3 ^ 40 * 6659324 * 2
def baseEnd_6659324 : Nat := 3419434046021608597924333

theorem tailTrace_6659324 : CollatzResearch.WordTrace tailWord_6659324 prefixEnd_6659324 3419434046021608597924333 := by
  unfold tailWord_6659324
  simp only [CollatzResearch.WordTrace]
  refine ⟨121442750063206972418740513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161923666750942629891654017 121442750063206972418740513)
  ·
    refine ⟨91082062547405229314055385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121442750063206972418740513 91082062547405229314055385)
    ·
      refine ⟨68311546910553921985541539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91082062547405229314055385 68311546910553921985541539)
      ·
        refine ⟨102467320365830882978312309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68311546910553921985541539 102467320365830882978312309)
        ·
          refine ⟨9606311284296645279216779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 102467320365830882978312309 9606311284296645279216779)
          ·
            refine ⟨14409466926444967918825169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9606311284296645279216779 14409466926444967918825169)
            ·
              refine ⟨10807100194833725939118877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14409466926444967918825169 10807100194833725939118877)
              ·
                refine ⟨4052662573062647227169579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10807100194833725939118877 4052662573062647227169579)
                ·
                  refine ⟨6078993859593970840754369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4052662573062647227169579 6078993859593970840754369)
                  ·
                    refine ⟨4559245394695478130565777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6078993859593970840754369 4559245394695478130565777)
                    ·
                      refine ⟨3419434046021608597924333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4559245394695478130565777 3419434046021608597924333)
                      ·
                        rfl

theorem cell23_6659324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 2, 3, 1, 2, 2].length) (baseStart_6659324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6659324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6659324 prefixEnd_6659324 := by exact prefixLift 6659324
  have htrace : WordTrace (prefixWord ++ tailWord_6659324) baseStart_6659324 baseEnd_6659324 := by
    simpa [prefixWord, tailWord_6659324, baseEnd_6659324] using wordTrace_append hprefix tailTrace_6659324
  have hstable : (prefixWord ++ tailWord_6659324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6659324).length < 2 ^ (prefixWord ++ tailWord_6659324).sum := by decide
  have hdescent : baseEnd_6659324 < baseStart_6659324 := by decide
  rcases family_descends (prefixWord ++ tailWord_6659324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6659340 : List Nat := [2, 2, 1, 2, 2, 3, 3, 2, 2, 1, 3]
def baseStart_6659340 : Nat := 118140960795 + 6659340 * 2 ^ 59
def prefixEnd_6659340 : Nat := 4983230072969 + 3 ^ 40 * 6659340 * 2
def baseEnd_6659340 : Nat := 3419442261712080535324259

theorem tailTrace_6659340 : CollatzResearch.WordTrace tailWord_6659340 prefixEnd_6659340 3419442261712080535324259 := by
  unfold tailWord_6659340
  simp only [CollatzResearch.WordTrace]
  refine ⟨121443041847177989785031737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161924055796237319713375649 121443041847177989785031737)
  ·
    refine ⟨91082281385383492338773803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121443041847177989785031737 91082281385383492338773803)
    ·
      refine ⟨136623422078075238508160705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91082281385383492338773803 136623422078075238508160705)
      ·
        refine ⟨102467566558556428881120529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136623422078075238508160705 102467566558556428881120529)
        ·
          refine ⟨76850674918917321660840397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102467566558556428881120529 76850674918917321660840397)
          ·
            refine ⟨28819003094593995622815149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76850674918917321660840397 28819003094593995622815149)
            ·
              refine ⟨10807126160472748358555681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28819003094593995622815149 10807126160472748358555681)
              ·
                refine ⟨8105344620354561268916761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10807126160472748358555681 8105344620354561268916761)
                ·
                  refine ⟨6079008465265920951687571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8105344620354561268916761 6079008465265920951687571)
                  ·
                    refine ⟨9118512697898881427531357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6079008465265920951687571 9118512697898881427531357)
                    ·
                      refine ⟨3419442261712080535324259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9118512697898881427531357 3419442261712080535324259)
                      ·
                        rfl

theorem cell23_6659340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 3, 2, 2, 1, 3].length) (baseStart_6659340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6659340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6659340 prefixEnd_6659340 := by exact prefixLift 6659340
  have htrace : WordTrace (prefixWord ++ tailWord_6659340) baseStart_6659340 baseEnd_6659340 := by
    simpa [prefixWord, tailWord_6659340, baseEnd_6659340] using wordTrace_append hprefix tailTrace_6659340
  have hstable : (prefixWord ++ tailWord_6659340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6659340).length < 2 ^ (prefixWord ++ tailWord_6659340).sum := by decide
  have hdescent : baseEnd_6659340 < baseStart_6659340 := by decide
  rcases family_descends (prefixWord ++ tailWord_6659340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6659356 : List Nat := [2, 2, 3, 1, 1, 1, 4, 1, 2, 6]
def baseStart_6659356 : Nat := 118140960795 + 6659356 * 2 ^ 59
def prefixEnd_6659356 : Nat := 4983230072969 + 3 ^ 40 * 6659356 * 2
def baseEnd_6659356 : Nat := 1139816825800850824241395

theorem tailTrace_6659356 : CollatzResearch.WordTrace tailWord_6659356 prefixEnd_6659356 1139816825800850824241395 := by
  unfold tailWord_6659356
  simp only [CollatzResearch.WordTrace]
  refine ⟨121443333631149007151322961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161924444841532009535097281 121443333631149007151322961)
  ·
    refine ⟨91082500223361755363492221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121443333631149007151322961 91082500223361755363492221)
    ·
      refine ⟨34155937583760658261309583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91082500223361755363492221 34155937583760658261309583)
      ·
        refine ⟨51233906375640987391964375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34155937583760658261309583 51233906375640987391964375)
        ·
          refine ⟨76850859563461481087946563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51233906375640987391964375 76850859563461481087946563)
          ·
            refine ⟨115276289345192221631919845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76850859563461481087946563 115276289345192221631919845)
            ·
              refine ⟨21614304252223541555984971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 115276289345192221631919845 21614304252223541555984971)
              ·
                refine ⟨32421456378335312333977457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21614304252223541555984971 32421456378335312333977457)
                ·
                  refine ⟨24316092283751484250483093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32421456378335312333977457 24316092283751484250483093)
                  ·
                    refine ⟨1139816825800850824241395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24316092283751484250483093 1139816825800850824241395)
                    ·
                      rfl

theorem cell23_6659356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 1, 2, 6].length) (baseStart_6659356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6659356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6659356 prefixEnd_6659356 := by exact prefixLift 6659356
  have htrace : WordTrace (prefixWord ++ tailWord_6659356) baseStart_6659356 baseEnd_6659356 := by
    simpa [prefixWord, tailWord_6659356, baseEnd_6659356] using wordTrace_append hprefix tailTrace_6659356
  have hstable : (prefixWord ++ tailWord_6659356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6659356).length < 2 ^ (prefixWord ++ tailWord_6659356).sum := by decide
  have hdescent : baseEnd_6659356 < baseStart_6659356 := by decide
  rcases family_descends (prefixWord ++ tailWord_6659356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6659369 : List Nat := [1, 2, 1, 1, 1, 1, 1, 2, 13]
def baseStart_6659369 : Nat := 118140960795 + 6659369 * 2 ^ 59
def prefixEnd_6659369 : Nat := 4983230072969 + 3 ^ 40 * 6659369 * 2
def baseEnd_6659369 : Nat := 379939683627895657984625

theorem tailTrace_6659369 : CollatzResearch.WordTrace tailWord_6659369 prefixEnd_6659369 379939683627895657984625 := by
  unfold tailWord_6659369
  simp only [CollatzResearch.WordTrace]
  refine ⟨242887141411250917522869161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161924760940833945015246107 242887141411250917522869161)
  ·
    refine ⟨182165356058438188142151871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242887141411250917522869161 182165356058438188142151871)
    ·
      refine ⟨273248034087657282213227807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182165356058438188142151871 273248034087657282213227807)
      ·
        refine ⟨409872051131485923319841711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273248034087657282213227807 409872051131485923319841711)
        ·
          refine ⟨614808076697228884979762567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 409872051131485923319841711 614808076697228884979762567)
          ·
            refine ⟨922212115045843327469643851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 614808076697228884979762567 922212115045843327469643851)
            ·
              refine ⟨1383318172568764991204465777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 922212115045843327469643851 1383318172568764991204465777)
              ·
                refine ⟨1037488629426573743403349333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1383318172568764991204465777 1037488629426573743403349333)
                ·
                  refine ⟨379939683627895657984625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 13 1037488629426573743403349333 379939683627895657984625)
                  ·
                    rfl

theorem cell23_6659369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 13].length) (baseStart_6659369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6659369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6659369 prefixEnd_6659369 := by exact prefixLift 6659369
  have htrace : WordTrace (prefixWord ++ tailWord_6659369) baseStart_6659369 baseEnd_6659369 := by
    simpa [prefixWord, tailWord_6659369, baseEnd_6659369] using wordTrace_append hprefix tailTrace_6659369
  have hstable : (prefixWord ++ tailWord_6659369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6659369).length < 2 ^ (prefixWord ++ tailWord_6659369).sum := by decide
  have hdescent : baseEnd_6659369 < baseStart_6659369 := by decide
  rcases family_descends (prefixWord ++ tailWord_6659369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6659380 : List Nat := [2, 5, 1, 1, 1, 1, 2, 1, 3, 4, 2]
def baseStart_6659380 : Nat := 118140960795 + 6659380 * 2 ^ 59
def prefixEnd_6659380 : Nat := 4983230072969 + 3 ^ 40 * 6659380 * 2
def baseEnd_6659380 : Nat := 3419462800938260378824075

theorem tailTrace_6659380 : CollatzResearch.WordTrace tailWord_6659380 prefixEnd_6659380 3419462800938260378824075 := by
  unfold tailWord_6659380
  simp only [CollatzResearch.WordTrace]
  refine ⟨121443771307105533200759797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161925028409474044267679729 121443771307105533200759797)
  ·
    refine ⟨11385353560041143737571231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 121443771307105533200759797 11385353560041143737571231)
    ·
      refine ⟨17078030340061715606356847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11385353560041143737571231 17078030340061715606356847)
      ·
        refine ⟨25617045510092573409535271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17078030340061715606356847 25617045510092573409535271)
        ·
          refine ⟨38425568265138860114302907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25617045510092573409535271 38425568265138860114302907)
          ·
            refine ⟨57638352397708290171454361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38425568265138860114302907 57638352397708290171454361)
            ·
              refine ⟨43228764298281217628590771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57638352397708290171454361 43228764298281217628590771)
              ·
                refine ⟨64843146447421826442886157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43228764298281217628590771 64843146447421826442886157)
                ·
                  refine ⟨24316179917783184916082309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64843146447421826442886157 24316179917783184916082309)
                  ·
                    refine ⟨4559283734584347171765433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24316179917783184916082309 4559283734584347171765433)
                    ·
                      refine ⟨3419462800938260378824075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4559283734584347171765433 3419462800938260378824075)
                      ·
                        rfl

theorem cell23_6659380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 2, 1, 3, 4, 2].length) (baseStart_6659380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6659380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6659380 prefixEnd_6659380 := by exact prefixLift 6659380
  have htrace : WordTrace (prefixWord ++ tailWord_6659380) baseStart_6659380 baseEnd_6659380 := by
    simpa [prefixWord, tailWord_6659380, baseEnd_6659380] using wordTrace_append hprefix tailTrace_6659380
  have hstable : (prefixWord ++ tailWord_6659380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6659380).length < 2 ^ (prefixWord ++ tailWord_6659380).sum := by decide
  have hdescent : baseEnd_6659380 < baseStart_6659380 := by decide
  rcases family_descends (prefixWord ++ tailWord_6659380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6659416 : List Nat := [2, 1, 2, 2, 1, 1, 3, 2, 4, 5]
def baseStart_6659416 : Nat := 118140960795 + 6659416 * 2 ^ 59
def prefixEnd_6659416 : Nat := 4983230072969 + 3 ^ 40 * 6659416 * 2
def baseEnd_6659416 : Nat := 1139827095413940745991303

theorem tailTrace_6659416 : CollatzResearch.WordTrace tailWord_6659416 prefixEnd_6659416 1139827095413940745991303 := by
  unfold tailWord_6659416
  simp only [CollatzResearch.WordTrace]
  refine ⟨121444427821040322274915051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161925903761387096366553401 121444427821040322274915051)
  ·
    refine ⟨182166641731560483412372577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121444427821040322274915051 182166641731560483412372577)
    ·
      refine ⟨136624981298670362559279433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182166641731560483412372577 136624981298670362559279433)
      ·
        refine ⟨102468735974002771919459575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136624981298670362559279433 102468735974002771919459575)
        ·
          refine ⟨153703103961004157879189363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102468735974002771919459575 153703103961004157879189363)
          ·
            refine ⟨230554655941506236818784045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153703103961004157879189363 230554655941506236818784045)
            ·
              refine ⟨86457995978064838807044017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 230554655941506236818784045 86457995978064838807044017)
              ·
                refine ⟨64843496983548629105283013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86457995978064838807044017 64843496983548629105283013)
                ·
                  refine ⟨12158155684415367957240565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64843496983548629105283013 12158155684415367957240565)
                  ·
                    refine ⟨1139827095413940745991303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12158155684415367957240565 1139827095413940745991303)
                    ·
                      rfl

theorem cell23_6659416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 2, 4, 5].length) (baseStart_6659416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6659416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6659416 prefixEnd_6659416 := by exact prefixLift 6659416
  have htrace : WordTrace (prefixWord ++ tailWord_6659416) baseStart_6659416 baseEnd_6659416 := by
    simpa [prefixWord, tailWord_6659416, baseEnd_6659416] using wordTrace_append hprefix tailTrace_6659416
  have hstable : (prefixWord ++ tailWord_6659416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6659416).length < 2 ^ (prefixWord ++ tailWord_6659416).sum := by decide
  have hdescent : baseEnd_6659416 < baseStart_6659416 := by decide
  rcases family_descends (prefixWord ++ tailWord_6659416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6659453 : List Nat := [1, 4, 1, 1, 2, 2, 1, 4, 2, 1, 4]
def baseStart_6659453 : Nat := 118140960795 + 6659453 * 2 ^ 59
def prefixEnd_6659453 : Nat := 4983230072969 + 3 ^ 40 * 6659453 * 2
def baseEnd_6659453 : Nat := 3419500285026038593211239

theorem tailTrace_6659453 : CollatzResearch.WordTrace tailWord_6659453 prefixEnd_6659453 3419500285026038593211239 := by
  unfold tailWord_6659453
  simp only [CollatzResearch.WordTrace]
  refine ⟨242890205142946599868927013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161926803428631066579284675 242890205142946599868927013)
  ·
    refine ⟨45541913464302487475423815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 242890205142946599868927013 45541913464302487475423815)
    ·
      refine ⟨68312870196453731213135723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45541913464302487475423815 68312870196453731213135723)
      ·
        refine ⟨102469305294680596819703585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68312870196453731213135723 102469305294680596819703585)
        ·
          refine ⟨76851978971010447614777689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102469305294680596819703585 76851978971010447614777689)
          ·
            refine ⟨57638984228257835711083267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76851978971010447614777689 57638984228257835711083267)
            ·
              refine ⟨86458476342386753566624901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57638984228257835711083267 86458476342386753566624901)
              ·
                refine ⟨16210964314197516293742169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 86458476342386753566624901 16210964314197516293742169)
                ·
                  refine ⟨12158223235648137220306627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16210964314197516293742169 12158223235648137220306627)
                  ·
                    refine ⟨18237334853472205830459941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12158223235648137220306627 18237334853472205830459941)
                    ·
                      refine ⟨3419500285026038593211239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18237334853472205830459941 3419500285026038593211239)
                      ·
                        rfl

theorem cell23_6659453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 4, 2, 1, 4].length) (baseStart_6659453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6659453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6659453 prefixEnd_6659453 := by exact prefixLift 6659453
  have htrace : WordTrace (prefixWord ++ tailWord_6659453) baseStart_6659453 baseEnd_6659453 := by
    simpa [prefixWord, tailWord_6659453, baseEnd_6659453] using wordTrace_append hprefix tailTrace_6659453
  have hstable : (prefixWord ++ tailWord_6659453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6659453).length < 2 ^ (prefixWord ++ tailWord_6659453).sum := by decide
  have hdescent : baseEnd_6659453 < baseStart_6659453 := by decide
  rcases family_descends (prefixWord ++ tailWord_6659453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6659454 : List Nat := [4, 2, 3, 2, 1, 1, 1, 4, 5]
def baseStart_6659454 : Nat := 118140960795 + 6659454 * 2 ^ 59
def prefixEnd_6659454 : Nat := 4983230072969 + 3 ^ 40 * 6659454 * 2
def baseEnd_6659454 : Nat := 379944533167410343255415

theorem tailTrace_6659454 : CollatzResearch.WordTrace tailWord_6659454 prefixEnd_6659454 379944533167410343255415 := by
  unfold tailWord_6659454
  simp only [CollatzResearch.WordTrace]
  refine ⟨30361280201992872129964177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 161926827743961984693142277 30361280201992872129964177)
  ·
    refine ⟨22770960151494654097473133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30361280201992872129964177 22770960151494654097473133)
    ·
      refine ⟨8539110056810495286552425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22770960151494654097473133 8539110056810495286552425)
      ·
        refine ⟨6404332542607871464914319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8539110056810495286552425 6404332542607871464914319)
        ·
          refine ⟨9606498813911807197371479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6404332542607871464914319 9606498813911807197371479)
          ·
            refine ⟨14409748220867710796057219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9606498813911807197371479 14409748220867710796057219)
            ·
              refine ⟨21614622331301566194085829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14409748220867710796057219 21614622331301566194085829)
              ·
                refine ⟨4052741687119043661391093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21614622331301566194085829 4052741687119043661391093)
                ·
                  refine ⟨379944533167410343255415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4052741687119043661391093 379944533167410343255415)
                  ·
                    rfl

theorem cell23_6659454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 4, 5].length) (baseStart_6659454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6659454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6659454 prefixEnd_6659454 := by exact prefixLift 6659454
  have htrace : WordTrace (prefixWord ++ tailWord_6659454) baseStart_6659454 baseEnd_6659454 := by
    simpa [prefixWord, tailWord_6659454, baseEnd_6659454] using wordTrace_append hprefix tailTrace_6659454
  have hstable : (prefixWord ++ tailWord_6659454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6659454).length < 2 ^ (prefixWord ++ tailWord_6659454).sum := by decide
  have hdescent : baseEnd_6659454 < baseStart_6659454 := by decide
  rcases family_descends (prefixWord ++ tailWord_6659454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6659484 : List Nat := [2, 2, 3, 4, 2, 1, 1, 1, 2, 5]
def baseStart_6659484 : Nat := 118140960795 + 6659484 * 2 ^ 59
def prefixEnd_6659484 : Nat := 4983230072969 + 3 ^ 40 * 6659484 * 2
def baseEnd_6659484 : Nat := 1139838734308775990641199

theorem tailTrace_6659484 : CollatzResearch.WordTrace tailWord_6659484 prefixEnd_6659484 1139838734308775990641199 := by
  unfold tailWord_6659484
  simp only [CollatzResearch.WordTrace]
  refine ⟨121445667902917146081652753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161927557203889528108870337 121445667902917146081652753)
  ·
    refine ⟨91084250927187859561239565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121445667902917146081652753 91084250927187859561239565)
    ·
      refine ⟨34156594097695447335464837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91084250927187859561239565 34156594097695447335464837)
      ·
        refine ⟨6404361393317896375399657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34156594097695447335464837 6404361393317896375399657)
        ·
          refine ⟨4803271044988422281549743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6404361393317896375399657 4803271044988422281549743)
          ·
            refine ⟨7204906567482633422324615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4803271044988422281549743 7204906567482633422324615)
            ·
              refine ⟨10807359851223950133486923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7204906567482633422324615 10807359851223950133486923)
              ·
                refine ⟨16211039776835925200230385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10807359851223950133486923 16211039776835925200230385)
                ·
                  refine ⟨12158279832626943900172789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16211039776835925200230385 12158279832626943900172789)
                  ·
                    refine ⟨1139838734308775990641199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12158279832626943900172789 1139838734308775990641199)
                    ·
                      rfl

theorem cell23_6659484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 1, 1, 2, 5].length) (baseStart_6659484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6659484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6659484 prefixEnd_6659484 := by exact prefixLift 6659484
  have htrace : WordTrace (prefixWord ++ tailWord_6659484) baseStart_6659484 baseEnd_6659484 := by
    simpa [prefixWord, tailWord_6659484, baseEnd_6659484] using wordTrace_append hprefix tailTrace_6659484
  have hstable : (prefixWord ++ tailWord_6659484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6659484).length < 2 ^ (prefixWord ++ tailWord_6659484).sum := by decide
  have hdescent : baseEnd_6659484 < baseStart_6659484 := by decide
  rcases family_descends (prefixWord ++ tailWord_6659484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6659490 : List Nat := [3, 3, 1, 2, 1, 3, 1, 1, 1, 4, 3]
def baseStart_6659490 : Nat := 118140960795 + 6659490 * 2 ^ 59
def prefixEnd_6659490 : Nat := 4983230072969 + 3 ^ 40 * 6659490 * 2
def baseEnd_6659490 : Nat := 3419519283810254948448569

theorem tailTrace_6659490 : CollatzResearch.WordTrace tailWord_6659490 prefixEnd_6659490 3419519283810254948448569 := by
  unfold tailWord_6659490
  simp only [CollatzResearch.WordTrace]
  refine ⟨60722888660953138797005981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161927703095875036792015949 60722888660953138797005981)
  ·
    refine ⟨22771083247857427048877243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60722888660953138797005981 22771083247857427048877243)
    ·
      refine ⟨34156624871786140573315865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22771083247857427048877243 34156624871786140573315865)
      ·
        refine ⟨25617468653839605429986899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34156624871786140573315865 25617468653839605429986899)
        ·
          refine ⟨38426202980759408144980349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25617468653839605429986899 38426202980759408144980349)
          ·
            refine ⟨14409826117784778054367631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38426202980759408144980349 14409826117784778054367631)
            ·
              refine ⟨21614739176677167081551447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14409826117784778054367631 21614739176677167081551447)
              ·
                refine ⟨32422108765015750622327171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21614739176677167081551447 32422108765015750622327171)
                ·
                  refine ⟨48633163147523625933490757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32422108765015750622327171 48633163147523625933490757)
                  ·
                    refine ⟨9118718090160679862529517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48633163147523625933490757 9118718090160679862529517)
                    ·
                      refine ⟨3419519283810254948448569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9118718090160679862529517 3419519283810254948448569)
                      ·
                        rfl

theorem cell23_6659490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 1, 1, 4, 3].length) (baseStart_6659490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6659490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6659490 prefixEnd_6659490 := by exact prefixLift 6659490
  have htrace : WordTrace (prefixWord ++ tailWord_6659490) baseStart_6659490 baseEnd_6659490 := by
    simpa [prefixWord, tailWord_6659490, baseEnd_6659490] using wordTrace_append hprefix tailTrace_6659490
  have hstable : (prefixWord ++ tailWord_6659490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6659490).length < 2 ^ (prefixWord ++ tailWord_6659490).sum := by decide
  have hdescent : baseEnd_6659490 < baseStart_6659490 := by decide
  rcases family_descends (prefixWord ++ tailWord_6659490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6659520 : List Nat := [2, 1, 1, 2, 3, 1, 3, 3, 3, 1, 3]
def baseStart_6659520 : Nat := 118140960795 + 6659520 * 2 ^ 59
def prefixEnd_6659520 : Nat := 4983230072969 + 3 ^ 40 * 6659520 * 2
def baseEnd_6659520 : Nat := 3419534688229889831073431

theorem tailTrace_6659520 : CollatzResearch.WordTrace tailWord_6659520 prefixEnd_6659520 3419534688229889831073431 := by
  unfold tailWord_6659520
  simp only [CollatzResearch.WordTrace]
  refine ⟨121446324416851935155808007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161928432555802580207744009 121446324416851935155808007)
  ·
    refine ⟨182169486625277902733712011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121446324416851935155808007 182169486625277902733712011)
    ·
      refine ⟨273254229937916854100568017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182169486625277902733712011 273254229937916854100568017)
      ·
        refine ⟨204940672453437640575426013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 273254229937916854100568017 204940672453437640575426013)
        ·
          refine ⟨76852752170039115215784755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 204940672453437640575426013 76852752170039115215784755)
          ·
            refine ⟨115279128255058672823677133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76852752170039115215784755 115279128255058672823677133)
            ·
              refine ⟨43229673095647002308878925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 115279128255058672823677133 43229673095647002308878925)
              ·
                refine ⟨16211127410867625865829597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43229673095647002308878925 16211127410867625865829597)
                ·
                  refine ⟨6079172779075359699686099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16211127410867625865829597 6079172779075359699686099)
                  ·
                    refine ⟨9118759168613039549529149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6079172779075359699686099 9118759168613039549529149)
                    ·
                      refine ⟨3419534688229889831073431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9118759168613039549529149 3419534688229889831073431)
                      ·
                        rfl

theorem cell23_6659520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 3, 3, 1, 3].length) (baseStart_6659520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6659520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6659520 prefixEnd_6659520 := by exact prefixLift 6659520
  have htrace : WordTrace (prefixWord ++ tailWord_6659520) baseStart_6659520 baseEnd_6659520 := by
    simpa [prefixWord, tailWord_6659520, baseEnd_6659520] using wordTrace_append hprefix tailTrace_6659520
  have hstable : (prefixWord ++ tailWord_6659520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6659520).length < 2 ^ (prefixWord ++ tailWord_6659520).sum := by decide
  have hdescent : baseEnd_6659520 < baseStart_6659520 := by decide
  rcases family_descends (prefixWord ++ tailWord_6659520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6659530 : List Nat := [3, 1, 2, 1, 2, 3, 1, 2, 1, 5, 2]
def baseStart_6659530 : Nat := 118140960795 + 6659530 * 2 ^ 59
def prefixEnd_6659530 : Nat := 4983230072969 + 3 ^ 40 * 6659530 * 2
def baseEnd_6659530 : Nat := 3419539823036434791948385

theorem tailTrace_6659530 : CollatzResearch.WordTrace tailWord_6659530 prefixEnd_6659530 3419539823036434791948385 := by
  unfold tailWord_6659530
  simp only [CollatzResearch.WordTrace]
  refine ⟨60723253390916910504870011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161928675709111761346320029 60723253390916910504870011)
  ·
    refine ⟨91084880086375365757305017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60723253390916910504870011 91084880086375365757305017)
    ·
      refine ⟨68313660064781524317978763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91084880086375365757305017 68313660064781524317978763)
      ·
        refine ⟨102470490097172286476968145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68313660064781524317978763 102470490097172286476968145)
        ·
          refine ⟨76852867572879214857726109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102470490097172286476968145 76852867572879214857726109)
          ·
            refine ⟨28819825339829705571647291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76852867572879214857726109 28819825339829705571647291)
            ·
              refine ⟨43229738009744558357470937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28819825339829705571647291 43229738009744558357470937)
              ·
                refine ⟨32422303507308418768103203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43229738009744558357470937 32422303507308418768103203)
                ·
                  refine ⟨48633455260962628152154805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32422303507308418768103203 48633455260962628152154805)
                  ·
                    refine ⟨4559386430715246389264513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48633455260962628152154805 4559386430715246389264513)
                    ·
                      refine ⟨3419539823036434791948385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4559386430715246389264513 3419539823036434791948385)
                      ·
                        rfl

theorem cell23_6659530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 2, 1, 5, 2].length) (baseStart_6659530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6659530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6659530 prefixEnd_6659530 := by exact prefixLift 6659530
  have htrace : WordTrace (prefixWord ++ tailWord_6659530) baseStart_6659530 baseEnd_6659530 := by
    simpa [prefixWord, tailWord_6659530, baseEnd_6659530] using wordTrace_append hprefix tailTrace_6659530
  have hstable : (prefixWord ++ tailWord_6659530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6659530).length < 2 ^ (prefixWord ++ tailWord_6659530).sum := by decide
  have hdescent : baseEnd_6659530 < baseStart_6659530 := by decide
  rcases family_descends (prefixWord ++ tailWord_6659530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6659543 : List Nat := [1, 1, 3, 2, 1, 1, 1, 5, 3, 1, 4]
def baseStart_6659543 : Nat := 118140960795 + 6659543 * 2 ^ 59
def prefixEnd_6659543 : Nat := 4983230072969 + 3 ^ 40 * 6659543 * 2
def baseEnd_6659543 : Nat := 3419546498284943241085825

theorem tailTrace_6659543 : CollatzResearch.WordTrace tailWord_6659543 prefixEnd_6659543 3419546498284943241085825 := by
  unfold tailWord_6659543
  simp only [CollatzResearch.WordTrace]
  refine ⟨242893487712620545239703283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161928991808413696826468855 242893487712620545239703283)
  ·
    refine ⟨364340231568930817859554925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242893487712620545239703283 364340231568930817859554925)
    ·
      refine ⟨136627586838349056697333097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 364340231568930817859554925 136627586838349056697333097)
      ·
        refine ⟨102470690128761792522999823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136627586838349056697333097 102470690128761792522999823)
        ·
          refine ⟨153706035193142688784499735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102470690128761792522999823 153706035193142688784499735)
          ·
            refine ⟨230559052789714033176749603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153706035193142688784499735 230559052789714033176749603)
            ·
              refine ⟨345838579184571049765124405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 230559052789714033176749603 345838579184571049765124405)
              ·
                refine ⟨32422366798553535915480413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 345838579184571049765124405 32422366798553535915480413)
                ·
                  refine ⟨12158387549457575968305155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32422366798553535915480413 12158387549457575968305155)
                  ·
                    refine ⟨18237581324186363952457733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12158387549457575968305155 18237581324186363952457733)
                    ·
                      refine ⟨3419546498284943241085825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18237581324186363952457733 3419546498284943241085825)
                      ·
                        rfl

theorem cell23_6659543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 5, 3, 1, 4].length) (baseStart_6659543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6659543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6659543 prefixEnd_6659543 := by exact prefixLift 6659543
  have htrace : WordTrace (prefixWord ++ tailWord_6659543) baseStart_6659543 baseEnd_6659543 := by
    simpa [prefixWord, tailWord_6659543, baseEnd_6659543] using wordTrace_append hprefix tailTrace_6659543
  have hstable : (prefixWord ++ tailWord_6659543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6659543).length < 2 ^ (prefixWord ++ tailWord_6659543).sum := by decide
  have hdescent : baseEnd_6659543 < baseStart_6659543 := by decide
  rcases family_descends (prefixWord ++ tailWord_6659543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6659560 : List Nat := [2, 1, 4, 1, 1, 2, 1, 5, 1, 1, 4]
def baseStart_6659560 : Nat := 118140960795 + 6659560 * 2 ^ 59
def prefixEnd_6659560 : Nat := 4983230072969 + 3 ^ 40 * 6659560 * 2
def baseEnd_6659560 : Nat := 3419555227456069674573247

theorem tailTrace_6659560 : CollatzResearch.WordTrace tailWord_6659560 prefixEnd_6659560 3419555227456069674573247 := by
  unfold tailWord_6659560
  simp only [CollatzResearch.WordTrace]
  refine ⟨121447053876779478571536067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161929405169039304762048089 121447053876779478571536067)
  ·
    refine ⟨182170580815169217857304101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121447053876779478571536067 182170580815169217857304101)
    ·
      refine ⟨34156983902844228348244519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 182170580815169217857304101 34156983902844228348244519)
      ·
        refine ⟨51235475854266342522366779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34156983902844228348244519 51235475854266342522366779)
        ·
          refine ⟨76853213781399513783550169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51235475854266342522366779 76853213781399513783550169)
          ·
            refine ⟨57639910336049635337662627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76853213781399513783550169 57639910336049635337662627)
            ·
              refine ⟨86459865504074453006493941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57639910336049635337662627 86459865504074453006493941)
              ·
                refine ⟨8105612391006979969358807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 86459865504074453006493941 8105612391006979969358807)
                ·
                  refine ⟨12158418586510469954038211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8105612391006979969358807 12158418586510469954038211)
                  ·
                    refine ⟨18237627879765704931057317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12158418586510469954038211 18237627879765704931057317)
                    ·
                      refine ⟨3419555227456069674573247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18237627879765704931057317 3419555227456069674573247)
                      ·
                        rfl

theorem cell23_6659560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 5, 1, 1, 4].length) (baseStart_6659560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6659560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6659560 prefixEnd_6659560 := by exact prefixLift 6659560
  have htrace : WordTrace (prefixWord ++ tailWord_6659560) baseStart_6659560 baseEnd_6659560 := by
    simpa [prefixWord, tailWord_6659560, baseEnd_6659560] using wordTrace_append hprefix tailTrace_6659560
  have hstable : (prefixWord ++ tailWord_6659560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6659560).length < 2 ^ (prefixWord ++ tailWord_6659560).sum := by decide
  have hdescent : baseEnd_6659560 < baseStart_6659560 := by decide
  rcases family_descends (prefixWord ++ tailWord_6659560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6659630 : List Nat := [4, 1, 3, 1, 2, 1, 1, 1, 2, 7]
def baseStart_6659630 : Nat := 118140960795 + 6659630 * 2 ^ 59
def prefixEnd_6659630 : Nat := 4983230072969 + 3 ^ 40 * 6659630 * 2
def baseEnd_6659630 : Nat := 1139863723700628133565975

theorem tailTrace_6659630 : CollatzResearch.WordTrace tailWord_6659630 prefixEnd_6659630 1139863723700628133565975 := by
  unfold tailWord_6659630
  simp only [CollatzResearch.WordTrace]
  refine ⟨30362082607913169887265043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 161931107242203572732080229 30362082607913169887265043)
  ·
    refine ⟨45543123911869754830897565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30362082607913169887265043 45543123911869754830897565)
    ·
      refine ⟨17078671466951158061586587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45543123911869754830897565 17078671466951158061586587)
      ·
        refine ⟨25618007200426737092379881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17078671466951158061586587 25618007200426737092379881)
        ·
          refine ⟨19213505400320052819284911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25618007200426737092379881 19213505400320052819284911)
          ·
            refine ⟨28820258100480079228927367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19213505400320052819284911 28820258100480079228927367)
            ·
              refine ⟨43230387150720118843391051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28820258100480079228927367 43230387150720118843391051)
              ·
                refine ⟨64845580726080178265086577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43230387150720118843391051 64845580726080178265086577)
                ·
                  refine ⟨48634185544560133698814933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64845580726080178265086577 48634185544560133698814933)
                  ·
                    refine ⟨1139863723700628133565975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48634185544560133698814933 1139863723700628133565975)
                    ·
                      rfl

theorem cell23_6659630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 1, 2, 7].length) (baseStart_6659630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6659630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6659630 prefixEnd_6659630 := by exact prefixLift 6659630
  have htrace : WordTrace (prefixWord ++ tailWord_6659630) baseStart_6659630 baseEnd_6659630 := by
    simpa [prefixWord, tailWord_6659630, baseEnd_6659630] using wordTrace_append hprefix tailTrace_6659630
  have hstable : (prefixWord ++ tailWord_6659630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6659630).length < 2 ^ (prefixWord ++ tailWord_6659630).sum := by decide
  have hdescent : baseEnd_6659630 < baseStart_6659630 := by decide
  rcases family_descends (prefixWord ++ tailWord_6659630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6659637 : List Nat := [1, 3, 3, 1, 1, 3, 1, 2, 3, 3, 2]
def baseStart_6659637 : Nat := 118140960795 + 6659637 * 2 ^ 59
def prefixEnd_6659637 : Nat := 4983230072969 + 3 ^ 40 * 6659637 * 2
def baseEnd_6659637 : Nat := 3419594765466465873310393

theorem tailTrace_6659637 : CollatzResearch.WordTrace tailWord_6659637 prefixEnd_6659637 3419594765466465873310393 := by
  unfold tailWord_6659637
  simp only [CollatzResearch.WordTrace]
  refine ⟨242896916174279999293625165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161931277449519999529083443 242896916174279999293625165)
  ·
    refine ⟨91086343565354999735109437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 242896916174279999293625165 91086343565354999735109437)
    ·
      refine ⟨34157378837008124900666039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91086343565354999735109437 34157378837008124900666039)
      ·
        refine ⟨51236068255512187350999059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34157378837008124900666039 51236068255512187350999059)
        ·
          refine ⟨76854102383268281026498589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51236068255512187350999059 76854102383268281026498589)
          ·
            refine ⟨28820288393725605384936971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76854102383268281026498589 28820288393725605384936971)
            ·
              refine ⟨43230432590588408077405457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28820288393725605384936971 43230432590588408077405457)
              ·
                refine ⟨32422824442941306058054093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43230432590588408077405457 32422824442941306058054093)
                ·
                  refine ⟨12158559166102989771770285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32422824442941306058054093 12158559166102989771770285)
                  ·
                    refine ⟨4559459687288621164413857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12158559166102989771770285 4559459687288621164413857)
                    ·
                      refine ⟨3419594765466465873310393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4559459687288621164413857 3419594765466465873310393)
                      ·
                        rfl

theorem cell23_6659637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 2, 3, 3, 2].length) (baseStart_6659637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6659637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6659637 prefixEnd_6659637 := by exact prefixLift 6659637
  have htrace : WordTrace (prefixWord ++ tailWord_6659637) baseStart_6659637 baseEnd_6659637 := by
    simpa [prefixWord, tailWord_6659637, baseEnd_6659637] using wordTrace_append hprefix tailTrace_6659637
  have hstable : (prefixWord ++ tailWord_6659637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6659637).length < 2 ^ (prefixWord ++ tailWord_6659637).sum := by decide
  have hdescent : baseEnd_6659637 < baseStart_6659637 := by decide
  rcases family_descends (prefixWord ++ tailWord_6659637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6659663 : List Nat := [1, 1, 2, 1, 1, 2, 3, 1, 3, 4, 4]
def baseStart_6659663 : Nat := 118140960795 + 6659663 * 2 ^ 59
def prefixEnd_6659663 : Nat := 4983230072969 + 3 ^ 40 * 6659663 * 2
def baseEnd_6659663 : Nat := 3419608115963482771585273

theorem tailTrace_6659663 : CollatzResearch.WordTrace tailWord_6659663 prefixEnd_6659663 3419608115963482771585273 := by
  unfold tailWord_6659663
  simp only [CollatzResearch.WordTrace]
  refine ⟨242897864472185805734071643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161931909648123870489381095 242897864472185805734071643)
  ·
    refine ⟨364346796708278708601107465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242897864472185805734071643 364346796708278708601107465)
    ·
      refine ⟨273260097531209031450830599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 364346796708278708601107465 273260097531209031450830599)
      ·
        refine ⟨409890146296813547176245899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273260097531209031450830599 409890146296813547176245899)
        ·
          refine ⟨614835219445220320764368849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 409890146296813547176245899 614835219445220320764368849)
          ·
            refine ⟨461126414583915240573276637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 614835219445220320764368849 461126414583915240573276637)
            ·
              refine ⟨172922405468968215214978739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 461126414583915240573276637 172922405468968215214978739)
              ·
                refine ⟨259383608203452322822468109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 172922405468968215214978739 259383608203452322822468109)
                ·
                  refine ⟨97268853076294621058425541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 259383608203452322822468109 97268853076294621058425541)
                  ·
                    refine ⟨18237909951805241448454789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 97268853076294621058425541 18237909951805241448454789)
                    ·
                      refine ⟨3419608115963482771585273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18237909951805241448454789 3419608115963482771585273)
                      ·
                        rfl

theorem cell23_6659663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 3, 4, 4].length) (baseStart_6659663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6659663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6659663 prefixEnd_6659663 := by exact prefixLift 6659663
  have htrace : WordTrace (prefixWord ++ tailWord_6659663) baseStart_6659663 baseEnd_6659663 := by
    simpa [prefixWord, tailWord_6659663, baseEnd_6659663] using wordTrace_append hprefix tailTrace_6659663
  have hstable : (prefixWord ++ tailWord_6659663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6659663).length < 2 ^ (prefixWord ++ tailWord_6659663).sum := by decide
  have hdescent : baseEnd_6659663 < baseStart_6659663 := by decide
  rcases family_descends (prefixWord ++ tailWord_6659663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6659671 : List Nat := [1, 1, 3, 2, 2, 5, 2, 1, 1, 3, 2]
def baseStart_6659671 : Nat := 118140960795 + 6659671 * 2 ^ 59
def prefixEnd_6659671 : Nat := 4983230072969 + 3 ^ 40 * 6659671 * 2
def baseEnd_6659671 : Nat := 3419612223808718740285237

theorem tailTrace_6659671 : CollatzResearch.WordTrace tailWord_6659671 prefixEnd_6659671 3419612223808718740285237 := by
  unfold tailWord_6659671
  simp only [CollatzResearch.WordTrace]
  refine ⟨242898156256156823100362867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161932104170771215400241911 242898156256156823100362867)
  ·
    refine ⟨364347234384235234650544301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242898156256156823100362867 364347234384235234650544301)
    ·
      refine ⟨136630212894088212993954113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 364347234384235234650544301 136630212894088212993954113)
      ·
        refine ⟨102472659670566159745465585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136630212894088212993954113 102472659670566159745465585)
        ·
          refine ⟨76854494752924619809099189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102472659670566159745465585 76854494752924619809099189)
          ·
            refine ⟨7205108883086683107103049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 76854494752924619809099189 7205108883086683107103049)
            ·
              refine ⟨5403831662315012330327287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7205108883086683107103049 5403831662315012330327287)
              ·
                refine ⟨8105747493472518495490931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5403831662315012330327287 8105747493472518495490931)
                ·
                  refine ⟨12158621240208777743236397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8105747493472518495490931 12158621240208777743236397)
                  ·
                    refine ⟨4559482965078291653713649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12158621240208777743236397 4559482965078291653713649)
                    ·
                      refine ⟨3419612223808718740285237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4559482965078291653713649 3419612223808718740285237)
                      ·
                        rfl

theorem cell23_6659671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 2, 1, 1, 3, 2].length) (baseStart_6659671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6659671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6659671 prefixEnd_6659671 := by exact prefixLift 6659671
  have htrace : WordTrace (prefixWord ++ tailWord_6659671) baseStart_6659671 baseEnd_6659671 := by
    simpa [prefixWord, tailWord_6659671, baseEnd_6659671] using wordTrace_append hprefix tailTrace_6659671
  have hstable : (prefixWord ++ tailWord_6659671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6659671).length < 2 ^ (prefixWord ++ tailWord_6659671).sum := by decide
  have hdescent : baseEnd_6659671 < baseStart_6659671 := by decide
  rcases family_descends (prefixWord ++ tailWord_6659671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6659684 : List Nat := [2, 3, 1, 1, 2, 4, 1, 1, 4, 2, 2]
def baseStart_6659684 : Nat := 118140960795 + 6659684 * 2 ^ 59
def prefixEnd_6659684 : Nat := 4983230072969 + 3 ^ 40 * 6659684 * 2
def baseEnd_6659684 : Nat := 3419618899057227189422677

theorem tailTrace_6659684 : CollatzResearch.WordTrace tailWord_6659684 prefixEnd_6659684 3419618899057227189422677 := by
  unfold tailWord_6659684
  simp only [CollatzResearch.WordTrace]
  refine ⟨121449315202554863160293053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161932420270073150880390737 121449315202554863160293053)
  ·
    refine ⟨45543493200958073685109895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121449315202554863160293053 45543493200958073685109895)
    ·
      refine ⟨68315239801437110527664843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45543493200958073685109895 68315239801437110527664843)
      ·
        refine ⟨102472859702155665791497265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68315239801437110527664843 102472859702155665791497265)
        ·
          refine ⟨76854644776616749343622949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102472859702155665791497265 76854644776616749343622949)
          ·
            refine ⟨14410245895615640501929303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76854644776616749343622949 14410245895615640501929303)
            ·
              refine ⟨21615368843423460752893955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14410245895615640501929303 21615368843423460752893955)
              ·
                refine ⟨32423053265135191129340933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21615368843423460752893955 32423053265135191129340933)
                ·
                  refine ⟨6079322487212848336751425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32423053265135191129340933 6079322487212848336751425)
                  ·
                    refine ⟨4559491865409636252563569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6079322487212848336751425 4559491865409636252563569)
                    ·
                      refine ⟨3419618899057227189422677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4559491865409636252563569 3419618899057227189422677)
                      ·
                        rfl

theorem cell23_6659684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 1, 1, 4, 2, 2].length) (baseStart_6659684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6659684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6659684 prefixEnd_6659684 := by exact prefixLift 6659684
  have htrace : WordTrace (prefixWord ++ tailWord_6659684) baseStart_6659684 baseEnd_6659684 := by
    simpa [prefixWord, tailWord_6659684, baseEnd_6659684] using wordTrace_append hprefix tailTrace_6659684
  have hstable : (prefixWord ++ tailWord_6659684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6659684).length < 2 ^ (prefixWord ++ tailWord_6659684).sum := by decide
  have hdescent : baseEnd_6659684 < baseStart_6659684 := by decide
  rcases family_descends (prefixWord ++ tailWord_6659684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6659690 : List Nat := [3, 1, 3, 2, 1, 2, 1, 3, 7]
def baseStart_6659690 : Nat := 118140960795 + 6659690 * 2 ^ 59
def prefixEnd_6659690 : Nat := 4983230072969 + 3 ^ 40 * 6659690 * 2
def baseEnd_6659690 : Nat := 379957997771239351771961

theorem tailTrace_6659690 : CollatzResearch.WordTrace tailWord_6659690 prefixEnd_6659690 379957997771239351771961 := by
  unfold tailWord_6659690
  simp only [CollatzResearch.WordTrace]
  refine ⟨60724712310771997336326131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161932566162058659563536349 60724712310771997336326131)
  ·
    refine ⟨91087068466157996004489197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60724712310771997336326131 91087068466157996004489197)
    ·
      refine ⟨34157650674809248501683449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91087068466157996004489197 34157650674809248501683449)
      ·
        refine ⟨25618238006106936376262587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34157650674809248501683449 25618238006106936376262587)
        ·
          refine ⟨38427357009160404564393881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25618238006106936376262587 38427357009160404564393881)
          ·
            refine ⟨28820517756870303423295411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38427357009160404564393881 28820517756870303423295411)
            ·
              refine ⟨43230776635305455134943117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28820517756870303423295411 43230776635305455134943117)
              ·
                refine ⟨16211541238239545675603669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43230776635305455134943117 16211541238239545675603669)
                ·
                  refine ⟨379957997771239351771961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16211541238239545675603669 379957997771239351771961)
                  ·
                    rfl

theorem cell23_6659690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 3, 7].length) (baseStart_6659690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6659690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6659690 prefixEnd_6659690 := by exact prefixLift 6659690
  have htrace : WordTrace (prefixWord ++ tailWord_6659690) baseStart_6659690 baseEnd_6659690 := by
    simpa [prefixWord, tailWord_6659690, baseEnd_6659690] using wordTrace_append hprefix tailTrace_6659690
  have hstable : (prefixWord ++ tailWord_6659690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6659690).length < 2 ^ (prefixWord ++ tailWord_6659690).sum := by decide
  have hdescent : baseEnd_6659690 < baseStart_6659690 := by decide
  rcases family_descends (prefixWord ++ tailWord_6659690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6659701 : List Nat := [1, 3, 4, 2, 1, 3, 1, 1, 1, 4, 2]
def baseStart_6659701 : Nat := 118140960795 + 6659701 * 2 ^ 59
def prefixEnd_6659701 : Nat := 4983230072969 + 3 ^ 40 * 6659701 * 2
def baseEnd_6659701 : Nat := 3419627628228353622910099

theorem tailTrace_6659701 : CollatzResearch.WordTrace tailWord_6659701 prefixEnd_6659701 3419627628228353622910099 := by
  unfold tailWord_6659701
  simp only [CollatzResearch.WordTrace]
  refine ⟨242899250446048138223954957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161932833630698758815969971 242899250446048138223954957)
  ·
    refine ⟨91087218917268051833983109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 242899250446048138223954957 91087218917268051833983109)
    ·
      refine ⟨17078853546987759718871833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91087218917268051833983109 17078853546987759718871833)
      ·
        refine ⟨12809140160240819789153875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17078853546987759718871833 12809140160240819789153875)
        ·
          refine ⟨19213710240361229683730813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12809140160240819789153875 19213710240361229683730813)
          ·
            refine ⟨7205141340135461131399055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19213710240361229683730813 7205141340135461131399055)
            ·
              refine ⟨10807712010203191697098583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7205141340135461131399055 10807712010203191697098583)
              ·
                refine ⟨16211568015304787545647875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10807712010203191697098583 16211568015304787545647875)
                ·
                  refine ⟨24317352022957181318471813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16211568015304787545647875 24317352022957181318471813)
                  ·
                    refine ⟨4559503504304471497213465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24317352022957181318471813 4559503504304471497213465)
                    ·
                      refine ⟨3419627628228353622910099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4559503504304471497213465 3419627628228353622910099)
                      ·
                        rfl

theorem cell23_6659701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 1, 1, 1, 4, 2].length) (baseStart_6659701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6659701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6659701 prefixEnd_6659701 := by exact prefixLift 6659701
  have htrace : WordTrace (prefixWord ++ tailWord_6659701) baseStart_6659701 baseEnd_6659701 := by
    simpa [prefixWord, tailWord_6659701, baseEnd_6659701] using wordTrace_append hprefix tailTrace_6659701
  have hstable : (prefixWord ++ tailWord_6659701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6659701).length < 2 ^ (prefixWord ++ tailWord_6659701).sum := by decide
  have hdescent : baseEnd_6659701 < baseStart_6659701 := by decide
  rcases family_descends (prefixWord ++ tailWord_6659701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6659757 : List Nat := [1, 5, 2, 1, 1, 1, 1, 2, 4, 1, 4]
def baseStart_6659757 : Nat := 118140960795 + 6659757 * 2 ^ 59
def prefixEnd_6659757 : Nat := 4983230072969 + 3 ^ 40 * 6659757 * 2
def baseEnd_6659757 : Nat := 3419656383145005403809841

theorem tailTrace_6659757 : CollatzResearch.WordTrace tailWord_6659757 prefixEnd_6659757 3419656383145005403809841 := by
  unfold tailWord_6659757
  simp only [CollatzResearch.WordTrace]
  refine ⟨242901292933845259787993525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161934195289230173191995683 242901292933845259787993525)
  ·
    refine ⟨22771996212547993105124393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 242901292933845259787993525 22771996212547993105124393)
    ·
      refine ⟨17078997159410994828843295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22771996212547993105124393 17078997159410994828843295)
      ·
        refine ⟨25618495739116492243264943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17078997159410994828843295 25618495739116492243264943)
        ·
          refine ⟨38427743608674738364897415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25618495739116492243264943 38427743608674738364897415)
          ·
            refine ⟨57641615413012107547346123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38427743608674738364897415 57641615413012107547346123)
            ·
              refine ⟨86462423119518161321019185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57641615413012107547346123 86462423119518161321019185)
              ·
                refine ⟨64846817339638620990764389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86462423119518161321019185 64846817339638620990764389)
                ·
                  refine ⟨12158778251182241435768323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64846817339638620990764389 12158778251182241435768323)
                  ·
                    refine ⟨18238167376773362153652485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12158778251182241435768323 18238167376773362153652485)
                    ·
                      refine ⟨3419656383145005403809841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18238167376773362153652485 3419656383145005403809841)
                      ·
                        rfl

theorem cell23_6659757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_6659757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6659757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6659757 prefixEnd_6659757 := by exact prefixLift 6659757
  have htrace : WordTrace (prefixWord ++ tailWord_6659757) baseStart_6659757 baseEnd_6659757 := by
    simpa [prefixWord, tailWord_6659757, baseEnd_6659757] using wordTrace_append hprefix tailTrace_6659757
  have hstable : (prefixWord ++ tailWord_6659757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6659757).length < 2 ^ (prefixWord ++ tailWord_6659757).sum := by decide
  have hdescent : baseEnd_6659757 < baseStart_6659757 := by decide
  rcases family_descends (prefixWord ++ tailWord_6659757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6659760 : List Nat := [2, 1, 1, 1, 2, 1, 4, 1, 3, 4, 3]
def baseStart_6659760 : Nat := 118140960795 + 6659760 * 2 ^ 59
def prefixEnd_6659760 : Nat := 4983230072969 + 3 ^ 40 * 6659760 * 2
def baseEnd_6659760 : Nat := 3419657923586968892072327

theorem tailTrace_6659760 : CollatzResearch.WordTrace tailWord_6659760 prefixEnd_6659760 3419657923586968892072327 := by
  unfold tailWord_6659760
  simp only [CollatzResearch.WordTrace]
  refine ⟨121450701176417195650176367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161934268235222927533568489 121450701176417195650176367)
  ·
    refine ⟨182176051764625793475264551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121450701176417195650176367 182176051764625793475264551)
    ·
      refine ⟨273264077646938690212896827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182176051764625793475264551 273264077646938690212896827)
      ·
        refine ⟨409896116470408035319345241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273264077646938690212896827 409896116470408035319345241)
        ·
          refine ⟨307422087352806026489508931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 409896116470408035319345241 307422087352806026489508931)
          ·
            refine ⟨461133131029209039734263397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 307422087352806026489508931 461133131029209039734263397)
            ·
              refine ⟨86462462067976694950174387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 461133131029209039734263397 86462462067976694950174387)
              ·
                refine ⟨129693693101965042425261581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86462462067976694950174387 129693693101965042425261581)
                ·
                  refine ⟨48635134913236890909473093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 129693693101965042425261581 48635134913236890909473093)
                  ·
                    refine ⟨9119087796231917045526205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48635134913236890909473093 9119087796231917045526205)
                    ·
                      refine ⟨3419657923586968892072327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9119087796231917045526205 3419657923586968892072327)
                      ·
                        rfl

theorem cell23_6659760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 3, 4, 3].length) (baseStart_6659760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6659760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6659760 prefixEnd_6659760 := by exact prefixLift 6659760
  have htrace : WordTrace (prefixWord ++ tailWord_6659760) baseStart_6659760 baseEnd_6659760 := by
    simpa [prefixWord, tailWord_6659760, baseEnd_6659760] using wordTrace_append hprefix tailTrace_6659760
  have hstable : (prefixWord ++ tailWord_6659760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6659760).length < 2 ^ (prefixWord ++ tailWord_6659760).sum := by decide
  have hdescent : baseEnd_6659760 < baseStart_6659760 := by decide
  rcases family_descends (prefixWord ++ tailWord_6659760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6659774 : List Nat := [4, 2, 1, 1, 2, 3, 2, 1, 2, 1, 4]
def baseStart_6659774 : Nat := 118140960795 + 6659774 * 2 ^ 59
def prefixEnd_6659774 : Nat := 4983230072969 + 3 ^ 40 * 6659774 * 2
def baseEnd_6659774 : Nat := 3419665112316131837297263

theorem tailTrace_6659774 : CollatzResearch.WordTrace tailWord_6659774 prefixEnd_6659774 3419665112316131837297263 := by
  unfold tailWord_6659774
  simp only [CollatzResearch.WordTrace]
  refine ⟨30362739121847958961420297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 161934608649855781127574917 30362739121847958961420297)
  ·
    refine ⟨22772054341385969221065223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30362739121847958961420297 22772054341385969221065223)
    ·
      refine ⟨34158081512078953831597835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22772054341385969221065223 34158081512078953831597835)
      ·
        refine ⟨51237122268118430747396753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34158081512078953831597835 51237122268118430747396753)
        ·
          refine ⟨38427841701088823060547565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51237122268118430747396753 38427841701088823060547565)
          ·
            refine ⟨14410440637908308647705337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38427841701088823060547565 14410440637908308647705337)
            ·
              refine ⟨10807830478431231485779003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14410440637908308647705337 10807830478431231485779003)
              ·
                refine ⟨16211745717646847228668505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10807830478431231485779003 16211745717646847228668505)
                ·
                  refine ⟨12158809288235135421501379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16211745717646847228668505 12158809288235135421501379)
                  ·
                    refine ⟨18238213932352703132252069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12158809288235135421501379 18238213932352703132252069)
                    ·
                      refine ⟨3419665112316131837297263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18238213932352703132252069 3419665112316131837297263)
                      ·
                        rfl

theorem cell23_6659774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 3, 2, 1, 2, 1, 4].length) (baseStart_6659774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6659774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6659774 prefixEnd_6659774 := by exact prefixLift 6659774
  have htrace : WordTrace (prefixWord ++ tailWord_6659774) baseStart_6659774 baseEnd_6659774 := by
    simpa [prefixWord, tailWord_6659774, baseEnd_6659774] using wordTrace_append hprefix tailTrace_6659774
  have hstable : (prefixWord ++ tailWord_6659774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6659774).length < 2 ^ (prefixWord ++ tailWord_6659774).sum := by decide
  have hdescent : baseEnd_6659774 < baseStart_6659774 := by decide
  rcases family_descends (prefixWord ++ tailWord_6659774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6659784 : List Nat := [2, 1, 3, 1, 2, 2, 2, 5, 1, 4]
def baseStart_6659784 : Nat := 118140960795 + 6659784 * 2 ^ 59
def prefixEnd_6659784 : Nat := 4983230072969 + 3 ^ 40 * 6659784 * 2
def baseEnd_6659784 : Nat := 1139890082374225599390739

theorem tailTrace_6659784 : CollatzResearch.WordTrace tailWord_6659784 prefixEnd_6659784 1139890082374225599390739 := by
  unfold tailWord_6659784
  simp only [CollatzResearch.WordTrace]
  refine ⟨121451138852373721699613203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161934851803164962266150937 121451138852373721699613203)
  ·
    refine ⟨182176708278560582549419805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121451138852373721699613203 182176708278560582549419805)
    ·
      refine ⟨68316265604460218456032427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182176708278560582549419805 68316265604460218456032427)
      ·
        refine ⟨102474398406690327684048641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68316265604460218456032427 102474398406690327684048641)
        ·
          refine ⟨76855798805017745763036481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102474398406690327684048641 76855798805017745763036481)
          ·
            refine ⟨57641849103763309322277361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76855798805017745763036481 57641849103763309322277361)
            ·
              refine ⟨43231386827822481991708021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57641849103763309322277361 43231386827822481991708021)
              ·
                refine ⟨4052942515108357686722627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43231386827822481991708021 4052942515108357686722627)
                ·
                  refine ⟨6079413772662536530083941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4052942515108357686722627 6079413772662536530083941)
                  ·
                    refine ⟨1139890082374225599390739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6079413772662536530083941 1139890082374225599390739)
                    ·
                      rfl

theorem cell23_6659784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 5, 1, 4].length) (baseStart_6659784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6659784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6659784 prefixEnd_6659784 := by exact prefixLift 6659784
  have htrace : WordTrace (prefixWord ++ tailWord_6659784) baseStart_6659784 baseEnd_6659784 := by
    simpa [prefixWord, tailWord_6659784, baseEnd_6659784] using wordTrace_append hprefix tailTrace_6659784
  have hstable : (prefixWord ++ tailWord_6659784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6659784).length < 2 ^ (prefixWord ++ tailWord_6659784).sum := by decide
  have hdescent : baseEnd_6659784 < baseStart_6659784 := by decide
  rcases family_descends (prefixWord ++ tailWord_6659784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6659794 : List Nat := [3, 2, 2, 2, 2, 1, 2, 2, 2, 2, 3]
def baseStart_6659794 : Nat := 118140960795 + 6659794 * 2 ^ 59
def prefixEnd_6659794 : Nat := 4983230072969 + 3 ^ 40 * 6659794 * 2
def baseEnd_6659794 : Nat := 3419675381929221759047171

theorem tailTrace_6659794 : CollatzResearch.WordTrace tailWord_6659794 prefixEnd_6659794 3419675381929221759047171 := by
  unfold tailWord_6659794
  simp only [CollatzResearch.WordTrace]
  refine ⟨60725660608677803776772609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161935094956474143404726957 60725660608677803776772609)
  ·
    refine ⟨45544245456508352832579457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60725660608677803776772609 45544245456508352832579457)
    ·
      refine ⟨34158184092381264624434593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45544245456508352832579457 34158184092381264624434593)
      ·
        refine ⟨25618638069285948468325945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34158184092381264624434593 25618638069285948468325945)
        ·
          refine ⟨19213978551964461351244459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25618638069285948468325945 19213978551964461351244459)
          ·
            refine ⟨28820967827946692026866689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19213978551964461351244459 28820967827946692026866689)
            ·
              refine ⟨21615725870960019020150017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28820967827946692026866689 21615725870960019020150017)
              ·
                refine ⟨16211794403220014265112513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21615725870960019020150017 16211794403220014265112513)
                ·
                  refine ⟨12158845802415010698834385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16211794403220014265112513 12158845802415010698834385)
                  ·
                    refine ⟨9119134351811258024125789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12158845802415010698834385 9119134351811258024125789)
                    ·
                      refine ⟨3419675381929221759047171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9119134351811258024125789 3419675381929221759047171)
                      ·
                        rfl

theorem cell23_6659794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 2, 2, 2, 3].length) (baseStart_6659794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6659794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6659794 prefixEnd_6659794 := by exact prefixLift 6659794
  have htrace : WordTrace (prefixWord ++ tailWord_6659794) baseStart_6659794 baseEnd_6659794 := by
    simpa [prefixWord, tailWord_6659794, baseEnd_6659794] using wordTrace_append hprefix tailTrace_6659794
  have hstable : (prefixWord ++ tailWord_6659794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6659794).length < 2 ^ (prefixWord ++ tailWord_6659794).sum := by decide
  have hdescent : baseEnd_6659794 < baseStart_6659794 := by decide
  rcases family_descends (prefixWord ++ tailWord_6659794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6659800 : List Nat := [2, 1, 2, 2, 3, 1, 2, 1, 1, 2, 6]
def baseStart_6659800 : Nat := 118140960795 + 6659800 * 2 ^ 59
def prefixEnd_6659800 : Nat := 4983230072969 + 3 ^ 40 * 6659800 * 2
def baseEnd_6659800 : Nat := 3419678462813148735572143

theorem tailTrace_6659800 : CollatzResearch.WordTrace tailWord_6659800 prefixEnd_6659800 3419678462813148735572143 := by
  unfold tailWord_6659800
  simp only [CollatzResearch.WordTrace]
  refine ⟨121451430636344739065904427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161935240848459652087872569 121451430636344739065904427)
  ·
    refine ⟨182177145954517108598856641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121451430636344739065904427 182177145954517108598856641)
    ·
      refine ⟨136632859465887831449142481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182177145954517108598856641 136632859465887831449142481)
      ·
        refine ⟨102474644599415873586856861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136632859465887831449142481 102474644599415873586856861)
        ·
          refine ⟨38427991724780952595071323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102474644599415873586856861 38427991724780952595071323)
          ·
            refine ⟨57641987587171428892606985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38427991724780952595071323 57641987587171428892606985)
            ·
              refine ⟨43231490690378571669455239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57641987587171428892606985 43231490690378571669455239)
              ·
                refine ⟨64847236035567857504182859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43231490690378571669455239 64847236035567857504182859)
                ·
                  refine ⟨97270854053351786256274289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64847236035567857504182859 97270854053351786256274289)
                  ·
                    refine ⟨72953140540013839692205717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 97270854053351786256274289 72953140540013839692205717)
                    ·
                      refine ⟨3419678462813148735572143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72953140540013839692205717 3419678462813148735572143)
                      ·
                        rfl

theorem cell23_6659800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 1, 1, 2, 6].length) (baseStart_6659800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6659800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6659800 prefixEnd_6659800 := by exact prefixLift 6659800
  have htrace : WordTrace (prefixWord ++ tailWord_6659800) baseStart_6659800 baseEnd_6659800 := by
    simpa [prefixWord, tailWord_6659800, baseEnd_6659800] using wordTrace_append hprefix tailTrace_6659800
  have hstable : (prefixWord ++ tailWord_6659800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6659800).length < 2 ^ (prefixWord ++ tailWord_6659800).sum := by decide
  have hdescent : baseEnd_6659800 < baseStart_6659800 := by decide
  rcases family_descends (prefixWord ++ tailWord_6659800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6659801 : List Nat := [1, 2, 1, 2, 3, 3, 4, 2, 1, 4]
def baseStart_6659801 : Nat := 118140960795 + 6659801 * 2 ^ 59
def prefixEnd_6659801 : Nat := 4983230072969 + 3 ^ 40 * 6659801 * 2
def baseEnd_6659801 : Nat := 1139892992097934410553213

theorem tailTrace_6659801 : CollatzResearch.WordTrace tailWord_6659801 prefixEnd_6659801 1139892992097934410553213 := by
  unfold tailWord_6659801
  simp only [CollatzResearch.WordTrace]
  refine ⟨242902897745685855302595257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161935265163790570201730171 242902897745685855302595257)
  ·
    refine ⟨182177173309264391476946443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242902897745685855302595257 182177173309264391476946443)
    ·
      refine ⟨273265759963896587215419665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182177173309264391476946443 273265759963896587215419665)
      ·
        refine ⟨204949319972922440411564749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 273265759963896587215419665 204949319972922440411564749)
        ·
          refine ⟨76855994989845915154336781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 204949319972922440411564749 76855994989845915154336781)
          ·
            refine ⟨28820998121192218182876293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76855994989845915154336781 28820998121192218182876293)
            ·
              refine ⟨5403937147723540909289305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28820998121192218182876293 5403937147723540909289305)
              ·
                refine ⟨4052952860792655681966979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5403937147723540909289305 4052952860792655681966979)
                ·
                  refine ⟨6079429291188983522950469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4052952860792655681966979 6079429291188983522950469)
                  ·
                    refine ⟨1139892992097934410553213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6079429291188983522950469 1139892992097934410553213)
                    ·
                      rfl

theorem cell23_6659801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 4, 2, 1, 4].length) (baseStart_6659801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6659801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6659801 prefixEnd_6659801 := by exact prefixLift 6659801
  have htrace : WordTrace (prefixWord ++ tailWord_6659801) baseStart_6659801 baseEnd_6659801 := by
    simpa [prefixWord, tailWord_6659801, baseEnd_6659801] using wordTrace_append hprefix tailTrace_6659801
  have hstable : (prefixWord ++ tailWord_6659801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6659801).length < 2 ^ (prefixWord ++ tailWord_6659801).sum := by decide
  have hdescent : baseEnd_6659801 < baseStart_6659801 := by decide
  rcases family_descends (prefixWord ++ tailWord_6659801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6659817 : List Nat := [1, 2, 1, 1, 1, 2, 3, 4, 1, 5, 2]
def baseStart_6659817 : Nat := 118140960795 + 6659817 * 2 ^ 59
def prefixEnd_6659817 : Nat := 4983230072969 + 3 ^ 40 * 6659817 * 2
def baseEnd_6659817 : Nat := 3419687191984275169059565

theorem tailTrace_6659817 : CollatzResearch.WordTrace tailWord_6659817 prefixEnd_6659817 3419687191984275169059565 := by
  unfold tailWord_6659817
  simp only [CollatzResearch.WordTrace]
  refine ⟨242903481313627890035177705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161935654209085260023451803 242903481313627890035177705)
  ·
    refine ⟨182177610985220917526383279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242903481313627890035177705 182177610985220917526383279)
    ·
      refine ⟨273266416477831376289574919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182177610985220917526383279 273266416477831376289574919)
      ·
        refine ⟨409899624716747064434362379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273266416477831376289574919 409899624716747064434362379)
        ·
          refine ⟨614849437075120596651543569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 409899624716747064434362379 614849437075120596651543569)
          ·
            refine ⟨461137077806340447488657677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 614849437075120596651543569 461137077806340447488657677)
            ·
              refine ⟨172926404177377667808246629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 461137077806340447488657677 172926404177377667808246629)
              ·
                refine ⟨32423700783258312714046243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 172926404177377667808246629 32423700783258312714046243)
                ·
                  refine ⟨48635551174887469071069365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32423700783258312714046243 48635551174887469071069365)
                  ·
                    refine ⟨4559582922645700225412753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48635551174887469071069365 4559582922645700225412753)
                    ·
                      refine ⟨3419687191984275169059565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4559582922645700225412753 3419687191984275169059565)
                      ·
                        rfl

theorem cell23_6659817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 4, 1, 5, 2].length) (baseStart_6659817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6659817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6659817 prefixEnd_6659817 := by exact prefixLift 6659817
  have htrace : WordTrace (prefixWord ++ tailWord_6659817) baseStart_6659817 baseEnd_6659817 := by
    simpa [prefixWord, tailWord_6659817, baseEnd_6659817] using wordTrace_append hprefix tailTrace_6659817
  have hstable : (prefixWord ++ tailWord_6659817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6659817).length < 2 ^ (prefixWord ++ tailWord_6659817).sum := by decide
  have hdescent : baseEnd_6659817 < baseStart_6659817 := by decide
  rcases family_descends (prefixWord ++ tailWord_6659817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6659828 : List Nat := [2, 6, 1, 1, 1, 1, 3, 1, 2, 2, 3]
def baseStart_6659828 : Nat := 118140960795 + 6659828 * 2 ^ 59
def prefixEnd_6659828 : Nat := 4983230072969 + 3 ^ 40 * 6659828 * 2
def baseEnd_6659828 : Nat := 3419692840271474626022015

theorem tailTrace_6659828 : CollatzResearch.WordTrace tailWord_6659828 prefixEnd_6659828 3419692840271474626022015 := by
  unfold tailWord_6659828
  simp only [CollatzResearch.WordTrace]
  refine ⟨121451941258294019456914069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161935921677725359275885425 121451941258294019456914069)
  ·
    refine ⟨5693059746482532162042847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 121451941258294019456914069 5693059746482532162042847)
    ·
      refine ⟨8539589619723798243064271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5693059746482532162042847 8539589619723798243064271)
      ·
        refine ⟨12809384429585697364596407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8539589619723798243064271 12809384429585697364596407)
        ·
          refine ⟨19214076644378546046894611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12809384429585697364596407 19214076644378546046894611)
          ·
            refine ⟨28821114966567819070341917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19214076644378546046894611 28821114966567819070341917)
            ·
              refine ⟨10807918112462932151378219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28821114966567819070341917 10807918112462932151378219)
              ·
                refine ⟨16211877168694398227067329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10807918112462932151378219 16211877168694398227067329)
                ·
                  refine ⟨12158907876520798670300497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16211877168694398227067329 12158907876520798670300497)
                  ·
                    refine ⟨9119180907390599002725373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12158907876520798670300497 9119180907390599002725373)
                    ·
                      refine ⟨3419692840271474626022015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9119180907390599002725373 3419692840271474626022015)
                      ·
                        rfl

theorem cell23_6659828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_6659828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6659828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6659828 prefixEnd_6659828 := by exact prefixLift 6659828
  have htrace : WordTrace (prefixWord ++ tailWord_6659828) baseStart_6659828 baseEnd_6659828 := by
    simpa [prefixWord, tailWord_6659828, baseEnd_6659828] using wordTrace_append hprefix tailTrace_6659828
  have hstable : (prefixWord ++ tailWord_6659828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6659828).length < 2 ^ (prefixWord ++ tailWord_6659828).sum := by decide
  have hdescent : baseEnd_6659828 < baseStart_6659828 := by decide
  rcases family_descends (prefixWord ++ tailWord_6659828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6659841 : List Nat := [1, 2, 4, 1, 1, 1, 3, 5, 1, 1, 3]
def baseStart_6659841 : Nat := 118140960795 + 6659841 * 2 ^ 59
def prefixEnd_6659841 : Nat := 4983230072969 + 3 ^ 40 * 6659841 * 2
def baseEnd_6659841 : Nat := 3419699515519983075159455

theorem tailTrace_6659841 : CollatzResearch.WordTrace tailWord_6659841 prefixEnd_6659841 3419699515519983075159455 := by
  unfold tailWord_6659841
  simp only [CollatzResearch.WordTrace]
  refine ⟨242904356665540942134051377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161936237777027294756034251 242904356665540942134051377)
  ·
    refine ⟨182178267499155706600538533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242904356665540942134051377 182178267499155706600538533)
    ·
      refine ⟨34158425156091694987600975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 182178267499155706600538533 34158425156091694987600975)
      ·
        refine ⟨51237637734137542481401463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34158425156091694987600975 51237637734137542481401463)
        ·
          refine ⟨76856456601206313722102195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51237637734137542481401463 76856456601206313722102195)
          ·
            refine ⟨115284684901809470583153293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76856456601206313722102195 115284684901809470583153293)
            ·
              refine ⟨43231756838178551468682485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 115284684901809470583153293 43231756838178551468682485)
              ·
                refine ⟨4052977203579239200188983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43231756838178551468682485 4052977203579239200188983)
                ·
                  refine ⟨6079465805368858800283475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4052977203579239200188983 6079465805368858800283475)
                  ·
                    refine ⟨9119198708053288200425213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6079465805368858800283475 9119198708053288200425213)
                    ·
                      refine ⟨3419699515519983075159455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9119198708053288200425213 3419699515519983075159455)
                      ·
                        rfl

theorem cell23_6659841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 5, 1, 1, 3].length) (baseStart_6659841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6659841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6659841 prefixEnd_6659841 := by exact prefixLift 6659841
  have htrace : WordTrace (prefixWord ++ tailWord_6659841) baseStart_6659841 baseEnd_6659841 := by
    simpa [prefixWord, tailWord_6659841, baseEnd_6659841] using wordTrace_append hprefix tailTrace_6659841
  have hstable : (prefixWord ++ tailWord_6659841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6659841).length < 2 ^ (prefixWord ++ tailWord_6659841).sum := by decide
  have hdescent : baseEnd_6659841 < baseStart_6659841 := by decide
  rcases family_descends (prefixWord ++ tailWord_6659841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6659844 : List Nat := [2, 3, 2, 2, 1, 3, 1, 3, 1, 5]
def baseStart_6659844 : Nat := 118140960795 + 6659844 * 2 ^ 59
def prefixEnd_6659844 : Nat := 4983230072969 + 3 ^ 40 * 6659844 * 2
def baseEnd_6659844 : Nat := 1139900351987315521140647

theorem tailTrace_6659844 : CollatzResearch.WordTrace tailWord_6659844 prefixEnd_6659844 1139900351987315521140647 := by
  unfold tailWord_6659844
  simp only [CollatzResearch.WordTrace]
  refine ⟨121452233042265036823205293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161936310723020049097607057 121452233042265036823205293)
  ·
    refine ⟨45544587390849388808701985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121452233042265036823205293 45544587390849388808701985)
    ·
      refine ⟨34158440543137041606526489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45544587390849388808701985 34158440543137041606526489)
      ·
        refine ⟨25618830407352781204894867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34158440543137041606526489 25618830407352781204894867)
        ·
          refine ⟨38428245611029171807342301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25618830407352781204894867 38428245611029171807342301)
          ·
            refine ⟨14410592104135939427753363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38428245611029171807342301 14410592104135939427753363)
            ·
              refine ⟨21615888156203909141630045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14410592104135939427753363 21615888156203909141630045)
              ·
                refine ⟨8105958058576465928111267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21615888156203909141630045 8105958058576465928111267)
                ·
                  refine ⟨12158937087864698892166901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8105958058576465928111267 12158937087864698892166901)
                  ·
                    refine ⟨1139900351987315521140647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12158937087864698892166901 1139900351987315521140647)
                    ·
                      rfl

theorem cell23_6659844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 3, 1, 5].length) (baseStart_6659844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6659844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6659844 prefixEnd_6659844 := by exact prefixLift 6659844
  have htrace : WordTrace (prefixWord ++ tailWord_6659844) baseStart_6659844 baseEnd_6659844 := by
    simpa [prefixWord, tailWord_6659844, baseEnd_6659844] using wordTrace_append hprefix tailTrace_6659844
  have hstable : (prefixWord ++ tailWord_6659844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6659844).length < 2 ^ (prefixWord ++ tailWord_6659844).sum := by decide
  have hdescent : baseEnd_6659844 < baseStart_6659844 := by decide
  rcases family_descends (prefixWord ++ tailWord_6659844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6659858 : List Nat := [3, 2, 4, 1, 1, 2, 2, 1, 3, 1, 3]
def baseStart_6659858 : Nat := 118140960795 + 6659858 * 2 ^ 59
def prefixEnd_6659858 : Nat := 4983230072969 + 3 ^ 40 * 6659858 * 2
def baseEnd_6659858 : Nat := 3419708244691109508646877

theorem tailTrace_6659858 : CollatzResearch.WordTrace tailWord_6659858 prefixEnd_6659858 3419708244691109508646877 := by
  unfold tailWord_6659858
  simp only [CollatzResearch.WordTrace]
  refine ⟨60726244176619838509355057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161936651137652902691613485 60726244176619838509355057)
  ·
    refine ⟨45544683132464878882016293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60726244176619838509355057 45544683132464878882016293)
    ·
      refine ⟨8539628087337164790378055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45544683132464878882016293 8539628087337164790378055)
      ·
        refine ⟨12809442131005747185567083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8539628087337164790378055 12809442131005747185567083)
        ·
          refine ⟨19214163196508620778350625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12809442131005747185567083 19214163196508620778350625)
          ·
            refine ⟨14410622397381465583762969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19214163196508620778350625 14410622397381465583762969)
            ·
              refine ⟨10807966798036099187822227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14410622397381465583762969 10807966798036099187822227)
              ·
                refine ⟨16211950197054148781733341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10807966798036099187822227 16211950197054148781733341)
                ·
                  refine ⟨6079481323895305793150003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16211950197054148781733341 6079481323895305793150003)
                  ·
                    refine ⟨9119221985842958689725005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6079481323895305793150003 9119221985842958689725005)
                    ·
                      refine ⟨3419708244691109508646877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9119221985842958689725005 3419708244691109508646877)
                      ·
                        rfl

theorem cell23_6659858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_6659858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6659858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6659858 prefixEnd_6659858 := by exact prefixLift 6659858
  have htrace : WordTrace (prefixWord ++ tailWord_6659858) baseStart_6659858 baseEnd_6659858 := by
    simpa [prefixWord, tailWord_6659858, baseEnd_6659858] using wordTrace_append hprefix tailTrace_6659858
  have hstable : (prefixWord ++ tailWord_6659858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6659858).length < 2 ^ (prefixWord ++ tailWord_6659858).sum := by decide
  have hdescent : baseEnd_6659858 < baseStart_6659858 := by decide
  rcases family_descends (prefixWord ++ tailWord_6659858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6659877 : List Nat := [1, 3, 1, 2, 3, 3, 1, 1, 1, 1, 6]
def baseStart_6659877 : Nat := 118140960795 + 6659877 * 2 ^ 59
def prefixEnd_6659877 : Nat := 4983230072969 + 3 ^ 40 * 6659877 * 2
def baseEnd_6659877 : Nat := 3419718000823544934309289

theorem tailTrace_6659877 : CollatzResearch.WordTrace tailWord_6659877 prefixEnd_6659877 3419718000823544934309289 := by
  unfold tailWord_6659877
  simp only [CollatzResearch.WordTrace]
  refine ⟨242905669693410520282361885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161937113128940346854907923 242905669693410520282361885)
  ·
    refine ⟨91089626135028945105885707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 242905669693410520282361885 91089626135028945105885707)
    ·
      refine ⟨136634439202543417658828561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91089626135028945105885707 136634439202543417658828561)
      ·
        refine ⟨102475829401907563244121421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136634439202543417658828561 102475829401907563244121421)
        ·
          refine ⟨38428436025715336216545533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102475829401907563244121421 38428436025715336216545533)
          ·
            refine ⟨14410663509643251081204575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38428436025715336216545533 14410663509643251081204575)
            ·
              refine ⟨21615995264464876621806863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14410663509643251081204575 21615995264464876621806863)
              ·
                refine ⟨32423992896697314932710295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21615995264464876621806863 32423992896697314932710295)
                ·
                  refine ⟨48635989345045972399065443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32423992896697314932710295 48635989345045972399065443)
                  ·
                    refine ⟨72953984017568958598598165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48635989345045972399065443 72953984017568958598598165)
                    ·
                      refine ⟨3419718000823544934309289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72953984017568958598598165 3419718000823544934309289)
                      ·
                        rfl

theorem cell23_6659877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 1, 1, 1, 6].length) (baseStart_6659877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6659877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6659877 prefixEnd_6659877 := by exact prefixLift 6659877
  have htrace : WordTrace (prefixWord ++ tailWord_6659877) baseStart_6659877 baseEnd_6659877 := by
    simpa [prefixWord, tailWord_6659877, baseEnd_6659877] using wordTrace_append hprefix tailTrace_6659877
  have hstable : (prefixWord ++ tailWord_6659877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6659877).length < 2 ^ (prefixWord ++ tailWord_6659877).sum := by decide
  have hdescent : baseEnd_6659877 < baseStart_6659877 := by decide
  rcases family_descends (prefixWord ++ tailWord_6659877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6659884 : List Nat := [2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 3]
def baseStart_6659884 : Nat := 118140960795 + 6659884 * 2 ^ 59
def prefixEnd_6659884 : Nat := 4983230072969 + 3 ^ 40 * 6659884 * 2
def baseEnd_6659884 : Nat := 3419721595188126406921757

theorem tailTrace_6659884 : CollatzResearch.WordTrace tailWord_6659884 prefixEnd_6659884 3419721595188126406921757 := by
  unfold tailWord_6659884
  simp only [CollatzResearch.WordTrace]
  refine ⟨121452962502192580238933353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161937283336256773651911137 121452962502192580238933353)
  ·
    refine ⟨91089721876644435179200015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121452962502192580238933353 91089721876644435179200015)
    ·
      refine ⟨136634582814966652768800023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91089721876644435179200015 136634582814966652768800023)
      ·
        refine ⟨204951874222449979153200035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136634582814966652768800023 204951874222449979153200035)
        ·
          refine ⟨307427811333674968729800053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204951874222449979153200035 307427811333674968729800053)
          ·
            refine ⟨28821357312532028318418755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 307427811333674968729800053 28821357312532028318418755)
            ·
              refine ⟨43232035968798042477628133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28821357312532028318418755 43232035968798042477628133)
              ·
                refine ⟨8106006744149632964555275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43232035968798042477628133 8106006744149632964555275)
                ·
                  refine ⟨12159010116224449446832913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8106006744149632964555275 12159010116224449446832913)
                  ·
                    refine ⟨9119257587168337085124685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12159010116224449446832913 9119257587168337085124685)
                    ·
                      refine ⟨3419721595188126406921757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9119257587168337085124685 3419721595188126406921757)
                      ·
                        rfl

theorem cell23_6659884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 3].length) (baseStart_6659884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6659884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6659884 prefixEnd_6659884 := by exact prefixLift 6659884
  have htrace : WordTrace (prefixWord ++ tailWord_6659884) baseStart_6659884 baseEnd_6659884 := by
    simpa [prefixWord, tailWord_6659884, baseEnd_6659884] using wordTrace_append hprefix tailTrace_6659884
  have hstable : (prefixWord ++ tailWord_6659884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6659884).length < 2 ^ (prefixWord ++ tailWord_6659884).sum := by decide
  have hdescent : baseEnd_6659884 < baseStart_6659884 := by decide
  rcases family_descends (prefixWord ++ tailWord_6659884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6659901 : List Nat := [1, 4, 1, 4, 1, 1, 2, 3, 1, 2, 3]
def baseStart_6659901 : Nat := 118140960795 + 6659901 * 2 ^ 59
def prefixEnd_6659901 : Nat := 4983230072969 + 3 ^ 40 * 6659901 * 2
def baseEnd_6659901 : Nat := 3419730324359252840409179

theorem tailTrace_6659901 : CollatzResearch.WordTrace tailWord_6659901 prefixEnd_6659901 3419730324359252840409179 := by
  unfold tailWord_6659901
  simp only [CollatzResearch.WordTrace]
  refine ⟨242906545045323572381235557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161937696696882381587490371 242906545045323572381235557)
  ·
    refine ⟨45544977195998169821481667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 242906545045323572381235557 45544977195998169821481667)
    ·
      refine ⟨68317465793997254732222501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45544977195998169821481667 68317465793997254732222501)
      ·
        refine ⟨12809524836374485262291719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68317465793997254732222501 12809524836374485262291719)
        ·
          refine ⟨19214287254561727893437579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12809524836374485262291719 19214287254561727893437579)
          ·
            refine ⟨28821430881842591840156369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19214287254561727893437579 28821430881842591840156369)
            ·
              refine ⟨21616073161381943880117277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28821430881842591840156369 21616073161381943880117277)
              ·
                refine ⟨8106027435518228955043979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21616073161381943880117277 8106027435518228955043979)
                ·
                  refine ⟨12159041153277343432565969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8106027435518228955043979 12159041153277343432565969)
                  ·
                    refine ⟨9119280864958007574424477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12159041153277343432565969 9119280864958007574424477)
                    ·
                      refine ⟨3419730324359252840409179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9119280864958007574424477 3419730324359252840409179)
                      ·
                        rfl

theorem cell23_6659901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_6659901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6659901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6659901 prefixEnd_6659901 := by exact prefixLift 6659901
  have htrace : WordTrace (prefixWord ++ tailWord_6659901) baseStart_6659901 baseEnd_6659901 := by
    simpa [prefixWord, tailWord_6659901, baseEnd_6659901] using wordTrace_append hprefix tailTrace_6659901
  have hstable : (prefixWord ++ tailWord_6659901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6659901).length < 2 ^ (prefixWord ++ tailWord_6659901).sum := by decide
  have hdescent : baseEnd_6659901 < baseStart_6659901 := by decide
  rcases family_descends (prefixWord ++ tailWord_6659901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6659914 : List Nat := [3, 1, 2, 1, 1, 1, 3, 3, 4, 1, 3]
def baseStart_6659914 : Nat := 118140960795 + 6659914 * 2 ^ 59
def prefixEnd_6659914 : Nat := 4983230072969 + 3 ^ 40 * 6659914 * 2
def baseEnd_6659914 : Nat := 3419736999607761289546619

theorem tailTrace_6659914 : CollatzResearch.WordTrace tailWord_6659914 prefixEnd_6659914 3419736999607761289546619 := by
  unfold tailWord_6659914
  simp only [CollatzResearch.WordTrace]
  refine ⟨60726754798569118900364699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161938012796184317067639197 60726754798569118900364699)
  ·
    refine ⟨91090132197853678350547049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60726754798569118900364699 91090132197853678350547049)
    ·
      refine ⟨68317599148390258762910287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91090132197853678350547049 68317599148390258762910287)
      ·
        refine ⟨102476398722585388144365431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68317599148390258762910287 102476398722585388144365431)
        ·
          refine ⟨153714598083878082216548147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102476398722585388144365431 153714598083878082216548147)
          ·
            refine ⟨230571897125817123324822221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153714598083878082216548147 230571897125817123324822221)
            ·
              refine ⟨86464461422181421246808333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 230571897125817123324822221 86464461422181421246808333)
              ·
                refine ⟨32424173033318032967553125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86464461422181421246808333 32424173033318032967553125)
                ·
                  refine ⟨6079532443747131181416211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32424173033318032967553125 6079532443747131181416211)
                  ·
                    refine ⟨9119298665620696772124317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6079532443747131181416211 9119298665620696772124317)
                    ·
                      refine ⟨3419736999607761289546619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9119298665620696772124317 3419736999607761289546619)
                      ·
                        rfl

theorem cell23_6659914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 3, 4, 1, 3].length) (baseStart_6659914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6659914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6659914 prefixEnd_6659914 := by exact prefixLift 6659914
  have htrace : WordTrace (prefixWord ++ tailWord_6659914) baseStart_6659914 baseEnd_6659914 := by
    simpa [prefixWord, tailWord_6659914, baseEnd_6659914] using wordTrace_append hprefix tailTrace_6659914
  have hstable : (prefixWord ++ tailWord_6659914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6659914).length < 2 ^ (prefixWord ++ tailWord_6659914).sum := by decide
  have hdescent : baseEnd_6659914 < baseStart_6659914 := by decide
  rcases family_descends (prefixWord ++ tailWord_6659914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6659967 : List Nat := [1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 4]
def baseStart_6659967 : Nat := 118140960795 + 6659967 * 2 ^ 59
def prefixEnd_6659967 : Nat := 4983230072969 + 3 ^ 40 * 6659967 * 2
def baseEnd_6659967 : Nat := 3419764214082449582183875

theorem tailTrace_6659967 : CollatzResearch.WordTrace tailWord_6659967 prefixEnd_6659967 3419764214082449582183875 := by
  unfold tailWord_6659967
  simp only [CollatzResearch.WordTrace]
  refine ⟨242908952263084465653138155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161939301508722977102092103 242908952263084465653138155)
  ·
    refine ⟨364363428394626698479707233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242908952263084465653138155 364363428394626698479707233)
    ·
      refine ⟨273272571295970023859780425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 364363428394626698479707233 273272571295970023859780425)
      ·
        refine ⟨204954428471977517894835319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 273272571295970023859780425 204954428471977517894835319)
        ·
          refine ⟨307431642707966276842252979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204954428471977517894835319 307431642707966276842252979)
          ·
            refine ⟨461147464061949415263379469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 307431642707966276842252979 461147464061949415263379469)
            ·
              refine ⟨172930299023231030723767301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 461147464061949415263379469 172930299023231030723767301)
              ·
                refine ⟨32424431066855818260706369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 172930299023231030723767301 32424431066855818260706369)
                ·
                  refine ⟨24318323300141863695529777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32424431066855818260706369 24318323300141863695529777)
                  ·
                    refine ⟨18238742475106397771647333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24318323300141863695529777 18238742475106397771647333)
                    ·
                      refine ⟨3419764214082449582183875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18238742475106397771647333 3419764214082449582183875)
                      ·
                        rfl

theorem cell23_6659967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 4].length) (baseStart_6659967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6659967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6659967 prefixEnd_6659967 := by exact prefixLift 6659967
  have htrace : WordTrace (prefixWord ++ tailWord_6659967) baseStart_6659967 baseEnd_6659967 := by
    simpa [prefixWord, tailWord_6659967, baseEnd_6659967] using wordTrace_append hprefix tailTrace_6659967
  have hstable : (prefixWord ++ tailWord_6659967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6659967).length < 2 ^ (prefixWord ++ tailWord_6659967).sum := by decide
  have hdescent : baseEnd_6659967 < baseStart_6659967 := by decide
  rcases family_descends (prefixWord ++ tailWord_6659967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6659977 : List Nat := [1, 2, 1, 1, 5, 1, 2, 3, 7]
def baseStart_6659977 : Nat := 118140960795 + 6659977 * 2 ^ 59
def prefixEnd_6659977 : Nat := 4983230072969 + 3 ^ 40 * 6659977 * 2
def baseEnd_6659977 : Nat := 379974372098777171450981

theorem tailTrace_6659977 : CollatzResearch.WordTrace tailWord_6659977 prefixEnd_6659977 379974372098777171450981 := by
  unfold tailWord_6659977
  simp only [CollatzResearch.WordTrace]
  refine ⟨242909316993048237361002185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161939544662032158240668123 242909316993048237361002185)
  ·
    refine ⟨182181987744786178020751639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242909316993048237361002185 182181987744786178020751639)
    ·
      refine ⟨273272981617179267031127459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182181987744786178020751639 273272981617179267031127459)
      ·
        refine ⟨409909472425768900546691189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273272981617179267031127459 409909472425768900546691189)
        ·
          refine ⟨38429013039915834426252299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 409909472425768900546691189 38429013039915834426252299)
          ·
            refine ⟨57643519559873751639378449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38429013039915834426252299 57643519559873751639378449)
            ·
              refine ⟨43232639669905313729533837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57643519559873751639378449 43232639669905313729533837)
              ·
                refine ⟨16212239876214492648575189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43232639669905313729533837 16212239876214492648575189)
                ·
                  refine ⟨379974372098777171450981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16212239876214492648575189 379974372098777171450981)
                  ·
                    rfl

theorem cell23_6659977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 3, 7].length) (baseStart_6659977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6659977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6659977 prefixEnd_6659977 := by exact prefixLift 6659977
  have htrace : WordTrace (prefixWord ++ tailWord_6659977) baseStart_6659977 baseEnd_6659977 := by
    simpa [prefixWord, tailWord_6659977, baseEnd_6659977] using wordTrace_append hprefix tailTrace_6659977
  have hstable : (prefixWord ++ tailWord_6659977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6659977).length < 2 ^ (prefixWord ++ tailWord_6659977).sum := by decide
  have hdescent : baseEnd_6659977 < baseStart_6659977 := by decide
  rcases family_descends (prefixWord ++ tailWord_6659977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6659988 : List Nat := [2, 4, 2, 1, 1, 3, 2, 1, 1, 4, 2]
def baseStart_6659988 : Nat := 118140960795 + 6659988 * 2 ^ 59
def prefixEnd_6659988 : Nat := 4983230072969 + 3 ^ 40 * 6659988 * 2
def baseEnd_6659988 : Nat := 3419774997176194000021279

theorem tailTrace_6659988 : CollatzResearch.WordTrace tailWord_6659988 prefixEnd_6659988 3419774997176194000021279 := by
  unfold tailWord_6659988
  simp only [CollatzResearch.WordTrace]
  refine ⟨121454859098004193119826309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161939812130672257493101745 121454859098004193119826309)
  ·
    refine ⟨22772786080875786209967433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 121454859098004193119826309 22772786080875786209967433)
    ·
      refine ⟨17079589560656839657475575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22772786080875786209967433 17079589560656839657475575)
      ·
        refine ⟨25619384340985259486213363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17079589560656839657475575 25619384340985259486213363)
        ·
          refine ⟨38429076511477889229320045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25619384340985259486213363 38429076511477889229320045)
          ·
            refine ⟨14410903691804208460995017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38429076511477889229320045 14410903691804208460995017)
            ·
              refine ⟨10808177768853156345746263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14410903691804208460995017 10808177768853156345746263)
              ·
                refine ⟨16212266653279734518619395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10808177768853156345746263 16212266653279734518619395)
                ·
                  refine ⟨24318399979919601777929093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16212266653279734518619395 24318399979919601777929093)
                  ·
                    refine ⟨4559699996234925333361705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24318399979919601777929093 4559699996234925333361705)
                    ·
                      refine ⟨3419774997176194000021279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4559699996234925333361705 3419774997176194000021279)
                      ·
                        rfl

theorem cell23_6659988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 2, 1, 1, 4, 2].length) (baseStart_6659988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6659988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6659988 prefixEnd_6659988 := by exact prefixLift 6659988
  have htrace : WordTrace (prefixWord ++ tailWord_6659988) baseStart_6659988 baseEnd_6659988 := by
    simpa [prefixWord, tailWord_6659988, baseEnd_6659988] using wordTrace_append hprefix tailTrace_6659988
  have hstable : (prefixWord ++ tailWord_6659988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6659988).length < 2 ^ (prefixWord ++ tailWord_6659988).sum := by decide
  have hdescent : baseEnd_6659988 < baseStart_6659988 := by decide
  rcases family_descends (prefixWord ++ tailWord_6659988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6659994 : List Nat := [3, 1, 1, 4, 2, 2, 1, 2, 7]
def baseStart_6659994 : Nat := 118140960795 + 6659994 * 2 ^ 59
def prefixEnd_6659994 : Nat := 4983230072969 + 3 ^ 40 * 6659994 * 2
def baseEnd_6659994 : Nat := 379975342006680108505139

theorem tailTrace_6659994 : CollatzResearch.WordTrace tailWord_6659994 prefixEnd_6659994 379975342006680108505139 := by
  unfold tailWord_6659994
  simp only [CollatzResearch.WordTrace]
  refine ⟨60727484258496662316092759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161939958022657766176247357 60727484258496662316092759)
  ·
    refine ⟨91091226387744993474139139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60727484258496662316092759 91091226387744993474139139)
    ·
      refine ⟨136636839581617490211208709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91091226387744993474139139 136636839581617490211208709)
      ·
        refine ⟨25619407421553279414601633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 136636839581617490211208709 25619407421553279414601633)
        ·
          refine ⟨19214555566164959560951225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25619407421553279414601633 19214555566164959560951225)
          ·
            refine ⟨14410916674623719670713419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19214555566164959560951225 14410916674623719670713419)
            ·
              refine ⟨21616375011935579506070129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14410916674623719670713419 21616375011935579506070129)
              ·
                refine ⟨16212281258951684629552597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21616375011935579506070129 16212281258951684629552597)
                ·
                  refine ⟨379975342006680108505139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16212281258951684629552597 379975342006680108505139)
                  ·
                    rfl

theorem cell23_6659994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 2, 7].length) (baseStart_6659994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6659994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6659994 prefixEnd_6659994 := by exact prefixLift 6659994
  have htrace : WordTrace (prefixWord ++ tailWord_6659994) baseStart_6659994 baseEnd_6659994 := by
    simpa [prefixWord, tailWord_6659994, baseEnd_6659994] using wordTrace_append hprefix tailTrace_6659994
  have hstable : (prefixWord ++ tailWord_6659994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6659994).length < 2 ^ (prefixWord ++ tailWord_6659994).sum := by decide
  have hdescent : baseEnd_6659994 < baseStart_6659994 := by decide
  rcases family_descends (prefixWord ++ tailWord_6659994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6660027 : List Nat := [1, 1, 1, 1, 1, 2, 2, 4, 3, 3, 4]
def baseStart_6660027 : Nat := 118140960795 + 6660027 * 2 ^ 59
def prefixEnd_6660027 : Nat := 4983230072969 + 3 ^ 40 * 6660027 * 2
def baseEnd_6660027 : Nat := 3419795022921719347433599

theorem tailTrace_6660027 : CollatzResearch.WordTrace tailWord_6660027 prefixEnd_6660027 3419795022921719347433599 := by
  unfold tailWord_6660027
  simp only [CollatzResearch.WordTrace]
  refine ⟨242911140642867095900322335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161940760428578063933548223 242911140642867095900322335)
  ·
    refine ⟨364366710964300643850483503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242911140642867095900322335 364366710964300643850483503)
    ·
      refine ⟨546550066446450965775725255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 364366710964300643850483503 546550066446450965775725255)
      ·
        refine ⟨819825099669676448663587883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 546550066446450965775725255 819825099669676448663587883)
        ·
          refine ⟨1229737649504514672995381825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 819825099669676448663587883 1229737649504514672995381825)
          ·
            refine ⟨922303237128386004746536369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1229737649504514672995381825 922303237128386004746536369)
            ·
              refine ⟨691727427846289503559902277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 922303237128386004746536369 691727427846289503559902277)
              ·
                refine ⟨129698892721179281917481677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 691727427846289503559902277 129698892721179281917481677)
                ·
                  refine ⟨48637084770442230719055629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 129698892721179281917481677 48637084770442230719055629)
                  ·
                    refine ⟨18238906788915836519645861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48637084770442230719055629 18238906788915836519645861)
                    ·
                      refine ⟨3419795022921719347433599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18238906788915836519645861 3419795022921719347433599)
                      ·
                        rfl

theorem cell23_6660027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 4, 3, 3, 4].length) (baseStart_6660027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6660027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6660027 prefixEnd_6660027 := by exact prefixLift 6660027
  have htrace : WordTrace (prefixWord ++ tailWord_6660027) baseStart_6660027 baseEnd_6660027 := by
    simpa [prefixWord, tailWord_6660027, baseEnd_6660027] using wordTrace_append hprefix tailTrace_6660027
  have hstable : (prefixWord ++ tailWord_6660027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6660027).length < 2 ^ (prefixWord ++ tailWord_6660027).sum := by decide
  have hdescent : baseEnd_6660027 < baseStart_6660027 := by decide
  rcases family_descends (prefixWord ++ tailWord_6660027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6660044 : List Nat := [2, 2, 1, 4, 1, 2, 1, 2, 1, 3, 4]
def baseStart_6660044 : Nat := 118140960795 + 6660044 * 2 ^ 59
def prefixEnd_6660044 : Nat := 4983230072969 + 3 ^ 40 * 6660044 * 2
def baseEnd_6660044 : Nat := 3419803752092845780921021

theorem tailTrace_6660044 : CollatzResearch.WordTrace tailWord_6660044 prefixEnd_6660044 3419803752092845780921021 := by
  unfold tailWord_6660044
  simp only [CollatzResearch.WordTrace]
  refine ⟨121455880341902753901845593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161941173789203671869127457 121455880341902753901845593)
  ·
    refine ⟨91091910256427065426384195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121455880341902753901845593 91091910256427065426384195)
    ·
      refine ⟨136637865384640598139576293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91091910256427065426384195 136637865384640598139576293)
      ·
        refine ⟨25619599759620112151170555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 136637865384640598139576293 25619599759620112151170555)
        ·
          refine ⟨38429399639430168226755833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25619599759620112151170555 38429399639430168226755833)
          ·
            refine ⟨28822049729572626170066875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38429399639430168226755833 28822049729572626170066875)
            ·
              refine ⟨43233074594358939255100313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28822049729572626170066875 43233074594358939255100313)
              ·
                refine ⟨32424805945769204441325235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43233074594358939255100313 32424805945769204441325235)
                ·
                  refine ⟨48637208918653806661987853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32424805945769204441325235 48637208918653806661987853)
                  ·
                    refine ⟨18238953344495177498245445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48637208918653806661987853 18238953344495177498245445)
                    ·
                      refine ⟨3419803752092845780921021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18238953344495177498245445 3419803752092845780921021)
                      ·
                        rfl

theorem cell23_6660044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_6660044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6660044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6660044 prefixEnd_6660044 := by exact prefixLift 6660044
  have htrace : WordTrace (prefixWord ++ tailWord_6660044) baseStart_6660044 baseEnd_6660044 := by
    simpa [prefixWord, tailWord_6660044, baseEnd_6660044] using wordTrace_append hprefix tailTrace_6660044
  have hstable : (prefixWord ++ tailWord_6660044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6660044).length < 2 ^ (prefixWord ++ tailWord_6660044).sum := by decide
  have hdescent : baseEnd_6660044 < baseStart_6660044 := by decide
  rcases family_descends (prefixWord ++ tailWord_6660044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6660064 : List Nat := [2, 1, 1, 3, 1, 1, 1, 2, 6, 2, 3]
def baseStart_6660064 : Nat := 118140960795 + 6660064 * 2 ^ 59
def prefixEnd_6660064 : Nat := 4983230072969 + 3 ^ 40 * 6660064 * 2
def baseEnd_6660064 : Nat := 3419814021705935702670929

theorem tailTrace_6660064 : CollatzResearch.WordTrace tailWord_6660064 prefixEnd_6660064 3419814021705935702670929 := by
  unfold tailWord_6660064
  simp only [CollatzResearch.WordTrace]
  refine ⟨121456245071866525609709623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161941660095822034146279497 121456245071866525609709623)
  ·
    refine ⟨182184367607799788414564435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121456245071866525609709623 182184367607799788414564435)
    ·
      refine ⟨273276551411699682621846653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182184367607799788414564435 273276551411699682621846653)
      ·
        refine ⟨102478706779387380983192495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 273276551411699682621846653 102478706779387380983192495)
        ·
          refine ⟨153718060169081071474788743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102478706779387380983192495 153718060169081071474788743)
          ·
            refine ⟨230577090253621607212183115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153718060169081071474788743 230577090253621607212183115)
            ·
              refine ⟨345865635380432410818274673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 230577090253621607212183115 345865635380432410818274673)
              ·
                refine ⟨259399226535324308113706005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 345865635380432410818274673 259399226535324308113706005)
                ·
                  refine ⟨12159338743843326942829969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 259399226535324308113706005 12159338743843326942829969)
                  ·
                    refine ⟨9119504057882495207122477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12159338743843326942829969 9119504057882495207122477)
                    ·
                      refine ⟨3419814021705935702670929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9119504057882495207122477 3419814021705935702670929)
                      ·
                        rfl

theorem cell23_6660064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 6, 2, 3].length) (baseStart_6660064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6660064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6660064 prefixEnd_6660064 := by exact prefixLift 6660064
  have htrace : WordTrace (prefixWord ++ tailWord_6660064) baseStart_6660064 baseEnd_6660064 := by
    simpa [prefixWord, tailWord_6660064, baseEnd_6660064] using wordTrace_append hprefix tailTrace_6660064
  have hstable : (prefixWord ++ tailWord_6660064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6660064).length < 2 ^ (prefixWord ++ tailWord_6660064).sum := by decide
  have hdescent : baseEnd_6660064 < baseStart_6660064 := by decide
  rcases family_descends (prefixWord ++ tailWord_6660064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6660101 : List Nat := [1, 3, 1, 1, 2, 4, 4, 1, 6]
def baseStart_6660101 : Nat := 118140960795 + 6660101 * 2 ^ 59
def prefixEnd_6660101 : Nat := 4983230072969 + 3 ^ 40 * 6660101 * 2
def baseEnd_6660101 : Nat := 379981446721128006434251

theorem tailTrace_6660101 : CollatzResearch.WordTrace tailWord_6660101 prefixEnd_6660101 379981446721128006434251 := by
  unfold tailWord_6660101
  simp only [CollatzResearch.WordTrace]
  refine ⟨242913839644599006538516157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161942559763066004359010771 242913839644599006538516157)
  ·
    refine ⟨91092689866724627451943559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 242913839644599006538516157 91092689866724627451943559)
    ·
      refine ⟨136639034800086941177915339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91092689866724627451943559 136639034800086941177915339)
      ·
        refine ⟨204958552200130411766873009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136639034800086941177915339 204958552200130411766873009)
        ·
          refine ⟨153718914150097808825154757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 204958552200130411766873009 153718914150097808825154757)
          ·
            refine ⟨28822296403143339154716517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 153718914150097808825154757 28822296403143339154716517)
            ·
              refine ⟨5404180575589376091509347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28822296403143339154716517 5404180575589376091509347)
              ·
                refine ⟨8106270863384064137264021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5404180575589376091509347 8106270863384064137264021)
                ·
                  refine ⟨379981446721128006434251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8106270863384064137264021 379981446721128006434251)
                  ·
                    rfl

theorem cell23_6660101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 4, 1, 6].length) (baseStart_6660101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6660101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6660101 prefixEnd_6660101 := by exact prefixLift 6660101
  have htrace : WordTrace (prefixWord ++ tailWord_6660101) baseStart_6660101 baseEnd_6660101 := by
    simpa [prefixWord, tailWord_6660101, baseEnd_6660101] using wordTrace_append hprefix tailTrace_6660101
  have hstable : (prefixWord ++ tailWord_6660101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6660101).length < 2 ^ (prefixWord ++ tailWord_6660101).sum := by decide
  have hdescent : baseEnd_6660101 < baseStart_6660101 := by decide
  rcases family_descends (prefixWord ++ tailWord_6660101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6660145 : List Nat := [1, 2, 2, 3, 1, 4, 1, 4, 1, 1, 3]
def baseStart_6660145 : Nat := 118140960795 + 6660145 * 2 ^ 59
def prefixEnd_6660145 : Nat := 4983230072969 + 3 ^ 40 * 6660145 * 2
def baseEnd_6660145 : Nat := 3419855613638949885758057

theorem tailTrace_6660145 : CollatzResearch.WordTrace tailWord_6660145 prefixEnd_6660145 3419855613638949885758057 := by
  unfold tailWord_6660145
  simp only [CollatzResearch.WordTrace]
  refine ⟨242915444456439602053117889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161943629637626401368745259 242915444456439602053117889)
  ·
    refine ⟨182186583342329701539838417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242915444456439602053117889 182186583342329701539838417)
    ·
      refine ⟨136639937506747276154878813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182186583342329701539838417 136639937506747276154878813)
      ·
        refine ⟨51239976565030228558079555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136639937506747276154878813 51239976565030228558079555)
        ·
          refine ⟨76859964847545342837119333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51239976565030228558079555 76859964847545342837119333)
          ·
            refine ⟨14411243408914751781959875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76859964847545342837119333 14411243408914751781959875)
            ·
              refine ⟨21616865113372127672939813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14411243408914751781959875 21616865113372127672939813)
              ·
                refine ⟨4053162208757273938676215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21616865113372127672939813 4053162208757273938676215)
                ·
                  refine ⟨6079743313135910908014323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4053162208757273938676215 6079743313135910908014323)
                  ·
                    refine ⟨9119614969703866362021485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6079743313135910908014323 9119614969703866362021485)
                    ·
                      refine ⟨3419855613638949885758057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9119614969703866362021485 3419855613638949885758057)
                      ·
                        rfl

theorem cell23_6660145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 4, 1, 1, 3].length) (baseStart_6660145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6660145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6660145 prefixEnd_6660145 := by exact prefixLift 6660145
  have htrace : WordTrace (prefixWord ++ tailWord_6660145) baseStart_6660145 baseEnd_6660145 := by
    simpa [prefixWord, tailWord_6660145, baseEnd_6660145] using wordTrace_append hprefix tailTrace_6660145
  have hstable : (prefixWord ++ tailWord_6660145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6660145).length < 2 ^ (prefixWord ++ tailWord_6660145).sum := by decide
  have hdescent : baseEnd_6660145 < baseStart_6660145 := by decide
  rcases family_descends (prefixWord ++ tailWord_6660145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6660154 : List Nat := [3, 1, 1, 1, 3, 1, 1, 3, 3, 1, 5]
def baseStart_6660154 : Nat := 118140960795 + 6660154 * 2 ^ 59
def prefixEnd_6660154 : Nat := 4983230072969 + 3 ^ 40 * 6660154 * 2
def baseEnd_6660154 : Nat := 3419860234964840350545515

theorem tailTrace_6660154 : CollatzResearch.WordTrace tailWord_6660154 prefixEnd_6660154 3419860234964840350545515 := by
  unfold tailWord_6660154
  simp only [CollatzResearch.WordTrace]
  refine ⟨60728943178351749147548879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161943848475604664393463677 60728943178351749147548879)
  ·
    refine ⟨91093414767527623721323319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60728943178351749147548879 91093414767527623721323319)
    ·
      refine ⟨136640122151291435581984979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91093414767527623721323319 136640122151291435581984979)
      ·
        refine ⟨204960183226937153372977469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136640122151291435581984979 204960183226937153372977469)
        ·
          refine ⟨76860068710101432514866551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 204960183226937153372977469 76860068710101432514866551)
          ·
            refine ⟨115290103065152148772299827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76860068710101432514866551 115290103065152148772299827)
            ·
              refine ⟨172935154597728223158449741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115290103065152148772299827 172935154597728223158449741)
              ·
                refine ⟨64850682974148083684418653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 172935154597728223158449741 64850682974148083684418653)
                ·
                  refine ⟨24319006115305531381656995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64850682974148083684418653 24319006115305531381656995)
                  ·
                    refine ⟨36478509172958297072485493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24319006115305531381656995 36478509172958297072485493)
                    ·
                      refine ⟨3419860234964840350545515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36478509172958297072485493 3419860234964840350545515)
                      ·
                        rfl

theorem cell23_6660154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 3, 3, 1, 5].length) (baseStart_6660154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6660154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6660154 prefixEnd_6660154 := by exact prefixLift 6660154
  have htrace : WordTrace (prefixWord ++ tailWord_6660154) baseStart_6660154 baseEnd_6660154 := by
    simpa [prefixWord, tailWord_6660154, baseEnd_6660154] using wordTrace_append hprefix tailTrace_6660154
  have hstable : (prefixWord ++ tailWord_6660154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6660154).length < 2 ^ (prefixWord ++ tailWord_6660154).sum := by decide
  have hdescent : baseEnd_6660154 < baseStart_6660154 := by decide
  rcases family_descends (prefixWord ++ tailWord_6660154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6660161 : List Nat := [1, 2, 5, 1, 2, 1, 1, 3, 1, 6]
def baseStart_6660161 : Nat := 118140960795 + 6660161 * 2 ^ 59
def prefixEnd_6660161 : Nat := 4983230072969 + 3 ^ 40 * 6660161 * 2
def baseEnd_6660161 : Nat := 1139954609776473941052661

theorem tailTrace_6660161 : CollatzResearch.WordTrace tailWord_6660161 prefixEnd_6660161 1139954609776473941052661 := by
  unfold tailWord_6660161
  simp only [CollatzResearch.WordTrace]
  refine ⟨242916028024381636785700337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161944018682921091190466891 242916028024381636785700337)
  ·
    refine ⟨182187021018286227589275253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242916028024381636785700337 182187021018286227589275253)
    ·
      refine ⟨17080033220464333836494555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 182187021018286227589275253 17080033220464333836494555)
      ·
        refine ⟨25620049830696500754741833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17080033220464333836494555 25620049830696500754741833)
        ·
          refine ⟨19215037373022375566056375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25620049830696500754741833 19215037373022375566056375)
          ·
            refine ⟨28822556059533563349084563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19215037373022375566056375 28822556059533563349084563)
            ·
              refine ⟨43233834089300345023626845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28822556059533563349084563 43233834089300345023626845)
              ·
                refine ⟨16212687783487629383860067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43233834089300345023626845 16212687783487629383860067)
                ·
                  refine ⟨24319031675231444075790101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16212687783487629383860067 24319031675231444075790101)
                  ·
                    refine ⟨1139954609776473941052661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24319031675231444075790101 1139954609776473941052661)
                    ·
                      rfl

theorem cell23_6660161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 3, 1, 6].length) (baseStart_6660161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6660161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6660161 prefixEnd_6660161 := by exact prefixLift 6660161
  have htrace : WordTrace (prefixWord ++ tailWord_6660161) baseStart_6660161 baseEnd_6660161 := by
    simpa [prefixWord, tailWord_6660161, baseEnd_6660161] using wordTrace_append hprefix tailTrace_6660161
  have hstable : (prefixWord ++ tailWord_6660161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6660161).length < 2 ^ (prefixWord ++ tailWord_6660161).sum := by decide
  have hdescent : baseEnd_6660161 < baseStart_6660161 := by decide
  rcases family_descends (prefixWord ++ tailWord_6660161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6660181 : List Nat := [1, 3, 2, 2, 1, 3, 2, 2, 1, 2, 4]
def baseStart_6660181 : Nat := 118140960795 + 6660181 * 2 ^ 59
def prefixEnd_6660181 : Nat := 4983230072969 + 3 ^ 40 * 6660181 * 2
def baseEnd_6660181 : Nat := 3419874098942511744907891

theorem tailTrace_6660181 : CollatzResearch.WordTrace tailWord_6660181 prefixEnd_6660181 3419874098942511744907891 := by
  unfold tailWord_6660181
  simp only [CollatzResearch.WordTrace]
  refine ⟨242916757484309180201428397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161944504989539453467618931 242916757484309180201428397)
  ·
    refine ⟨91093784056615942575535649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 242916757484309180201428397 91093784056615942575535649)
    ·
      refine ⟨68320338042461956931651737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91093784056615942575535649 68320338042461956931651737)
      ·
        refine ⟨51240253531846467698738803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68320338042461956931651737 51240253531846467698738803)
        ·
          refine ⟨76860380297769701548108205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51240253531846467698738803 76860380297769701548108205)
          ·
            refine ⟨28822642611663638080540577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76860380297769701548108205 28822642611663638080540577)
            ·
              refine ⟨21616981958747728560405433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28822642611663638080540577 21616981958747728560405433)
              ·
                refine ⟨16212736469060796420304075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21616981958747728560405433 16212736469060796420304075)
                ·
                  refine ⟨24319104703591194630456113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16212736469060796420304075 24319104703591194630456113)
                  ·
                    refine ⟨18239328527693395972842085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24319104703591194630456113 18239328527693395972842085)
                    ·
                      refine ⟨3419874098942511744907891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18239328527693395972842085 3419874098942511744907891)
                      ·
                        rfl

theorem cell23_6660181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 2, 1, 2, 4].length) (baseStart_6660181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6660181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6660181 prefixEnd_6660181 := by exact prefixLift 6660181
  have htrace : WordTrace (prefixWord ++ tailWord_6660181) baseStart_6660181 baseEnd_6660181 := by
    simpa [prefixWord, tailWord_6660181, baseEnd_6660181] using wordTrace_append hprefix tailTrace_6660181
  have hstable : (prefixWord ++ tailWord_6660181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6660181).length < 2 ^ (prefixWord ++ tailWord_6660181).sum := by decide
  have hdescent : baseEnd_6660181 < baseStart_6660181 := by decide
  rcases family_descends (prefixWord ++ tailWord_6660181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6660182 : List Nat := [5, 2, 2, 1, 1, 1, 4, 1, 1, 5]
def baseStart_6660182 : Nat := 118140960795 + 6660182 * 2 ^ 59
def prefixEnd_6660182 : Nat := 4983230072969 + 3 ^ 40 * 6660182 * 2
def baseEnd_6660182 : Nat := 1139958204141055413665129

theorem tailTrace_6660182 : CollatzResearch.WordTrace tailWord_6660182 prefixEnd_6660182 1139958204141055413665129 := by
  unfold tailWord_6660182
  simp only [CollatzResearch.WordTrace]
  refine ⟨15182299622331597335763425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 161944529304870371581476533 15182299622331597335763425)
  ·
    refine ⟨11386724716748698001822569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15182299622331597335763425 11386724716748698001822569)
    ·
      refine ⟨8540043537561523501366927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11386724716748698001822569 8540043537561523501366927)
      ·
        refine ⟨12810065306342285252050391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8540043537561523501366927 12810065306342285252050391)
        ·
          refine ⟨19215097959513427878075587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12810065306342285252050391 19215097959513427878075587)
          ·
            refine ⟨28822646939270141817113381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19215097959513427878075587 28822646939270141817113381)
            ·
              refine ⟨5404246301113151590708759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28822646939270141817113381 5404246301113151590708759)
              ·
                refine ⟨8106369451669727386063139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5404246301113151590708759 8106369451669727386063139)
                ·
                  refine ⟨12159554177504591079094709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8106369451669727386063139 12159554177504591079094709)
                  ·
                    refine ⟨1139958204141055413665129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12159554177504591079094709 1139958204141055413665129)
                    ·
                      rfl

theorem cell23_6660182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_6660182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6660182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6660182 prefixEnd_6660182 := by exact prefixLift 6660182
  have htrace : WordTrace (prefixWord ++ tailWord_6660182) baseStart_6660182 baseEnd_6660182 := by
    simpa [prefixWord, tailWord_6660182, baseEnd_6660182] using wordTrace_append hprefix tailTrace_6660182
  have hstable : (prefixWord ++ tailWord_6660182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6660182).length < 2 ^ (prefixWord ++ tailWord_6660182).sum := by decide
  have hdescent : baseEnd_6660182 < baseStart_6660182 := by decide
  rcases family_descends (prefixWord ++ tailWord_6660182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6660202 : List Nat := [3, 1, 3, 2, 3, 1, 2, 1, 3, 2, 2]
def baseStart_6660202 : Nat := 118140960795 + 6660202 * 2 ^ 59
def prefixEnd_6660202 : Nat := 4983230072969 + 3 ^ 40 * 6660202 * 2
def baseEnd_6660202 : Nat := 3419884882036256162745295

theorem tailTrace_6660202 : CollatzResearch.WordTrace tailWord_6660202 prefixEnd_6660202 3419884882036256162745295 := by
  unfold tailWord_6660202
  simp only [CollatzResearch.WordTrace]
  refine ⟨60729380854308275196985715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161945015611488733858628573 60729380854308275196985715)
  ·
    refine ⟨91094071281462412795478573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60729380854308275196985715 91094071281462412795478573)
    ·
      refine ⟨34160276730548404798304465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91094071281462412795478573 34160276730548404798304465)
      ·
        refine ⟨25620207547911303598728349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34160276730548404798304465 25620207547911303598728349)
        ·
          refine ⟨9607577830466738849523131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25620207547911303598728349 9607577830466738849523131)
          ·
            refine ⟨14411366745700108274284697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9607577830466738849523131 14411366745700108274284697)
            ·
              refine ⟨10808525059275081205713523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14411366745700108274284697 10808525059275081205713523)
              ·
                refine ⟨16212787588912621808570285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10808525059275081205713523 16212787588912621808570285)
                ·
                  refine ⟨6079795345842233178213857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16212787588912621808570285 6079795345842233178213857)
                  ·
                    refine ⟨4559846509381674883660393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6079795345842233178213857 4559846509381674883660393)
                    ·
                      refine ⟨3419884882036256162745295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4559846509381674883660393 3419884882036256162745295)
                      ·
                        rfl

theorem cell23_6660202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 2, 1, 3, 2, 2].length) (baseStart_6660202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6660202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6660202 prefixEnd_6660202 := by exact prefixLift 6660202
  have htrace : WordTrace (prefixWord ++ tailWord_6660202) baseStart_6660202 baseEnd_6660202 := by
    simpa [prefixWord, tailWord_6660202, baseEnd_6660202] using wordTrace_append hprefix tailTrace_6660202
  have hstable : (prefixWord ++ tailWord_6660202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6660202).length < 2 ^ (prefixWord ++ tailWord_6660202).sum := by decide
  have hdescent : baseEnd_6660202 < baseStart_6660202 := by decide
  rcases family_descends (prefixWord ++ tailWord_6660202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6660225 : List Nat := [1, 2, 4, 2, 4, 1, 2, 7]
def baseStart_6660225 : Nat := 118140960795 + 6660225 * 2 ^ 59
def prefixEnd_6660225 : Nat := 4983230072969 + 3 ^ 40 * 6660225 * 2
def baseEnd_6660225 : Nat := 126662840447826280472507

theorem tailTrace_6660225 : CollatzResearch.WordTrace tailWord_6660225 prefixEnd_6660225 126662840447826280472507 := by
  unfold tailWord_6660225
  simp only [CollatzResearch.WordTrace]
  refine ⟨242918362296149775716030129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161945574864099850477353419 242918362296149775716030129)
  ·
    refine ⟨182188771722112331787022597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242918362296149775716030129 182188771722112331787022597)
    ·
      refine ⟨34160394697896062210066737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 182188771722112331787022597 34160394697896062210066737)
      ·
        refine ⟨25620296023422046657550053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34160394697896062210066737 25620296023422046657550053)
        ·
          refine ⟨4803805504391633748290635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25620296023422046657550053 4803805504391633748290635)
          ·
            refine ⟨7205708256587450622435953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4803805504391633748290635 7205708256587450622435953)
            ·
              refine ⟨5404281192440587966826965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7205708256587450622435953 5404281192440587966826965)
              ·
                refine ⟨126662840447826280472507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5404281192440587966826965 126662840447826280472507)
                ·
                  rfl

theorem cell23_6660225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 2, 7].length) (baseStart_6660225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6660225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6660225 prefixEnd_6660225 := by exact prefixLift 6660225
  have htrace : WordTrace (prefixWord ++ tailWord_6660225) baseStart_6660225 baseEnd_6660225 := by
    simpa [prefixWord, tailWord_6660225, baseEnd_6660225] using wordTrace_append hprefix tailTrace_6660225
  have hstable : (prefixWord ++ tailWord_6660225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6660225).length < 2 ^ (prefixWord ++ tailWord_6660225).sum := by decide
  have hdescent : baseEnd_6660225 < baseStart_6660225 := by decide
  rcases family_descends (prefixWord ++ tailWord_6660225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6660261 : List Nat := [1, 3, 1, 2, 1, 3, 2, 1, 2, 4, 3]
def baseStart_6660261 : Nat := 118140960795 + 6660261 * 2 ^ 59
def prefixEnd_6660261 : Nat := 4983230072969 + 3 ^ 40 * 6660261 * 2
def baseEnd_6660261 : Nat := 3419915177394871431907523

theorem tailTrace_6660261 : CollatzResearch.WordTrace tailWord_6660261 prefixEnd_6660261 3419915177394871431907523 := by
  unfold tailWord_6660261
  simp only [CollatzResearch.WordTrace]
  refine ⟨242919675324019353864340637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161946450216012902576227091 242919675324019353864340637)
  ·
    refine ⟨91094878246507257699127739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 242919675324019353864340637 91094878246507257699127739)
    ·
      refine ⟨136642317369760886548691609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91094878246507257699127739 136642317369760886548691609)
      ·
        refine ⟨102481738027320664911518707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136642317369760886548691609 102481738027320664911518707)
        ·
          refine ⟨153722607040980997367278061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102481738027320664911518707 153722607040980997367278061)
          ·
            refine ⟨57645977640367874012729273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 153722607040980997367278061 57645977640367874012729273)
            ·
              refine ⟨43234483230275905509546955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57645977640367874012729273 43234483230275905509546955)
              ·
                refine ⟨64851724845413858264320433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43234483230275905509546955 64851724845413858264320433)
                ·
                  refine ⟨48638793634060393698240325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64851724845413858264320433 48638793634060393698240325)
                  ·
                    refine ⟨9119773806386323818420061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48638793634060393698240325 9119773806386323818420061)
                    ·
                      refine ⟨3419915177394871431907523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9119773806386323818420061 3419915177394871431907523)
                      ·
                        rfl

theorem cell23_6660261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 1, 2, 4, 3].length) (baseStart_6660261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6660261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6660261 prefixEnd_6660261 := by exact prefixLift 6660261
  have htrace : WordTrace (prefixWord ++ tailWord_6660261) baseStart_6660261 baseEnd_6660261 := by
    simpa [prefixWord, tailWord_6660261, baseEnd_6660261] using wordTrace_append hprefix tailTrace_6660261
  have hstable : (prefixWord ++ tailWord_6660261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6660261).length < 2 ^ (prefixWord ++ tailWord_6660261).sum := by decide
  have hdescent : baseEnd_6660261 < baseStart_6660261 := by decide
  rcases family_descends (prefixWord ++ tailWord_6660261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6660269 : List Nat := [1, 5, 2, 1, 2, 3, 2, 1, 2, 1, 3]
def baseStart_6660269 : Nat := 118140960795 + 6660269 * 2 ^ 59
def prefixEnd_6660269 : Nat := 4983230072969 + 3 ^ 40 * 6660269 * 2
def baseEnd_6660269 : Nat := 3419919285240107400607487

theorem tailTrace_6660269 : CollatzResearch.WordTrace tailWord_6660269 prefixEnd_6660269 3419919285240107400607487 := by
  unfold tailWord_6660269
  simp only [CollatzResearch.WordTrace]
  refine ⟨242919967107990371230631861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161946644738660247487087907 242919967107990371230631861)
  ·
    refine ⟨22773746916374097302871737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 242919967107990371230631861 22773746916374097302871737)
    ·
      refine ⟨17080310187280572977153803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22773746916374097302871737 17080310187280572977153803)
      ·
        refine ⟨25620465280920859465730705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17080310187280572977153803 25620465280920859465730705)
        ·
          refine ⟨19215348960690644599298029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25620465280920859465730705 19215348960690644599298029)
          ·
            refine ⟨7205755860258991724736761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19215348960690644599298029 7205755860258991724736761)
            ·
              refine ⟨5404316895194243793552571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7205755860258991724736761 5404316895194243793552571)
              ·
                refine ⟨8106475342791365690328857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5404316895194243793552571 8106475342791365690328857)
                ·
                  refine ⟨6079856507093524267746643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8106475342791365690328857 6079856507093524267746643)
                  ·
                    refine ⟨9119784760640286401619965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6079856507093524267746643 9119784760640286401619965)
                    ·
                      refine ⟨3419919285240107400607487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9119784760640286401619965 3419919285240107400607487)
                      ·
                        rfl

theorem cell23_6660269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 2, 1, 2, 1, 3].length) (baseStart_6660269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6660269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6660269 prefixEnd_6660269 := by exact prefixLift 6660269
  have htrace : WordTrace (prefixWord ++ tailWord_6660269) baseStart_6660269 baseEnd_6660269 := by
    simpa [prefixWord, tailWord_6660269, baseEnd_6660269] using wordTrace_append hprefix tailTrace_6660269
  have hstable : (prefixWord ++ tailWord_6660269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6660269).length < 2 ^ (prefixWord ++ tailWord_6660269).sum := by decide
  have hdescent : baseEnd_6660269 < baseStart_6660269 := by decide
  rcases family_descends (prefixWord ++ tailWord_6660269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6660298 : List Nat := [3, 1, 2, 1, 3, 1, 2, 5, 5]
def baseStart_6660298 : Nat := 118140960795 + 6660298 * 2 ^ 59
def prefixEnd_6660298 : Nat := 4983230072969 + 3 ^ 40 * 6660298 * 2
def baseEnd_6660298 : Nat := 379992686242120865238317

theorem tailTrace_6660298 : CollatzResearch.WordTrace tailWord_6660298 prefixEnd_6660298 379992686242120865238317 := by
  unfold tailWord_6660298
  simp only [CollatzResearch.WordTrace]
  refine ⟨60730256206221327295859387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161947349883256872788958365 60730256206221327295859387)
  ·
    refine ⟨91095384309331990943789081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60730256206221327295859387 91095384309331990943789081)
    ·
      refine ⟨68321538231998993207841811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91095384309331990943789081 68321538231998993207841811)
      ·
        refine ⟨102482307347998489811762717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68321538231998993207841811 102482307347998489811762717)
        ·
          refine ⟨38430865255499433679411019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102482307347998489811762717 38430865255499433679411019)
          ·
            refine ⟨57646297883249150519116529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38430865255499433679411019 57646297883249150519116529)
            ·
              refine ⟨43234723412436862889337397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57646297883249150519116529 43234723412436862889337397)
              ·
                refine ⟨4053255319915955895875381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43234723412436862889337397 4053255319915955895875381)
                ·
                  refine ⟨379992686242120865238317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4053255319915955895875381 379992686242120865238317)
                  ·
                    rfl

theorem cell23_6660298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 5, 5].length) (baseStart_6660298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6660298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6660298 prefixEnd_6660298 := by exact prefixLift 6660298
  have htrace : WordTrace (prefixWord ++ tailWord_6660298) baseStart_6660298 baseEnd_6660298 := by
    simpa [prefixWord, tailWord_6660298, baseEnd_6660298] using wordTrace_append hprefix tailTrace_6660298
  have hstable : (prefixWord ++ tailWord_6660298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6660298).length < 2 ^ (prefixWord ++ tailWord_6660298).sum := by decide
  have hdescent : baseEnd_6660298 < baseStart_6660298 := by decide
  rcases family_descends (prefixWord ++ tailWord_6660298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6660309 : List Nat := [1, 3, 2, 4, 2, 1, 2, 2, 2, 2, 2]
def baseStart_6660309 : Nat := 118140960795 + 6660309 * 2 ^ 59
def prefixEnd_6660309 : Nat := 4983230072969 + 3 ^ 40 * 6660309 * 2
def baseEnd_6660309 : Nat := 3419939824466287244107303

theorem tailTrace_6660309 : CollatzResearch.WordTrace tailWord_6660309 prefixEnd_6660309 3419939824466287244107303 := by
  unfold tailWord_6660309
  simp only [CollatzResearch.WordTrace]
  refine ⟨242921426027845458062087981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161947617351896972041391987 242921426027845458062087981)
  ·
    refine ⟨91095534760442046773282993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 242921426027845458062087981 91095534760442046773282993)
    ·
      refine ⟨68321651070331535079962245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91095534760442046773282993 68321651070331535079962245)
      ·
        refine ⟨12810309575687162827492921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68321651070331535079962245 12810309575687162827492921)
        ·
          refine ⟨9607732181765372120619691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12810309575687162827492921 9607732181765372120619691)
          ·
            refine ⟨14411598272648058180929537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9607732181765372120619691 14411598272648058180929537)
            ·
              refine ⟨10808698704486043635697153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14411598272648058180929537 10808698704486043635697153)
              ·
                refine ⟨8106524028364532726772865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10808698704486043635697153 8106524028364532726772865)
                ·
                  refine ⟨6079893021273399545079649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8106524028364532726772865 6079893021273399545079649)
                  ·
                    refine ⟨4559919765955049658809737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6079893021273399545079649 4559919765955049658809737)
                    ·
                      refine ⟨3419939824466287244107303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4559919765955049658809737 3419939824466287244107303)
                      ·
                        rfl

theorem cell23_6660309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 2, 2, 2, 2, 2].length) (baseStart_6660309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6660309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6660309 prefixEnd_6660309 := by exact prefixLift 6660309
  have htrace : WordTrace (prefixWord ++ tailWord_6660309) baseStart_6660309 baseEnd_6660309 := by
    simpa [prefixWord, tailWord_6660309, baseEnd_6660309] using wordTrace_append hprefix tailTrace_6660309
  have hstable : (prefixWord ++ tailWord_6660309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6660309).length < 2 ^ (prefixWord ++ tailWord_6660309).sum := by decide
  have hdescent : baseEnd_6660309 < baseStart_6660309 := by decide
  rcases family_descends (prefixWord ++ tailWord_6660309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6660321 : List Nat := [1, 2, 3, 1, 3, 1, 1, 3, 1, 2, 5]
def baseStart_6660321 : Nat := 118140960795 + 6660321 * 2 ^ 59
def prefixEnd_6660321 : Nat := 4983230072969 + 3 ^ 40 * 6660321 * 2
def baseEnd_6660321 : Nat := 3419945986234141197157247

theorem tailTrace_6660321 : CollatzResearch.WordTrace tailWord_6660321 prefixEnd_6660321 3419945986234141197157247 := by
  unfold tailWord_6660321
  simp only [CollatzResearch.WordTrace]
  refine ⟨242921863703801984111524817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161947909135867989407683211 242921863703801984111524817)
  ·
    refine ⟨182191397777851488083643613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242921863703801984111524817 182191397777851488083643613)
    ·
      refine ⟨68321774166694308031366355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182191397777851488083643613 68321774166694308031366355)
      ·
        refine ⟨102482661250041462047049533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68321774166694308031366355 102482661250041462047049533)
        ·
          refine ⟨38430997968765548267643575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102482661250041462047049533 38430997968765548267643575)
          ·
            refine ⟨57646496953148322401465363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38430997968765548267643575 57646496953148322401465363)
            ·
              refine ⟨86469745429722483602198045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57646496953148322401465363 86469745429722483602198045)
              ·
                refine ⟨32426154536145931350824267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86469745429722483602198045 32426154536145931350824267)
                ·
                  refine ⟨48639231804218897026236401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32426154536145931350824267 48639231804218897026236401)
                  ·
                    refine ⟨36479423853164172769677301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48639231804218897026236401 36479423853164172769677301)
                    ·
                      refine ⟨3419945986234141197157247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36479423853164172769677301 3419945986234141197157247)
                      ·
                        rfl

theorem cell23_6660321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 3, 1, 2, 5].length) (baseStart_6660321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6660321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6660321 prefixEnd_6660321 := by exact prefixLift 6660321
  have htrace : WordTrace (prefixWord ++ tailWord_6660321) baseStart_6660321 baseEnd_6660321 := by
    simpa [prefixWord, tailWord_6660321, baseEnd_6660321] using wordTrace_append hprefix tailTrace_6660321
  have hstable : (prefixWord ++ tailWord_6660321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6660321).length < 2 ^ (prefixWord ++ tailWord_6660321).sum := by decide
  have hdescent : baseEnd_6660321 < baseStart_6660321 := by decide
  rcases family_descends (prefixWord ++ tailWord_6660321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6660331 : List Nat := [1, 1, 1, 1, 2, 5, 2, 2, 1, 3, 4]
def baseStart_6660331 : Nat := 118140960795 + 6660331 * 2 ^ 59
def prefixEnd_6660331 : Nat := 4983230072969 + 3 ^ 40 * 6660331 * 2
def baseEnd_6660331 : Nat := 3419951121040686158032201

theorem tailTrace_6660331 : CollatzResearch.WordTrace tailWord_6660331 prefixEnd_6660331 3419951121040686158032201 := by
  unfold tailWord_6660331
  simp only [CollatzResearch.WordTrace]
  refine ⟨242922228433765755819388847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161948152289177170546259231 242922228433765755819388847)
  ·
    refine ⟨364383342650648633729083271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242922228433765755819388847 364383342650648633729083271)
    ·
      refine ⟨546575013975972950593624907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 364383342650648633729083271 546575013975972950593624907)
      ·
        refine ⟨819862520963959425890437361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 546575013975972950593624907 819862520963959425890437361)
        ·
          refine ⟨614896890722969569417828021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 819862520963959425890437361 614896890722969569417828021)
          ·
            refine ⟨57646583505278397132921377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 614896890722969569417828021 57646583505278397132921377)
            ·
              refine ⟨43234937628958797849691033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57646583505278397132921377 43234937628958797849691033)
              ·
                refine ⟨32426203221719098387268275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43234937628958797849691033 32426203221719098387268275)
                ·
                  refine ⟨48639304832578647580902413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32426203221719098387268275 48639304832578647580902413)
                  ·
                    refine ⟨18239739312216992842838405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48639304832578647580902413 18239739312216992842838405)
                    ·
                      refine ⟨3419951121040686158032201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18239739312216992842838405 3419951121040686158032201)
                      ·
                        rfl

theorem cell23_6660331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 2, 1, 3, 4].length) (baseStart_6660331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6660331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6660331 prefixEnd_6660331 := by exact prefixLift 6660331
  have htrace : WordTrace (prefixWord ++ tailWord_6660331) baseStart_6660331 baseEnd_6660331 := by
    simpa [prefixWord, tailWord_6660331, baseEnd_6660331] using wordTrace_append hprefix tailTrace_6660331
  have hstable : (prefixWord ++ tailWord_6660331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6660331).length < 2 ^ (prefixWord ++ tailWord_6660331).sum := by decide
  have hdescent : baseEnd_6660331 < baseStart_6660331 := by decide
  rcases family_descends (prefixWord ++ tailWord_6660331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6660348 : List Nat := [2, 2, 2, 1, 4, 2, 1, 1, 1, 3, 4]
def baseStart_6660348 : Nat := 118140960795 + 6660348 * 2 ^ 59
def prefixEnd_6660348 : Nat := 4983230072969 + 3 ^ 40 * 6660348 * 2
def baseEnd_6660348 : Nat := 3419959850211812591519623

theorem tailTrace_6660348 : CollatzResearch.WordTrace tailWord_6660348 prefixEnd_6660348 3419959850211812591519623 := by
  unfold tailWord_6660348
  simp only [CollatzResearch.WordTrace]
  refine ⟨121461424237352083861378849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161948565649802778481838465 121461424237352083861378849)
  ·
    refine ⟨91096068178014062896034137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121461424237352083861378849 91096068178014062896034137)
    ·
      refine ⟨68322051133510547172025603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91096068178014062896034137 68322051133510547172025603)
      ·
        refine ⟨102483076700265820758038405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68322051133510547172025603 102483076700265820758038405)
        ·
          refine ⟨19215576881299841392132201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102483076700265820758038405 19215576881299841392132201)
          ·
            refine ⟨14411682660974881044099151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19215576881299841392132201 14411682660974881044099151)
            ·
              refine ⟨21617523991462321566148727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14411682660974881044099151 21617523991462321566148727)
              ·
                refine ⟨32426285987193482349223091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21617523991462321566148727 32426285987193482349223091)
                ·
                  refine ⟨48639428980790223523834637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32426285987193482349223091 48639428980790223523834637)
                  ·
                    refine ⟨18239785867796333821437989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48639428980790223523834637 18239785867796333821437989)
                    ·
                      refine ⟨3419959850211812591519623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18239785867796333821437989 3419959850211812591519623)
                      ·
                        rfl

theorem cell23_6660348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 1, 1, 3, 4].length) (baseStart_6660348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6660348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6660348 prefixEnd_6660348 := by exact prefixLift 6660348
  have htrace : WordTrace (prefixWord ++ tailWord_6660348) baseStart_6660348 baseEnd_6660348 := by
    simpa [prefixWord, tailWord_6660348, baseEnd_6660348] using wordTrace_append hprefix tailTrace_6660348
  have hstable : (prefixWord ++ tailWord_6660348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6660348).length < 2 ^ (prefixWord ++ tailWord_6660348).sum := by decide
  have hdescent : baseEnd_6660348 < baseStart_6660348 := by decide
  rcases family_descends (prefixWord ++ tailWord_6660348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6660361 : List Nat := [1, 2, 1, 1, 3, 4, 1, 1, 2, 1, 6]
def baseStart_6660361 : Nat := 118140960795 + 6660361 * 2 ^ 59
def prefixEnd_6660361 : Nat := 4983230072969 + 3 ^ 40 * 6660361 * 2
def baseEnd_6660361 : Nat := 3419966525460321040657063

theorem tailTrace_6660361 : CollatzResearch.WordTrace tailWord_6660361 prefixEnd_6660361 3419966525460321040657063 := by
  unfold tailWord_6660361
  simp only [CollatzResearch.WordTrace]
  refine ⟨242923322623657070942980937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161948881749104713961987291 242923322623657070942980937)
  ·
    refine ⟨182192491967742803207235703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242923322623657070942980937 182192491967742803207235703)
    ·
      refine ⟨273288737951614204810853555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182192491967742803207235703 273288737951614204810853555)
      ·
        refine ⟨409933106927421307216280333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273288737951614204810853555 409933106927421307216280333)
        ·
          refine ⟨153724915097782990206105125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 409933106927421307216280333 153724915097782990206105125)
          ·
            refine ⟨28823421580834310663644711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 153724915097782990206105125 28823421580834310663644711)
            ·
              refine ⟨43235132371251465995467067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28823421580834310663644711 43235132371251465995467067)
              ·
                refine ⟨64852698556877198993200601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43235132371251465995467067 64852698556877198993200601)
                ·
                  refine ⟨48639523917657899244900451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64852698556877198993200601 48639523917657899244900451)
                  ·
                    refine ⟨72959285876486848867350677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48639523917657899244900451 72959285876486848867350677)
                    ·
                      refine ⟨3419966525460321040657063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72959285876486848867350677 3419966525460321040657063)
                      ·
                        rfl

theorem cell23_6660361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 1, 2, 1, 6].length) (baseStart_6660361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6660361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6660361 prefixEnd_6660361 := by exact prefixLift 6660361
  have htrace : WordTrace (prefixWord ++ tailWord_6660361) baseStart_6660361 baseEnd_6660361 := by
    simpa [prefixWord, tailWord_6660361, baseEnd_6660361] using wordTrace_append hprefix tailTrace_6660361
  have hstable : (prefixWord ++ tailWord_6660361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6660361).length < 2 ^ (prefixWord ++ tailWord_6660361).sum := by decide
  have hdescent : baseEnd_6660361 < baseStart_6660361 := by decide
  rcases family_descends (prefixWord ++ tailWord_6660361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6660375 : List Nat := [1, 1, 3, 4, 1, 3, 2, 1, 3, 4]
def baseStart_6660375 : Nat := 118140960795 + 6660375 * 2 ^ 59
def prefixEnd_6660375 : Nat := 4983230072969 + 3 ^ 40 * 6660375 * 2
def baseEnd_6660375 : Nat := 1139991238063161328627333

theorem tailTrace_6660375 : CollatzResearch.WordTrace tailWord_6660375 prefixEnd_6660375 1139991238063161328627333 := by
  unfold tailWord_6660375
  simp only [CollatzResearch.WordTrace]
  refine ⟨242923833245606351333990579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161949222163737567555993719 242923833245606351333990579)
  ·
    refine ⟨364385749868409527000985869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242923833245606351333990579 364385749868409527000985869)
    ·
      refine ⟨136644656200653572625369701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 364385749868409527000985869 136644656200653572625369701)
      ·
        refine ⟨25620873037622544867256819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 136644656200653572625369701 25620873037622544867256819)
        ·
          refine ⟨38431309556433817300885229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25620873037622544867256819 38431309556433817300885229)
          ·
            refine ⟨14411741083662681487831961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38431309556433817300885229 14411741083662681487831961)
            ·
              refine ⟨10808805812747011115873971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14411741083662681487831961 10808805812747011115873971)
              ·
                refine ⟨16213208719120516673810957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10808805812747011115873971 16213208719120516673810957)
                ·
                  refine ⟨6079953269670193752679109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16213208719120516673810957 6079953269670193752679109)
                  ·
                    refine ⟨1139991238063161328627333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6079953269670193752679109 1139991238063161328627333)
                    ·
                      rfl

theorem cell23_6660375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 2, 1, 3, 4].length) (baseStart_6660375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6660375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6660375 prefixEnd_6660375 := by exact prefixLift 6660375
  have htrace : WordTrace (prefixWord ++ tailWord_6660375) baseStart_6660375 baseEnd_6660375 := by
    simpa [prefixWord, tailWord_6660375, baseEnd_6660375] using wordTrace_append hprefix tailTrace_6660375
  have hstable : (prefixWord ++ tailWord_6660375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6660375).length < 2 ^ (prefixWord ++ tailWord_6660375).sum := by decide
  have hdescent : baseEnd_6660375 < baseStart_6660375 := by decide
  rcases family_descends (prefixWord ++ tailWord_6660375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6660409 : List Nat := [1, 2, 1, 6, 1, 3, 1, 3, 1, 4]
def baseStart_6660409 : Nat := 118140960795 + 6660409 * 2 ^ 59
def prefixEnd_6660409 : Nat := 4983230072969 + 3 ^ 40 * 6660409 * 2
def baseEnd_6660409 : Nat := 1139997057510578950952281

theorem tailTrace_6660409 : CollatzResearch.WordTrace tailWord_6660409 prefixEnd_6660409 1139997057510578950952281 := by
  unfold tailWord_6660409
  simp only [CollatzResearch.WordTrace]
  refine ⟨242925073327483175140728281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161950048884988783427152187 242925073327483175140728281)
  ·
    refine ⟨182193804995612381355546211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242925073327483175140728281 182193804995612381355546211)
    ·
      refine ⟨273290707493418572033319317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182193804995612381355546211 273290707493418572033319317)
      ·
        refine ⟨12810501913753995564061843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 273290707493418572033319317 12810501913753995564061843)
        ·
          refine ⟨19215752870630993346092765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12810501913753995564061843 19215752870630993346092765)
          ·
            refine ⟨7205907326486622504784787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19215752870630993346092765 7205907326486622504784787)
            ·
              refine ⟨10808860989729933757177181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7205907326486622504784787 10808860989729933757177181)
              ·
                refine ⟨4053322871148725158941443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10808860989729933757177181 4053322871148725158941443)
                ·
                  refine ⟨6079984306723087738412165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4053322871148725158941443 6079984306723087738412165)
                  ·
                    refine ⟨1139997057510578950952281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6079984306723087738412165 1139997057510578950952281)
                    ·
                      rfl

theorem cell23_6660409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 1, 3, 1, 4].length) (baseStart_6660409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6660409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6660409 prefixEnd_6660409 := by exact prefixLift 6660409
  have htrace : WordTrace (prefixWord ++ tailWord_6660409) baseStart_6660409 baseEnd_6660409 := by
    simpa [prefixWord, tailWord_6660409, baseEnd_6660409] using wordTrace_append hprefix tailTrace_6660409
  have hstable : (prefixWord ++ tailWord_6660409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6660409).length < 2 ^ (prefixWord ++ tailWord_6660409).sum := by decide
  have hdescent : baseEnd_6660409 < baseStart_6660409 := by decide
  rcases family_descends (prefixWord ++ tailWord_6660409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6660431 : List Nat := [1, 1, 2, 1, 1, 2, 1, 3, 5, 6]
def baseStart_6660431 : Nat := 118140960795 + 6660431 * 2 ^ 59
def prefixEnd_6660431 : Nat := 4983230072969 + 3 ^ 40 * 6660431 * 2
def baseEnd_6660431 : Nat := 1140000823035378588927247

theorem tailTrace_6660431 : CollatzResearch.WordTrace tailWord_6660431 prefixEnd_6660431 1140000823035378588927247 := by
  unfold tailWord_6660431
  simp only [CollatzResearch.WordTrace]
  refine ⟨242925875733403472898029147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161950583822268981932019431 242925875733403472898029147)
  ·
    refine ⟨364388813600105209347043721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242925875733403472898029147 364388813600105209347043721)
    ·
      refine ⟨273291610200078907010282791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 364388813600105209347043721 273291610200078907010282791)
      ·
        refine ⟨409937415300118360515424187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273291610200078907010282791 409937415300118360515424187)
        ·
          refine ⟨614906122950177540773136281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 409937415300118360515424187 614906122950177540773136281)
          ·
            refine ⟨461179592212633155579852211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 614906122950177540773136281 461179592212633155579852211)
            ·
              refine ⟨691769388318949733369778317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 461179592212633155579852211 691769388318949733369778317)
              ·
                refine ⟨259413520619606150013666869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 691769388318949733369778317 259413520619606150013666869)
                ·
                  refine ⟨24320017558088076563781269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 259413520619606150013666869 24320017558088076563781269)
                  ·
                    refine ⟨1140000823035378588927247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24320017558088076563781269 1140000823035378588927247)
                    ·
                      rfl

theorem cell23_6660431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 5, 6].length) (baseStart_6660431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6660431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6660431 prefixEnd_6660431 := by exact prefixLift 6660431
  have htrace : WordTrace (prefixWord ++ tailWord_6660431) baseStart_6660431 baseEnd_6660431 := by
    simpa [prefixWord, tailWord_6660431, baseEnd_6660431] using wordTrace_append hprefix tailTrace_6660431
  have hstable : (prefixWord ++ tailWord_6660431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6660431).length < 2 ^ (prefixWord ++ tailWord_6660431).sum := by decide
  have hdescent : baseEnd_6660431 < baseStart_6660431 := by decide
  rcases family_descends (prefixWord ++ tailWord_6660431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6660432 : List Nat := [2, 1, 1, 1, 1, 8, 1, 1, 3, 1, 3]
def baseStart_6660432 : Nat := 118140960795 + 6660432 * 2 ^ 59
def prefixEnd_6660432 : Nat := 4983230072969 + 3 ^ 40 * 6660432 * 2
def baseEnd_6660432 : Nat := 3420002982586790262869237

theorem tailTrace_6660432 : CollatzResearch.WordTrace tailWord_6660432 prefixEnd_6660432 3420002982586790262869237 := by
  unfold tailWord_6660432
  simp only [CollatzResearch.WordTrace]
  refine ⟨121462956103199925034407775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161950608137599900045877033 121462956103199925034407775)
  ·
    refine ⟨182194434154799887551611663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121462956103199925034407775 182194434154799887551611663)
    ·
      refine ⟨273291651232199831327417495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182194434154799887551611663 273291651232199831327417495)
      ·
        refine ⟨409937476848299746991126243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273291651232199831327417495 409937476848299746991126243)
        ·
          refine ⟨614906215272449620486689365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 409937476848299746991126243 614906215272449620486689365)
          ·
            refine ⟨7205932210224018990078391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 614906215272449620486689365 7205932210224018990078391)
            ·
              refine ⟨10808898315336028485117587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7205932210224018990078391 10808898315336028485117587)
              ·
                refine ⟨16213347473004042727676381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10808898315336028485117587 16213347473004042727676381)
                ·
                  refine ⟨6080005302376516022878643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16213347473004042727676381 6080005302376516022878643)
                  ·
                    refine ⟨9120007953564774034317965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6080005302376516022878643 9120007953564774034317965)
                    ·
                      refine ⟨3420002982586790262869237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9120007953564774034317965 3420002982586790262869237)
                      ·
                        rfl

theorem cell23_6660432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 1, 1, 3, 1, 3].length) (baseStart_6660432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6660432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6660432 prefixEnd_6660432 := by exact prefixLift 6660432
  have htrace : WordTrace (prefixWord ++ tailWord_6660432) baseStart_6660432 baseEnd_6660432 := by
    simpa [prefixWord, tailWord_6660432, baseEnd_6660432] using wordTrace_append hprefix tailTrace_6660432
  have hstable : (prefixWord ++ tailWord_6660432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6660432).length < 2 ^ (prefixWord ++ tailWord_6660432).sum := by decide
  have hdescent : baseEnd_6660432 < baseStart_6660432 := by decide
  rcases family_descends (prefixWord ++ tailWord_6660432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6660455 : List Nat := [1, 1, 5, 1, 3, 2, 1, 1, 3, 1, 4]
def baseStart_6660455 : Nat := 118140960795 + 6660455 * 2 ^ 59
def prefixEnd_6660455 : Nat := 4983230072969 + 3 ^ 40 * 6660455 * 2
def baseEnd_6660455 : Nat := 3420014792641843672881631

theorem tailTrace_6660455 : CollatzResearch.WordTrace tailWord_6660455 prefixEnd_6660455 3420014792641843672881631 := by
  unfold tailWord_6660455
  simp only [CollatzResearch.WordTrace]
  refine ⟨242926751085316524996902819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161951167390211016664601879 242926751085316524996902819)
  ·
    refine ⟨364390126627974787495354229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242926751085316524996902819 364390126627974787495354229)
    ·
      refine ⟨34161574371372636327689459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 364390126627974787495354229 34161574371372636327689459)
      ·
        refine ⟨51242361557058954491534189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34161574371372636327689459 51242361557058954491534189)
        ·
          refine ⟨19215885583897107934325321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51242361557058954491534189 19215885583897107934325321)
          ·
            refine ⟨14411914187922830950743991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19215885583897107934325321 14411914187922830950743991)
            ·
              refine ⟨21617871281884246426115987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14411914187922830950743991 21617871281884246426115987)
              ·
                refine ⟨32426806922826369639173981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21617871281884246426115987 32426806922826369639173981)
                ·
                  refine ⟨12160052596059888614690243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32426806922826369639173981 12160052596059888614690243)
                  ·
                    refine ⟨18240078894089832922035365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12160052596059888614690243 18240078894089832922035365)
                    ·
                      refine ⟨3420014792641843672881631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18240078894089832922035365 3420014792641843672881631)
                      ·
                        rfl

theorem cell23_6660455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 1, 3, 1, 4].length) (baseStart_6660455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6660455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6660455 prefixEnd_6660455 := by exact prefixLift 6660455
  have htrace : WordTrace (prefixWord ++ tailWord_6660455) baseStart_6660455 baseEnd_6660455 := by
    simpa [prefixWord, tailWord_6660455, baseEnd_6660455] using wordTrace_append hprefix tailTrace_6660455
  have hstable : (prefixWord ++ tailWord_6660455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6660455).length < 2 ^ (prefixWord ++ tailWord_6660455).sum := by decide
  have hdescent : baseEnd_6660455 < baseStart_6660455 := by decide
  rcases family_descends (prefixWord ++ tailWord_6660455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6660475 : List Nat := [1, 1, 1, 1, 1, 9, 1, 1, 1, 1, 5]
def baseStart_6660475 : Nat := 118140960795 + 6660475 * 2 ^ 59
def prefixEnd_6660475 : Nat := 4983230072969 + 3 ^ 40 * 6660475 * 2
def baseEnd_6660475 : Nat := 3420025062254933594631539

theorem tailTrace_6660475 : CollatzResearch.WordTrace tailWord_6660475 prefixEnd_6660475 3420025062254933594631539 := by
  unfold tailWord_6660475
  simp only [CollatzResearch.WordTrace]
  refine ⟨242927480545244068412630879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161951653696829378941753919 242927480545244068412630879)
  ·
    refine ⟨364391220817866102618946319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242927480545244068412630879 364391220817866102618946319)
    ·
      refine ⟨546586831226799153928419479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 364391220817866102618946319 546586831226799153928419479)
      ·
        refine ⟨819880246840198730892629219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 546586831226799153928419479 819880246840198730892629219)
        ·
          refine ⟨1229820370260298096338943829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 819880246840198730892629219 1229820370260298096338943829)
          ·
            refine ⟨7205978731993934158235999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1229820370260298096338943829 7205978731993934158235999)
            ·
              refine ⟨10808968097990901237353999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7205978731993934158235999 10808968097990901237353999)
              ·
                refine ⟨16213452146986351856030999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10808968097990901237353999 16213452146986351856030999)
                ·
                  refine ⟨24320178220479527784046499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16213452146986351856030999 24320178220479527784046499)
                  ·
                    refine ⟨36480267330719291676069749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24320178220479527784046499 36480267330719291676069749)
                    ·
                      refine ⟨3420025062254933594631539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36480267330719291676069749 3420025062254933594631539)
                      ·
                        rfl

theorem cell23_6660475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 1, 1, 1, 1, 5].length) (baseStart_6660475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6660475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6660475 prefixEnd_6660475 := by exact prefixLift 6660475
  have htrace : WordTrace (prefixWord ++ tailWord_6660475) baseStart_6660475 baseEnd_6660475 := by
    simpa [prefixWord, tailWord_6660475, baseEnd_6660475] using wordTrace_append hprefix tailTrace_6660475
  have hstable : (prefixWord ++ tailWord_6660475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6660475).length < 2 ^ (prefixWord ++ tailWord_6660475).sum := by decide
  have hdescent : baseEnd_6660475 < baseStart_6660475 := by decide
  rcases family_descends (prefixWord ++ tailWord_6660475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6660478 : List Nat := [4, 2, 3, 14]
def baseStart_6660478 : Nat := 118140960795 + 6660478 * 2 ^ 59
def prefixEnd_6660478 : Nat := 4983230072969 + 3 ^ 40 * 6660478 * 2
def baseEnd_6660478 : Nat := 1563798172243665790075

theorem tailTrace_6660478 : CollatzResearch.WordTrace tailWord_6660478 prefixEnd_6660478 1563798172243665790075 := by
  unfold tailWord_6660478
  simp only [CollatzResearch.WordTrace]
  refine ⟨30365948745529149990623761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 161951726642822133283326725 30365948745529149990623761)
  ·
    refine ⟨22774461559146862492967821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30365948745529149990623761 22774461559146862492967821)
    ·
      refine ⟨8540423084680073434862933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22774461559146862492967821 8540423084680073434862933)
      ·
        refine ⟨1563798172243665790075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 14 8540423084680073434862933 1563798172243665790075)
        ·
          rfl

theorem cell23_6660478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 14].length) (baseStart_6660478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6660478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6660478 prefixEnd_6660478 := by exact prefixLift 6660478
  have htrace : WordTrace (prefixWord ++ tailWord_6660478) baseStart_6660478 baseEnd_6660478 := by
    simpa [prefixWord, tailWord_6660478, baseEnd_6660478] using wordTrace_append hprefix tailTrace_6660478
  have hstable : (prefixWord ++ tailWord_6660478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6660478).length < 2 ^ (prefixWord ++ tailWord_6660478).sum := by decide
  have hdescent : baseEnd_6660478 < baseStart_6660478 := by decide
  rcases family_descends (prefixWord ++ tailWord_6660478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6660483 : List Nat := [1, 1, 1, 3, 7, 1, 2, 2, 1, 1, 3]
def baseStart_6660483 : Nat := 118140960795 + 6660483 * 2 ^ 59
def prefixEnd_6660483 : Nat := 4983230072969 + 3 ^ 40 * 6660483 * 2
def baseEnd_6660483 : Nat := 3420029170100169563331503

theorem tailTrace_6660483 : CollatzResearch.WordTrace tailWord_6660483 prefixEnd_6660483 3420029170100169563331503 := by
  unfold tailWord_6660483
  simp only [CollatzResearch.WordTrace]
  refine ⟨242927772329215085778922103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161951848219476723852614735 242927772329215085778922103)
  ·
    refine ⟨364391658493822628668383155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242927772329215085778922103 364391658493822628668383155)
    ·
      refine ⟨546587487740733943002574733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 364391658493822628668383155 546587487740733943002574733)
      ·
        refine ⟨204970307902775228625965525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 546587487740733943002574733 204970307902775228625965525)
        ·
          refine ⟨4803991591471294420921067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 204970307902775228625965525 4803991591471294420921067)
          ·
            refine ⟨7205987387206941631381601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4803991591471294420921067 7205987387206941631381601)
            ·
              refine ⟨5404490540405206223536201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7205987387206941631381601 5404490540405206223536201)
              ·
                refine ⟨4053367905303904667652151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5404490540405206223536201 4053367905303904667652151)
                ·
                  refine ⟨6080051857955857001478227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4053367905303904667652151 6080051857955857001478227)
                  ·
                    refine ⟨9120077786933785502217341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6080051857955857001478227 9120077786933785502217341)
                    ·
                      refine ⟨3420029170100169563331503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9120077786933785502217341 3420029170100169563331503)
                      ·
                        rfl

theorem cell23_6660483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 2, 2, 1, 1, 3].length) (baseStart_6660483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6660483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6660483 prefixEnd_6660483 := by exact prefixLift 6660483
  have htrace : WordTrace (prefixWord ++ tailWord_6660483) baseStart_6660483 baseEnd_6660483 := by
    simpa [prefixWord, tailWord_6660483, baseEnd_6660483] using wordTrace_append hprefix tailTrace_6660483
  have hstable : (prefixWord ++ tailWord_6660483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6660483).length < 2 ^ (prefixWord ++ tailWord_6660483).sum := by decide
  have hdescent : baseEnd_6660483 < baseStart_6660483 := by decide
  rcases family_descends (prefixWord ++ tailWord_6660483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6660505 : List Nat := [1, 2, 1, 2, 1, 4, 4, 1, 1, 3, 3]
def baseStart_6660505 : Nat := 118140960795 + 6660505 * 2 ^ 59
def prefixEnd_6660505 : Nat := 4983230072969 + 3 ^ 40 * 6660505 * 2
def baseEnd_6660505 : Nat := 3420040466674568477256401

theorem tailTrace_6660505 : CollatzResearch.WordTrace tailWord_6660505 prefixEnd_6660505 3420040466674568477256401 := by
  unfold tailWord_6660505
  simp only [CollatzResearch.WordTrace]
  refine ⟨242928574735135383536222969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161952383156756922357481979 242928574735135383536222969)
  ·
    refine ⟨182196431051351537652167227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242928574735135383536222969 182196431051351537652167227)
    ·
      refine ⟨273294646577027306478250841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182196431051351537652167227 273294646577027306478250841)
      ·
        refine ⟨204970984932770479858688131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 273294646577027306478250841 204970984932770479858688131)
        ·
          refine ⟨307456477399155719788032197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204970984932770479858688131 307456477399155719788032197)
          ·
            refine ⟨57648089512341697460256037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 307456477399155719788032197 57648089512341697460256037)
            ·
              refine ⟨10809016783564068273798007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57648089512341697460256037 10809016783564068273798007)
              ·
                refine ⟨16213525175346102410697011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10809016783564068273798007 16213525175346102410697011)
                ·
                  refine ⟨24320287763019153616045517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16213525175346102410697011 24320287763019153616045517)
                  ·
                    refine ⟨9120107911132182606017069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24320287763019153616045517 9120107911132182606017069)
                    ·
                      refine ⟨3420040466674568477256401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9120107911132182606017069 3420040466674568477256401)
                      ·
                        rfl

theorem cell23_6660505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 4, 1, 1, 3, 3].length) (baseStart_6660505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6660505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6660505 prefixEnd_6660505 := by exact prefixLift 6660505
  have htrace : WordTrace (prefixWord ++ tailWord_6660505) baseStart_6660505 baseEnd_6660505 := by
    simpa [prefixWord, tailWord_6660505, baseEnd_6660505] using wordTrace_append hprefix tailTrace_6660505
  have hstable : (prefixWord ++ tailWord_6660505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6660505).length < 2 ^ (prefixWord ++ tailWord_6660505).sum := by decide
  have hdescent : baseEnd_6660505 < baseStart_6660505 := by decide
  rcases family_descends (prefixWord ++ tailWord_6660505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6660556 : List Nat := [2, 2, 1, 4, 3, 1, 3, 1, 2, 1, 3]
def baseStart_6660556 : Nat := 118140960795 + 6660556 * 2 ^ 59
def prefixEnd_6660556 : Nat := 4983230072969 + 3 ^ 40 * 6660556 * 2
def baseEnd_6660556 : Nat := 3420066654187947777718667

theorem tailTrace_6660556 : CollatzResearch.WordTrace tailWord_6660556 prefixEnd_6660556 3420066654187947777718667 := by
  unfold tailWord_6660556
  simp only [CollatzResearch.WordTrace]
  refine ⟨121465217428975309623164761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161953623238633746164219681 121465217428975309623164761)
  ·
    refine ⟨91098913071731482217373571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121465217428975309623164761 91098913071731482217373571)
    ·
      refine ⟨136648369607597223326060357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91098913071731482217373571 136648369607597223326060357)
      ·
        refine ⟨25621569301424479373636317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 136648369607597223326060357 25621569301424479373636317)
        ·
          refine ⟨9608088488034179765113619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25621569301424479373636317 9608088488034179765113619)
          ·
            refine ⟨14412132732051269647670429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9608088488034179765113619 14412132732051269647670429)
            ·
              refine ⟨5404549774519226117876411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14412132732051269647670429 5404549774519226117876411)
              ·
                refine ⟨8106824661778839176814617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5404549774519226117876411 8106824661778839176814617)
                ·
                  refine ⟨6080118496334129382610963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8106824661778839176814617 6080118496334129382610963)
                  ·
                    refine ⟨9120177744501194073916445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6080118496334129382610963 9120177744501194073916445)
                    ·
                      refine ⟨3420066654187947777718667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9120177744501194073916445 3420066654187947777718667)
                      ·
                        rfl

theorem cell23_6660556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 3, 1, 2, 1, 3].length) (baseStart_6660556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6660556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6660556 prefixEnd_6660556 := by exact prefixLift 6660556
  have htrace : WordTrace (prefixWord ++ tailWord_6660556) baseStart_6660556 baseEnd_6660556 := by
    simpa [prefixWord, tailWord_6660556, baseEnd_6660556] using wordTrace_append hprefix tailTrace_6660556
  have hstable : (prefixWord ++ tailWord_6660556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6660556).length < 2 ^ (prefixWord ++ tailWord_6660556).sum := by decide
  have hdescent : baseEnd_6660556 < baseStart_6660556 := by decide
  rcases family_descends (prefixWord ++ tailWord_6660556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6660566 : List Nat := [5, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2]
def baseStart_6660566 : Nat := 118140960795 + 6660566 * 2 ^ 59
def prefixEnd_6660566 : Nat := 4983230072969 + 3 ^ 40 * 6660566 * 2
def baseEnd_6660566 : Nat := 3420071788994492738593621

theorem tailTrace_6660566 : CollatzResearch.WordTrace tailWord_6660566 prefixEnd_6660566 3420071788994492738593621 := by
  unfold tailWord_6660566
  simp only [CollatzResearch.WordTrace]
  refine ⟨15183174974244649434637097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 161953866391942927302795701 15183174974244649434637097)
  ·
    refine ⟨11387381230683487075977823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15183174974244649434637097 11387381230683487075977823)
    ·
      refine ⟨17081071846025230613966735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11387381230683487075977823 17081071846025230613966735)
      ·
        refine ⟨25621607769037845920950103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17081071846025230613966735 25621607769037845920950103)
        ·
          refine ⟨38432411653556768881425155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25621607769037845920950103 38432411653556768881425155)
          ·
            refine ⟨57648617480335153322137733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38432411653556768881425155 57648617480335153322137733)
            ·
              refine ⟨10809115777562841247900825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57648617480335153322137733 10809115777562841247900825)
              ·
                refine ⟨8106836833172130935925619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10809115777562841247900825 8106836833172130935925619)
                ·
                  refine ⟨12160255249758196403888429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8106836833172130935925619 12160255249758196403888429)
                  ·
                    refine ⟨4560095718659323651458161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12160255249758196403888429 4560095718659323651458161)
                    ·
                      refine ⟨3420071788994492738593621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4560095718659323651458161 3420071788994492738593621)
                      ·
                        rfl

theorem cell23_6660566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2].length) (baseStart_6660566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6660566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6660566 prefixEnd_6660566 := by exact prefixLift 6660566
  have htrace : WordTrace (prefixWord ++ tailWord_6660566) baseStart_6660566 baseEnd_6660566 := by
    simpa [prefixWord, tailWord_6660566, baseEnd_6660566] using wordTrace_append hprefix tailTrace_6660566
  have hstable : (prefixWord ++ tailWord_6660566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6660566).length < 2 ^ (prefixWord ++ tailWord_6660566).sum := by decide
  have hdescent : baseEnd_6660566 < baseStart_6660566 := by decide
  rcases family_descends (prefixWord ++ tailWord_6660566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6660585 : List Nat := [1, 2, 1, 1, 1, 2, 1, 9, 5]
def baseStart_6660585 : Nat := 118140960795 + 6660585 * 2 ^ 59
def prefixEnd_6660585 : Nat := 4983230072969 + 3 ^ 40 * 6660585 * 2
def baseEnd_6660585 : Nat := 380009060569658684917337

theorem tailTrace_6660585 : CollatzResearch.WordTrace tailWord_6660585 prefixEnd_6660585 380009060569658684917337 := by
  unfold tailWord_6660585
  simp only [CollatzResearch.WordTrace]
  refine ⟨242931492574845557199135209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161954328383230371466090139 242931492574845557199135209)
  ·
    refine ⟨182198619431134167899351407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242931492574845557199135209 182198619431134167899351407)
    ·
      refine ⟨273297929146701251849027111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182198619431134167899351407 273297929146701251849027111)
      ·
        refine ⟨409946893720051877773540667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273297929146701251849027111 409946893720051877773540667)
        ·
          refine ⟨614920340580077816660311001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 409946893720051877773540667 614920340580077816660311001)
          ·
            refine ⟨461190255435058362495233251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 614920340580077816660311001 461190255435058362495233251)
            ·
              refine ⟨691785383152587543742849877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 461190255435058362495233251 691785383152587543742849877)
              ·
                refine ⟨4053429979409692639118261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 691785383152587543742849877 4053429979409692639118261)
                ·
                  refine ⟨380009060569658684917337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4053429979409692639118261 380009060569658684917337)
                  ·
                    rfl

theorem cell23_6660585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 9, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 9, 5].length) (baseStart_6660585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6660585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6660585 prefixEnd_6660585 := by exact prefixLift 6660585
  have htrace : WordTrace (prefixWord ++ tailWord_6660585) baseStart_6660585 baseEnd_6660585 := by
    simpa [prefixWord, tailWord_6660585, baseEnd_6660585] using wordTrace_append hprefix tailTrace_6660585
  have hstable : (prefixWord ++ tailWord_6660585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6660585).length < 2 ^ (prefixWord ++ tailWord_6660585).sum := by decide
  have hdescent : baseEnd_6660585 < baseStart_6660585 := by decide
  rcases family_descends (prefixWord ++ tailWord_6660585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6660632 : List Nat := [2, 1, 2, 3, 3, 2, 2, 1, 2, 5]
def baseStart_6660632 : Nat := 118140960795 + 6660632 * 2 ^ 59
def prefixEnd_6660632 : Nat := 4983230072969 + 3 ^ 40 * 6660632 * 2
def baseEnd_6660632 : Nat := 1140035226239229826789439

theorem tailTrace_6660632 : CollatzResearch.WordTrace tailWord_6660632 prefixEnd_6660632 1140035226239229826789439 := by
  unfold tailWord_6660632
  simp only [CollatzResearch.WordTrace]
  refine ⟨121466603402837642113048075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161955471203783522817397433 121466603402837642113048075)
  ·
    refine ⟨182199905104256463169572113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121466603402837642113048075 182199905104256463169572113)
    ·
      refine ⟨136649928828192347377179085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182199905104256463169572113 136649928828192347377179085)
      ·
        refine ⟨51243723310572130266442157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136649928828192347377179085 51243723310572130266442157)
        ·
          refine ⟨19216396241464548849915809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51243723310572130266442157 19216396241464548849915809)
          ·
            refine ⟨14412297181098411637436857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19216396241464548849915809 14412297181098411637436857)
            ·
              refine ⟨10809222885823808728077643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14412297181098411637436857 10809222885823808728077643)
              ·
                refine ⟨16213834328735713092116465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10809222885823808728077643 16213834328735713092116465)
                ·
                  refine ⟨12160375746551784819087349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16213834328735713092116465 12160375746551784819087349)
                  ·
                    refine ⟨1140035226239229826789439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12160375746551784819087349 1140035226239229826789439)
                    ·
                      rfl

theorem cell23_6660632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 2, 1, 2, 5].length) (baseStart_6660632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6660632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6660632 prefixEnd_6660632 := by exact prefixLift 6660632
  have htrace : WordTrace (prefixWord ++ tailWord_6660632) baseStart_6660632 baseEnd_6660632 := by
    simpa [prefixWord, tailWord_6660632, baseEnd_6660632] using wordTrace_append hprefix tailTrace_6660632
  have hstable : (prefixWord ++ tailWord_6660632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6660632).length < 2 ^ (prefixWord ++ tailWord_6660632).sum := by decide
  have hdescent : baseEnd_6660632 < baseStart_6660632 := by decide
  rcases family_descends (prefixWord ++ tailWord_6660632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6660653 : List Nat := [1, 5, 4, 1, 1, 1, 1, 4, 5]
def baseStart_6660653 : Nat := 118140960795 + 6660653 * 2 ^ 59
def prefixEnd_6660653 : Nat := 4983230072969 + 3 ^ 40 * 6660653 * 2
def baseEnd_6660653 : Nat := 380012940201270433133969

theorem tailTrace_6660653 : CollatzResearch.WordTrace tailWord_6660653 prefixEnd_6660653 380012940201270433133969 := by
  unfold tailWord_6660653
  simp only [CollatzResearch.WordTrace]
  refine ⟨242933972738599204812610613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161955981825732803208407075 242933972738599204812610613)
  ·
    refine ⟨22775059944243675451182245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 242933972738599204812610613 22775059944243675451182245)
    ·
      refine ⟨4270323739545689147096671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22775059944243675451182245 4270323739545689147096671)
      ·
        refine ⟨6405485609318533720645007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4270323739545689147096671 6405485609318533720645007)
        ·
          refine ⟨9608228413977800580967511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6405485609318533720645007 9608228413977800580967511)
          ·
            refine ⟨14412342620966700871451267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9608228413977800580967511 14412342620966700871451267)
            ·
              refine ⟨21618513931450051307176901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14412342620966700871451267 21618513931450051307176901)
              ·
                refine ⟨4053471362146884620095669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21618513931450051307176901 4053471362146884620095669)
                ·
                  refine ⟨380012940201270433133969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4053471362146884620095669 380012940201270433133969)
                  ·
                    rfl

theorem cell23_6660653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 4, 5].length) (baseStart_6660653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6660653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6660653 prefixEnd_6660653 := by exact prefixLift 6660653
  have htrace : WordTrace (prefixWord ++ tailWord_6660653) baseStart_6660653 baseEnd_6660653 := by
    simpa [prefixWord, tailWord_6660653, baseEnd_6660653] using wordTrace_append hprefix tailTrace_6660653
  have hstable : (prefixWord ++ tailWord_6660653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6660653).length < 2 ^ (prefixWord ++ tailWord_6660653).sum := by decide
  have hdescent : baseEnd_6660653 < baseStart_6660653 := by decide
  rcases family_descends (prefixWord ++ tailWord_6660653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6660669 : List Nat := [1, 4, 1, 3, 2, 2, 1, 1, 2, 4, 2]
def baseStart_6660669 : Nat := 118140960795 + 6660669 * 2 ^ 59
def prefixEnd_6660669 : Nat := 4983230072969 + 3 ^ 40 * 6660669 * 2
def baseEnd_6660669 : Nat := 3420124677501905835605647

theorem tailTrace_6660669 : CollatzResearch.WordTrace tailWord_6660669 prefixEnd_6660669 3420124677501905835605647 := by
  unfold tailWord_6660669
  simp only [CollatzResearch.WordTrace]
  refine ⟨242934556306541239545193061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161956370871027493030128707 242934556306541239545193061)
  ·
    refine ⟨45550229307476482414723699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 242934556306541239545193061 45550229307476482414723699)
    ·
      refine ⟨68325343961214723622085549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45550229307476482414723699 68325343961214723622085549)
      ·
        refine ⟨25622003985455521358282081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68325343961214723622085549 25622003985455521358282081)
        ·
          refine ⟨19216502989091641018711561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25622003985455521358282081 19216502989091641018711561)
          ·
            refine ⟨14412377241818730764033671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19216502989091641018711561 14412377241818730764033671)
            ·
              refine ⟨21618565862728096146050507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14412377241818730764033671 21618565862728096146050507)
              ·
                refine ⟨32427848794092144219075761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21618565862728096146050507 32427848794092144219075761)
                ·
                  refine ⟨24320886595569108164306821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32427848794092144219075761 24320886595569108164306821)
                  ·
                    refine ⟨4560166236669207780807529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24320886595569108164306821 4560166236669207780807529)
                    ·
                      refine ⟨3420124677501905835605647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4560166236669207780807529 3420124677501905835605647)
                      ·
                        rfl

theorem cell23_6660669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 1, 2, 4, 2].length) (baseStart_6660669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6660669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6660669 prefixEnd_6660669 := by exact prefixLift 6660669
  have htrace : WordTrace (prefixWord ++ tailWord_6660669) baseStart_6660669 baseEnd_6660669 := by
    simpa [prefixWord, tailWord_6660669, baseEnd_6660669] using wordTrace_append hprefix tailTrace_6660669
  have hstable : (prefixWord ++ tailWord_6660669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6660669).length < 2 ^ (prefixWord ++ tailWord_6660669).sum := by decide
  have hdescent : baseEnd_6660669 < baseStart_6660669 := by decide
  rcases family_descends (prefixWord ++ tailWord_6660669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6660689 : List Nat := [1, 2, 2, 1, 3, 5, 1, 1, 2, 2, 3]
def baseStart_6660689 : Nat := 118140960795 + 6660689 * 2 ^ 59
def prefixEnd_6660689 : Nat := 4983230072969 + 3 ^ 40 * 6660689 * 2
def baseEnd_6660689 : Nat := 3420134947114995757355555

theorem tailTrace_6660689 : CollatzResearch.WordTrace tailWord_6660689 prefixEnd_6660689 3420134947114995757355555 := by
  unfold tailWord_6660689
  simp only [CollatzResearch.WordTrace]
  refine ⟨242935285766468782960921121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161956857177645855307280747 242935285766468782960921121)
  ·
    refine ⟨182201464324851587220690841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242935285766468782960921121 182201464324851587220690841)
    ·
      refine ⟨136651098243638690415518131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182201464324851587220690841 136651098243638690415518131)
      ·
        refine ⟨204976647365458035623277197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136651098243638690415518131 204976647365458035623277197)
        ·
          refine ⟨76866242762046763358728949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 204976647365458035623277197 76866242762046763358728949)
          ·
            refine ⟨7206210258941884064880839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 76866242762046763358728949 7206210258941884064880839)
            ·
              refine ⟨10809315388412826097321259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7206210258941884064880839 10809315388412826097321259)
              ·
                refine ⟨16213973082619239145981889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10809315388412826097321259 16213973082619239145981889)
                ·
                  refine ⟨12160479811964429359486417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16213973082619239145981889 12160479811964429359486417)
                  ·
                    refine ⟨9120359858973322019614813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12160479811964429359486417 9120359858973322019614813)
                    ·
                      refine ⟨3420134947114995757355555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9120359858973322019614813 3420134947114995757355555)
                      ·
                        rfl

theorem cell23_6660689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 1, 1, 2, 2, 3].length) (baseStart_6660689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6660689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6660689 prefixEnd_6660689 := by exact prefixLift 6660689
  have htrace : WordTrace (prefixWord ++ tailWord_6660689) baseStart_6660689 baseEnd_6660689 := by
    simpa [prefixWord, tailWord_6660689, baseEnd_6660689] using wordTrace_append hprefix tailTrace_6660689
  have hstable : (prefixWord ++ tailWord_6660689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6660689).length < 2 ^ (prefixWord ++ tailWord_6660689).sum := by decide
  have hdescent : baseEnd_6660689 < baseStart_6660689 := by decide
  rcases family_descends (prefixWord ++ tailWord_6660689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6660709 : List Nat := [1, 3, 1, 3, 4, 2, 1, 2, 6]
def baseStart_6660709 : Nat := 118140960795 + 6660709 * 2 ^ 59
def prefixEnd_6660709 : Nat := 4983230072969 + 3 ^ 40 * 6660709 * 2
def baseEnd_6660709 : Nat := 380016135192009519900607

theorem tailTrace_6660709 : CollatzResearch.WordTrace tailWord_6660709 prefixEnd_6660709 380016135192009519900607 := by
  unfold tailWord_6660709
  simp only [CollatzResearch.WordTrace]
  refine ⟨242936015226396326376649181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161957343484264217584432787 242936015226396326376649181)
  ·
    refine ⟨91101005709898622391243443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 242936015226396326376649181 91101005709898622391243443)
    ·
      refine ⟨136651508564847933586865165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91101005709898622391243443 136651508564847933586865165)
      ·
        refine ⟨51244315711817975095074437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136651508564847933586865165 51244315711817975095074437)
        ·
          refine ⟨9608309195965870330326457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51244315711817975095074437 9608309195965870330326457)
          ·
            refine ⟨7206231896974402747744843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9608309195965870330326457 7206231896974402747744843)
            ·
              refine ⟨10809347845461604121617265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7206231896974402747744843 10809347845461604121617265)
              ·
                refine ⟨8107010884096203091212949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10809347845461604121617265 8107010884096203091212949)
                ·
                  refine ⟨380016135192009519900607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8107010884096203091212949 380016135192009519900607)
                  ·
                    rfl

theorem cell23_6660709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 1, 2, 6].length) (baseStart_6660709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6660709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6660709 prefixEnd_6660709 := by exact prefixLift 6660709
  have htrace : WordTrace (prefixWord ++ tailWord_6660709) baseStart_6660709 baseEnd_6660709 := by
    simpa [prefixWord, tailWord_6660709, baseEnd_6660709] using wordTrace_append hprefix tailTrace_6660709
  have hstable : (prefixWord ++ tailWord_6660709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6660709).length < 2 ^ (prefixWord ++ tailWord_6660709).sum := by decide
  have hdescent : baseEnd_6660709 < baseStart_6660709 := by decide
  rcases family_descends (prefixWord ++ tailWord_6660709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6660726 : List Nat := [5, 1, 1, 2, 3, 1, 3, 1, 6]
def baseStart_6660726 : Nat := 118140960795 + 6660726 * 2 ^ 59
def prefixEnd_6660726 : Nat := 4983230072969 + 3 ^ 40 * 6660726 * 2
def baseEnd_6660726 : Nat := 380017105099912456954765

theorem tailTrace_6660726 : CollatzResearch.WordTrace tailWord_6660726 prefixEnd_6660726 380017105099912456954765 := by
  unfold tailWord_6660726
  simp only [CollatzResearch.WordTrace]
  refine ⟨15183539704208421142501127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 161957756844889825520012021 15183539704208421142501127)
  ·
    refine ⟨22775309556312631713751691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15183539704208421142501127 22775309556312631713751691)
    ·
      refine ⟨34162964334468947570627537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22775309556312631713751691 34162964334468947570627537)
      ·
        refine ⟨25622223250851710677970653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34162964334468947570627537 25622223250851710677970653)
        ·
          refine ⟨9608333719069391504238995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25622223250851710677970653 9608333719069391504238995)
          ·
            refine ⟨14412500578604087256358493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9608333719069391504238995 14412500578604087256358493)
            ·
              refine ⟨5404687716976532721134435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14412500578604087256358493 5404687716976532721134435)
              ·
                refine ⟨8107031575464799081701653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5404687716976532721134435 8107031575464799081701653)
                ·
                  refine ⟨380017105099912456954765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8107031575464799081701653 380017105099912456954765)
                  ·
                    rfl

theorem cell23_6660726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 3, 1, 6].length) (baseStart_6660726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6660726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6660726 prefixEnd_6660726 := by exact prefixLift 6660726
  have htrace : WordTrace (prefixWord ++ tailWord_6660726) baseStart_6660726 baseEnd_6660726 := by
    simpa [prefixWord, tailWord_6660726, baseEnd_6660726] using wordTrace_append hprefix tailTrace_6660726
  have hstable : (prefixWord ++ tailWord_6660726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6660726).length < 2 ^ (prefixWord ++ tailWord_6660726).sum := by decide
  have hdescent : baseEnd_6660726 < baseStart_6660726 := by decide
  rcases family_descends (prefixWord ++ tailWord_6660726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6660735 : List Nat := [1, 1, 2, 2, 1, 1, 1, 7, 1, 6]
def baseStart_6660735 : Nat := 118140960795 + 6660735 * 2 ^ 59
def prefixEnd_6660735 : Nat := 4983230072969 + 3 ^ 40 * 6660735 * 2
def baseEnd_6660735 : Nat := 1140052855741700859126781

theorem tailTrace_6660735 : CollatzResearch.WordTrace tailWord_6660735 prefixEnd_6660735 1140052855741700859126781 := by
  unfold tailWord_6660735
  simp only [CollatzResearch.WordTrace]
  refine ⟨242936963524302132817095659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161957975682868088544730439 242936963524302132817095659)
  ·
    refine ⟨364405445286453199225643489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242936963524302132817095659 364405445286453199225643489)
    ·
      refine ⟨273304083964839899419232617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 364405445286453199225643489 273304083964839899419232617)
      ·
        refine ⟨204978062973629924564424463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 273304083964839899419232617 204978062973629924564424463)
        ·
          refine ⟨307467094460444886846636695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204978062973629924564424463 307467094460444886846636695)
          ·
            refine ⟨461200641690667330269955043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 307467094460444886846636695 461200641690667330269955043)
            ·
              refine ⟨691800962536000995404932565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 461200641690667330269955043 691800962536000995404932565)
              ·
                refine ⟨16214085059437523329803107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 691800962536000995404932565 16214085059437523329803107)
                ·
                  refine ⟨24321127589156284994704661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16214085059437523329803107 24321127589156284994704661)
                  ·
                    refine ⟨1140052855741700859126781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24321127589156284994704661 1140052855741700859126781)
                    ·
                      rfl

theorem cell23_6660735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 7, 1, 6].length) (baseStart_6660735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6660735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6660735 prefixEnd_6660735 := by exact prefixLift 6660735
  have htrace : WordTrace (prefixWord ++ tailWord_6660735) baseStart_6660735 baseEnd_6660735 := by
    simpa [prefixWord, tailWord_6660735, baseEnd_6660735] using wordTrace_append hprefix tailTrace_6660735
  have hstable : (prefixWord ++ tailWord_6660735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6660735).length < 2 ^ (prefixWord ++ tailWord_6660735).sum := by decide
  have hdescent : baseEnd_6660735 < baseStart_6660735 := by decide
  rcases family_descends (prefixWord ++ tailWord_6660735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6660745 : List Nat := [1, 2, 1, 1, 4, 1, 1, 1, 5, 1, 5]
def baseStart_6660745 : Nat := 118140960795 + 6660745 * 2 ^ 59
def prefixEnd_6660745 : Nat := 4983230072969 + 3 ^ 40 * 6660745 * 2
def baseEnd_6660745 : Nat := 3420163702031647538255297

theorem tailTrace_6660745 : CollatzResearch.WordTrace tailWord_6660745 prefixEnd_6660745 3420163702031647538255297 := by
  unfold tailWord_6660745
  simp only [CollatzResearch.WordTrace]
  refine ⟨242937328254265904524959689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161958218836177269683306459 242937328254265904524959689)
  ·
    refine ⟨182202996190699428393719767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242937328254265904524959689 182202996190699428393719767)
    ·
      refine ⟨273304494286049142590579651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182202996190699428393719767 273304494286049142590579651)
      ·
        refine ⟨409956741429073713885869477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273304494286049142590579651 409956741429073713885869477)
        ·
          refine ⟨76866889017951321353600527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 409956741429073713885869477 76866889017951321353600527)
          ·
            refine ⟨115300333526926982030400791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76866889017951321353600527 115300333526926982030400791)
            ·
              refine ⟨172950500290390473045601187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115300333526926982030400791 172950500290390473045601187)
              ·
                refine ⟨259425750435585709568401781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 172950500290390473045601187 259425750435585709568401781)
                ·
                  refine ⟨24321164103336160272037667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 259425750435585709568401781 24321164103336160272037667)
                  ·
                    refine ⟨36481746155004240408056501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24321164103336160272037667 36481746155004240408056501)
                    ·
                      refine ⟨3420163702031647538255297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36481746155004240408056501 3420163702031647538255297)
                      ·
                        rfl

theorem cell23_6660745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 5, 1, 5].length) (baseStart_6660745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6660745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6660745 prefixEnd_6660745 := by exact prefixLift 6660745
  have htrace : WordTrace (prefixWord ++ tailWord_6660745) baseStart_6660745 baseEnd_6660745 := by
    simpa [prefixWord, tailWord_6660745, baseEnd_6660745] using wordTrace_append hprefix tailTrace_6660745
  have hstable : (prefixWord ++ tailWord_6660745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6660745).length < 2 ^ (prefixWord ++ tailWord_6660745).sum := by decide
  have hdescent : baseEnd_6660745 < baseStart_6660745 := by decide
  rcases family_descends (prefixWord ++ tailWord_6660745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6660765 : List Nat := [1, 4, 2, 1, 1, 1, 13]
def baseStart_6660765 : Nat := 118140960795 + 6660765 * 2 ^ 59
def prefixEnd_6660765 : Nat := 4983230072969 + 3 ^ 40 * 6660765 * 2
def baseEnd_6660765 : Nat := 42224370020305400740805

theorem tailTrace_6660765 : CollatzResearch.WordTrace tailWord_6660765 prefixEnd_6660765 42224370020305400740805 := by
  unfold tailWord_6660765
  simp only [CollatzResearch.WordTrace]
  refine ⟨242938057714193447940687749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161958705142795631960458499 242938057714193447940687749)
  ·
    refine ⟨45550885821411271488878953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 242938057714193447940687749 45550885821411271488878953)
    ·
      refine ⟨34163164366058453616659215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45550885821411271488878953 34163164366058453616659215)
      ·
        refine ⟨51244746549087680424988823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34163164366058453616659215 51244746549087680424988823)
        ·
          refine ⟨76867119823631520637483235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51244746549087680424988823 76867119823631520637483235)
          ·
            refine ⟨115300679735447280956224853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76867119823631520637483235 115300679735447280956224853)
            ·
              refine ⟨42224370020305400740805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 115300679735447280956224853 42224370020305400740805)
              ·
                rfl

theorem cell23_6660765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 13].length) (baseStart_6660765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6660765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6660765 prefixEnd_6660765 := by exact prefixLift 6660765
  have htrace : WordTrace (prefixWord ++ tailWord_6660765) baseStart_6660765 baseEnd_6660765 := by
    simpa [prefixWord, tailWord_6660765, baseEnd_6660765] using wordTrace_append hprefix tailTrace_6660765
  have hstable : (prefixWord ++ tailWord_6660765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6660765).length < 2 ^ (prefixWord ++ tailWord_6660765).sum := by decide
  have hdescent : baseEnd_6660765 < baseStart_6660765 := by decide
  rcases family_descends (prefixWord ++ tailWord_6660765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6660790 : List Nat := [5, 1, 3, 1, 3, 1, 1, 2, 1, 5]
def baseStart_6660790 : Nat := 118140960795 + 6660790 * 2 ^ 59
def prefixEnd_6660790 : Nat := 4983230072969 + 3 ^ 40 * 6660790 * 2
def baseEnd_6660790 : Nat := 1140062269553699954064197

theorem tailTrace_6660790 : CollatzResearch.WordTrace tailWord_6660790 prefixEnd_6660790 1140062269553699954064197 := by
  unfold tailWord_6660790
  simp only [CollatzResearch.WordTrace]
  refine ⟨15183685596193929825646739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 161959313026068584806898549 15183685596193929825646739)
  ·
    refine ⟨22775528394290894738470109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15183685596193929825646739 22775528394290894738470109)
    ·
      refine ⟨8540823147859085526926291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22775528394290894738470109 8540823147859085526926291)
      ·
        refine ⟨12811234721788628290389437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8540823147859085526926291 12811234721788628290389437)
        ·
          refine ⟨4804213020670735608896039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12811234721788628290389437 4804213020670735608896039)
          ·
            refine ⟨7206319531006103413344059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4804213020670735608896039 7206319531006103413344059)
            ·
              refine ⟨10809479296509155120016089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7206319531006103413344059 10809479296509155120016089)
              ·
                refine ⟨8107109472381866340012067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10809479296509155120016089 8107109472381866340012067)
                ·
                  refine ⟨12160664208572799510018101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8107109472381866340012067 12160664208572799510018101)
                  ·
                    refine ⟨1140062269553699954064197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12160664208572799510018101 1140062269553699954064197)
                    ·
                      rfl

theorem cell23_6660790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_6660790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6660790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6660790 prefixEnd_6660790 := by exact prefixLift 6660790
  have htrace : WordTrace (prefixWord ++ tailWord_6660790) baseStart_6660790 baseEnd_6660790 := by
    simpa [prefixWord, tailWord_6660790, baseEnd_6660790] using wordTrace_append hprefix tailTrace_6660790
  have hstable : (prefixWord ++ tailWord_6660790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6660790).length < 2 ^ (prefixWord ++ tailWord_6660790).sum := by decide
  have hdescent : baseEnd_6660790 < baseStart_6660790 := by decide
  rcases family_descends (prefixWord ++ tailWord_6660790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6660813 : List Nat := [1, 6, 2, 1, 2, 2, 1, 1, 1, 1, 5]
def baseStart_6660813 : Nat := 118140960795 + 6660813 * 2 ^ 59
def prefixEnd_6660813 : Nat := 4983230072969 + 3 ^ 40 * 6660813 * 2
def baseEnd_6660813 : Nat := 3420198618716153272204985

theorem tailTrace_6660813 : CollatzResearch.WordTrace tailWord_6660813 prefixEnd_6660813 3420198618716153272204985 := by
  unfold tailWord_6660813
  simp only [CollatzResearch.WordTrace]
  refine ⟨242939808418019552138435093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161959872278679701425623395 242939808418019552138435093)
  ·
    refine ⟨11387803519594666506489145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 242939808418019552138435093 11387803519594666506489145)
    ·
      refine ⟨8540852639695999879866859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11387803519594666506489145 8540852639695999879866859)
      ·
        refine ⟨12811278959543999819800289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8540852639695999879866859 12811278959543999819800289)
        ·
          refine ⟨9608459219657999864850217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12811278959543999819800289 9608459219657999864850217)
          ·
            refine ⟨7206344414743499898637663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9608459219657999864850217 7206344414743499898637663)
            ·
              refine ⟨10809516622115249847956495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7206344414743499898637663 10809516622115249847956495)
              ·
                refine ⟨16214274933172874771934743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10809516622115249847956495 16214274933172874771934743)
                ·
                  refine ⟨24321412399759312157902115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16214274933172874771934743 24321412399759312157902115)
                  ·
                    refine ⟨36482118599638968236853173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24321412399759312157902115 36482118599638968236853173)
                    ·
                      refine ⟨3420198618716153272204985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36482118599638968236853173 3420198618716153272204985)
                      ·
                        rfl

theorem cell23_6660813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_6660813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6660813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6660813 prefixEnd_6660813 := by exact prefixLift 6660813
  have htrace : WordTrace (prefixWord ++ tailWord_6660813) baseStart_6660813 baseEnd_6660813 := by
    simpa [prefixWord, tailWord_6660813, baseEnd_6660813] using wordTrace_append hprefix tailTrace_6660813
  have hstable : (prefixWord ++ tailWord_6660813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6660813).length < 2 ^ (prefixWord ++ tailWord_6660813).sum := by decide
  have hdescent : baseEnd_6660813 < baseStart_6660813 := by decide
  rcases family_descends (prefixWord ++ tailWord_6660813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6660826 : List Nat := [3, 1, 1, 2, 2, 2, 4, 2, 2, 1, 3]
def baseStart_6660826 : Nat := 118140960795 + 6660826 * 2 ^ 59
def prefixEnd_6660826 : Nat := 4983230072969 + 3 ^ 40 * 6660826 * 2
def baseEnd_6660826 : Nat := 3420205293964661721342425

theorem tailTrace_6660826 : CollatzResearch.WordTrace tailWord_6660826 prefixEnd_6660826 3420205293964661721342425 := by
  unfold tailWord_6660826
  simp only [CollatzResearch.WordTrace]
  refine ⟨60735070641743113839664583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161960188377981636905772221 60735070641743113839664583)
  ·
    refine ⟨91102605962614670759496875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60735070641743113839664583 91102605962614670759496875)
    ·
      refine ⟨136653908943922006139245313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91102605962614670759496875 136653908943922006139245313)
      ·
        refine ⟨102490431707941504604433985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136653908943922006139245313 102490431707941504604433985)
        ·
          refine ⟨76867823780956128453325489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102490431707941504604433985 76867823780956128453325489)
          ·
            refine ⟨57650867835717096339994117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76867823780956128453325489 57650867835717096339994117)
            ·
              refine ⟨10809537719196955563748897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57650867835717096339994117 10809537719196955563748897)
              ·
                refine ⟨8107153289397716672811673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10809537719196955563748897 8107153289397716672811673)
                ·
                  refine ⟨6080364967048287504608755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8107153289397716672811673 6080364967048287504608755)
                  ·
                    refine ⟨9120547450572431256913133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6080364967048287504608755 9120547450572431256913133)
                    ·
                      refine ⟨3420205293964661721342425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9120547450572431256913133 3420205293964661721342425)
                      ·
                        rfl

theorem cell23_6660826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 4, 2, 2, 1, 3].length) (baseStart_6660826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6660826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6660826 prefixEnd_6660826 := by exact prefixLift 6660826
  have htrace : WordTrace (prefixWord ++ tailWord_6660826) baseStart_6660826 baseEnd_6660826 := by
    simpa [prefixWord, tailWord_6660826, baseEnd_6660826] using wordTrace_append hprefix tailTrace_6660826
  have hstable : (prefixWord ++ tailWord_6660826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6660826).length < 2 ^ (prefixWord ++ tailWord_6660826).sum := by decide
  have hdescent : baseEnd_6660826 < baseStart_6660826 := by decide
  rcases family_descends (prefixWord ++ tailWord_6660826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6660900 : List Nat := [2, 3, 1, 3, 4, 1, 1, 1, 1, 4, 2]
def baseStart_6660900 : Nat := 118140960795 + 6660900 * 2 ^ 59
def prefixEnd_6660900 : Nat := 4983230072969 + 3 ^ 40 * 6660900 * 2
def baseEnd_6660900 : Nat := 3420243291533094431817085

theorem tailTrace_6660900 : CollatzResearch.WordTrace tailWord_6660900 prefixEnd_6660900 3420243291533094431817085 := by
  unfold tailWord_6660900
  simp only [CollatzResearch.WordTrace]
  refine ⟨121471490784352182998426077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161961987712469577331234769 121471490784352182998426077)
  ·
    refine ⟨45551809044132068624409779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121471490784352182998426077 45551809044132068624409779)
    ·
      refine ⟨68327713566198102936614669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45551809044132068624409779 68327713566198102936614669)
      ·
        refine ⟨25622892587324288601230501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68327713566198102936614669 25622892587324288601230501)
        ·
          refine ⟨4804292360123304112730719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25622892587324288601230501 4804292360123304112730719)
          ·
            refine ⟨7206438540184956169096079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4804292360123304112730719 7206438540184956169096079)
            ·
              refine ⟨10809657810277434253644119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7206438540184956169096079 10809657810277434253644119)
              ·
                refine ⟨16214486715416151380466179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10809657810277434253644119 16214486715416151380466179)
                ·
                  refine ⟨24321730073124227070699269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16214486715416151380466179 24321730073124227070699269)
                  ·
                    refine ⟨4560324388710792575756113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24321730073124227070699269 4560324388710792575756113)
                    ·
                      refine ⟨3420243291533094431817085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4560324388710792575756113 3420243291533094431817085)
                      ·
                        rfl

theorem cell23_6660900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 1, 1, 1, 4, 2].length) (baseStart_6660900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6660900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6660900 prefixEnd_6660900 := by exact prefixLift 6660900
  have htrace : WordTrace (prefixWord ++ tailWord_6660900) baseStart_6660900 baseEnd_6660900 := by
    simpa [prefixWord, tailWord_6660900, baseEnd_6660900] using wordTrace_append hprefix tailTrace_6660900
  have hstable : (prefixWord ++ tailWord_6660900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6660900).length < 2 ^ (prefixWord ++ tailWord_6660900).sum := by decide
  have hdescent : baseEnd_6660900 < baseStart_6660900 := by decide
  rcases family_descends (prefixWord ++ tailWord_6660900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6660952 : List Nat := [2, 1, 2, 2, 1, 1, 1, 4, 2, 1, 6]
def baseStart_6660952 : Nat := 118140960795 + 6660952 * 2 ^ 59
def prefixEnd_6660952 : Nat := 4983230072969 + 3 ^ 40 * 6660952 * 2
def baseEnd_6660952 : Nat := 3420269992527128228366845

theorem tailTrace_6660952 : CollatzResearch.WordTrace tailWord_6660952 prefixEnd_6660952 3420269992527128228366845 := by
  unfold tailWord_6660952
  simp only [CollatzResearch.WordTrace]
  refine ⟨121472439082257989438872555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161963252109677319251830073 121472439082257989438872555)
  ·
    refine ⟨182208658623386984158308833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121472439082257989438872555 182208658623386984158308833)
    ·
      refine ⟨136656493967540238118731625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182208658623386984158308833 136656493967540238118731625)
      ·
        refine ⟨102492370475655178589048719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136656493967540238118731625 102492370475655178589048719)
        ·
          refine ⟨153738555713482767883573079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102492370475655178589048719 153738555713482767883573079)
          ·
            refine ⟨230607833570224151825359619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153738555713482767883573079 230607833570224151825359619)
            ·
              refine ⟨345911750355336227738039429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 230607833570224151825359619 345911750355336227738039429)
              ·
                refine ⟨64858453191625542700882393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 345911750355336227738039429 64858453191625542700882393)
                ·
                  refine ⟨48643839893719157025661795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64858453191625542700882393 48643839893719157025661795)
                  ·
                    refine ⟨72965759840578735538492693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48643839893719157025661795 72965759840578735538492693)
                    ·
                      refine ⟨3420269992527128228366845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72965759840578735538492693 3420269992527128228366845)
                      ·
                        rfl

theorem cell23_6660952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 4, 2, 1, 6].length) (baseStart_6660952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6660952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6660952 prefixEnd_6660952 := by exact prefixLift 6660952
  have htrace : WordTrace (prefixWord ++ tailWord_6660952) baseStart_6660952 baseEnd_6660952 := by
    simpa [prefixWord, tailWord_6660952, baseEnd_6660952] using wordTrace_append hprefix tailTrace_6660952
  have hstable : (prefixWord ++ tailWord_6660952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6660952).length < 2 ^ (prefixWord ++ tailWord_6660952).sum := by decide
  have hdescent : baseEnd_6660952 < baseStart_6660952 := by decide
  rcases family_descends (prefixWord ++ tailWord_6660952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6660959 : List Nat := [1, 1, 2, 3, 1, 3, 1, 2, 4, 2, 3]
def baseStart_6660959 : Nat := 118140960795 + 6660959 * 2 ^ 59
def prefixEnd_6660959 : Nat := 4983230072969 + 3 ^ 40 * 6660959 * 2
def baseEnd_6660959 : Nat := 3420273586891709700979313

theorem tailTrace_6660959 : CollatzResearch.WordTrace tailWord_6660959 prefixEnd_6660959 3420273586891709700979313 := by
  unfold tailWord_6660959
  simp only [CollatzResearch.WordTrace]
  refine ⟨242945133475490619073249931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161963422316993746048833287 242945133475490619073249931)
  ·
    refine ⟨364417700213235928609874897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242945133475490619073249931 364417700213235928609874897)
    ·
      refine ⟨273313275159926946457406173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 364417700213235928609874897 273313275159926946457406173)
      ·
        refine ⟨102492478184972604921527315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 273313275159926946457406173 102492478184972604921527315)
        ·
          refine ⟨153738717277458907382290973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102492478184972604921527315 153738717277458907382290973)
          ·
            refine ⟨57652018979047090268359115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 153738717277458907382290973 57652018979047090268359115)
            ·
              refine ⟨86478028468570635402538673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57652018979047090268359115 86478028468570635402538673)
              ·
                refine ⟨64858521351427976551904005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86478028468570635402538673 64858521351427976551904005)
                ·
                  refine ⟨12160972753392745603482001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64858521351427976551904005 12160972753392745603482001)
                  ·
                    refine ⟨9120729565044559202611501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12160972753392745603482001 9120729565044559202611501)
                    ·
                      refine ⟨3420273586891709700979313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9120729565044559202611501 3420273586891709700979313)
                      ·
                        rfl

theorem cell23_6660959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 2, 4, 2, 3].length) (baseStart_6660959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6660959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6660959 prefixEnd_6660959 := by exact prefixLift 6660959
  have htrace : WordTrace (prefixWord ++ tailWord_6660959) baseStart_6660959 baseEnd_6660959 := by
    simpa [prefixWord, tailWord_6660959, baseEnd_6660959] using wordTrace_append hprefix tailTrace_6660959
  have hstable : (prefixWord ++ tailWord_6660959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6660959).length < 2 ^ (prefixWord ++ tailWord_6660959).sum := by decide
  have hdescent : baseEnd_6660959 < baseStart_6660959 := by decide
  rcases family_descends (prefixWord ++ tailWord_6660959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6661000 : List Nat := [2, 1, 3, 3, 2, 1, 4, 2, 1, 4]
def baseStart_6661000 : Nat := 118140960795 + 6661000 * 2 ^ 59
def prefixEnd_6661000 : Nat := 4983230072969 + 3 ^ 40 * 6661000 * 2
def baseEnd_6661000 : Nat := 1140098213199514680188875

theorem tailTrace_6661000 : CollatzResearch.WordTrace tailWord_6661000 prefixEnd_6661000 1140098213199514680188875 := by
  unfold tailWord_6661000
  simp only [CollatzResearch.WordTrace]
  refine ⟨121473314434171041537746227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161964419245561388716994969 121473314434171041537746227)
  ·
    refine ⟨182209971651256562306619341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121473314434171041537746227 182209971651256562306619341)
    ·
      refine ⟨68328739369221210864982253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182209971651256562306619341 68328739369221210864982253)
      ·
        refine ⟨25623277263457954074368345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68328739369221210864982253 25623277263457954074368345)
        ·
          refine ⟨19217457947593465555776259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25623277263457954074368345 19217457947593465555776259)
          ·
            refine ⟨28826186921390198333664389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19217457947593465555776259 28826186921390198333664389)
            ·
              refine ⟨5404910047760662187562073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28826186921390198333664389 5404910047760662187562073)
              ·
                refine ⟨4053682535820496640671555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5404910047760662187562073 4053682535820496640671555)
                ·
                  refine ⟨6080523803730744961007333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4053682535820496640671555 6080523803730744961007333)
                  ·
                    refine ⟨1140098213199514680188875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6080523803730744961007333 1140098213199514680188875)
                    ·
                      rfl

theorem cell23_6661000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 4, 2, 1, 4].length) (baseStart_6661000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6661000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6661000 prefixEnd_6661000 := by exact prefixLift 6661000
  have htrace : WordTrace (prefixWord ++ tailWord_6661000) baseStart_6661000 baseEnd_6661000 := by
    simpa [prefixWord, tailWord_6661000, baseEnd_6661000] using wordTrace_append hprefix tailTrace_6661000
  have hstable : (prefixWord ++ tailWord_6661000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6661000).length < 2 ^ (prefixWord ++ tailWord_6661000).sum := by decide
  have hdescent : baseEnd_6661000 < baseStart_6661000 := by decide
  rcases family_descends (prefixWord ++ tailWord_6661000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6661023 : List Nat := [1, 1, 2, 5, 2, 2, 1, 2, 3, 1, 3]
def baseStart_6661023 : Nat := 118140960795 + 6661023 * 2 ^ 59
def prefixEnd_6661023 : Nat := 4983230072969 + 3 ^ 40 * 6661023 * 2
def baseEnd_6661023 : Nat := 3420306449653597450579019

theorem tailTrace_6661023 : CollatzResearch.WordTrace tailWord_6661023 prefixEnd_6661023 3420306449653597450579019 := by
  unfold tailWord_6661023
  simp only [CollatzResearch.WordTrace]
  refine ⟨242947467747258758003579723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161964978498172505335719815 242947467747258758003579723)
  ·
    refine ⟨364421201620888137005369585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242947467747258758003579723 364421201620888137005369585)
    ·
      refine ⟨273315901215666102754027189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 364421201620888137005369585 273315901215666102754027189)
      ·
        refine ⟨25623365738968697133190049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 273315901215666102754027189 25623365738968697133190049)
        ·
          refine ⟨19217524304226522849892537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25623365738968697133190049 19217524304226522849892537)
          ·
            refine ⟨14413143228169892137419403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19217524304226522849892537 14413143228169892137419403)
            ·
              refine ⟨21619714842254838206129105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14413143228169892137419403 21619714842254838206129105)
              ·
                refine ⟨16214786131691128654596829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21619714842254838206129105 16214786131691128654596829)
                ·
                  refine ⟨6080544799384173245473811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16214786131691128654596829 6080544799384173245473811)
                  ·
                    refine ⟨9120817199076259868210717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6080544799384173245473811 9120817199076259868210717)
                    ·
                      refine ⟨3420306449653597450579019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9120817199076259868210717 3420306449653597450579019)
                      ·
                        rfl

theorem cell23_6661023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 2, 3, 1, 3].length) (baseStart_6661023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6661023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6661023 prefixEnd_6661023 := by exact prefixLift 6661023
  have htrace : WordTrace (prefixWord ++ tailWord_6661023) baseStart_6661023 baseEnd_6661023 := by
    simpa [prefixWord, tailWord_6661023, baseEnd_6661023] using wordTrace_append hprefix tailTrace_6661023
  have hstable : (prefixWord ++ tailWord_6661023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6661023).length < 2 ^ (prefixWord ++ tailWord_6661023).sum := by decide
  have hdescent : baseEnd_6661023 < baseStart_6661023 := by decide
  rcases family_descends (prefixWord ++ tailWord_6661023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6661026 : List Nat := [3, 3, 1, 2, 2, 1, 2, 1, 3, 5]
def baseStart_6661026 : Nat := 118140960795 + 6661026 * 2 ^ 59
def prefixEnd_6661026 : Nat := 4983230072969 + 3 ^ 40 * 6661026 * 2
def baseEnd_6661026 : Nat := 1140102663365186979613835

theorem tailTrace_6661026 : CollatzResearch.WordTrace tailWord_6661026 prefixEnd_6661026 1140102663365186979613835 := by
  unfold tailWord_6661026
  simp only [CollatzResearch.WordTrace]
  refine ⟨60736894291561972378984733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161965051444165259677292621 60736894291561972378984733)
  ·
    refine ⟨22776335359335739642119275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60736894291561972378984733 22776335359335739642119275)
    ·
      refine ⟨34164503039003609463178913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22776335359335739642119275 34164503039003609463178913)
      ·
        refine ⟨25623377279252707097384185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34164503039003609463178913 25623377279252707097384185)
        ·
          refine ⟨19217532959439530323038139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25623377279252707097384185 19217532959439530323038139)
          ·
            refine ⟨28826299439159295484557209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19217532959439530323038139 28826299439159295484557209)
            ·
              refine ⟨21619724579369471613417907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28826299439159295484557209 21619724579369471613417907)
              ·
                refine ⟨32429586869054207420126861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21619724579369471613417907 32429586869054207420126861)
                ·
                  refine ⟨12161095075895327782547573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32429586869054207420126861 12161095075895327782547573)
                  ·
                    refine ⟨1140102663365186979613835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12161095075895327782547573 1140102663365186979613835)
                    ·
                      rfl

theorem cell23_6661026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 1, 3, 5].length) (baseStart_6661026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6661026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6661026 prefixEnd_6661026 := by exact prefixLift 6661026
  have htrace : WordTrace (prefixWord ++ tailWord_6661026) baseStart_6661026 baseEnd_6661026 := by
    simpa [prefixWord, tailWord_6661026, baseEnd_6661026] using wordTrace_append hprefix tailTrace_6661026
  have hstable : (prefixWord ++ tailWord_6661026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6661026).length < 2 ^ (prefixWord ++ tailWord_6661026).sum := by decide
  have hdescent : baseEnd_6661026 < baseStart_6661026 := by decide
  rcases family_descends (prefixWord ++ tailWord_6661026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6661056 : List Nat := [2, 1, 1, 2, 3, 4, 1, 1, 4, 4]
def baseStart_6661056 : Nat := 118140960795 + 6661056 * 2 ^ 59
def prefixEnd_6661056 : Nat := 4983230072969 + 3 ^ 40 * 6661056 * 2
def baseEnd_6661056 : Nat := 1140107798171731940488789

theorem tailTrace_6661056 : CollatzResearch.WordTrace tailWord_6661056 prefixEnd_6661056 1140107798171731940488789 := by
  unfold tailWord_6661056
  simp only [CollatzResearch.WordTrace]
  refine ⟨121474335678069602319765511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161965780904092803093020681 121474335678069602319765511)
  ·
    refine ⟨182211503517104403479648267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121474335678069602319765511 182211503517104403479648267)
    ·
      refine ⟨273317255275656605219472401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182211503517104403479648267 273317255275656605219472401)
      ·
        refine ⟨204987941456742453914604301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 273317255275656605219472401 204987941456742453914604301)
        ·
          refine ⟨76870478046278420217976613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 204987941456742453914604301 76870478046278420217976613)
          ·
            refine ⟨14413214633677203790870615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76870478046278420217976613 14413214633677203790870615)
            ·
              refine ⟨21619821950515805686305923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14413214633677203790870615 21619821950515805686305923)
              ·
                refine ⟨32429732925773708529458885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21619821950515805686305923 32429732925773708529458885)
                ·
                  refine ⟨6080574923582570349273541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32429732925773708529458885 6080574923582570349273541)
                  ·
                    refine ⟨1140107798171731940488789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6080574923582570349273541 1140107798171731940488789)
                    ·
                      rfl

theorem cell23_6661056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 1, 4, 4].length) (baseStart_6661056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6661056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6661056 prefixEnd_6661056 := by exact prefixLift 6661056
  have htrace : WordTrace (prefixWord ++ tailWord_6661056) baseStart_6661056 baseEnd_6661056 := by
    simpa [prefixWord, tailWord_6661056, baseEnd_6661056] using wordTrace_append hprefix tailTrace_6661056
  have hstable : (prefixWord ++ tailWord_6661056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6661056).length < 2 ^ (prefixWord ++ tailWord_6661056).sum := by decide
  have hdescent : baseEnd_6661056 < baseStart_6661056 := by decide
  rcases family_descends (prefixWord ++ tailWord_6661056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6661063 : List Nat := [1, 1, 4, 1, 1, 2, 3, 3, 3, 2, 2]
def baseStart_6661063 : Nat := 118140960795 + 6661063 * 2 ^ 59
def prefixEnd_6661063 : Nat := 4983230072969 + 3 ^ 40 * 6661063 * 2
def baseEnd_6661063 : Nat := 3420326988879777294078835

theorem tailTrace_6661063 : CollatzResearch.WordTrace tailWord_6661063 prefixEnd_6661063 3420326988879777294078835 := by
  unfold tailWord_6661063
  simp only [CollatzResearch.WordTrace]
  refine ⟨242948926667113844835035843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161965951111409229890023895 242948926667113844835035843)
  ·
    refine ⟨364423390000670767252553765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242948926667113844835035843 364423390000670767252553765)
    ·
      refine ⟨68329385625125768859853831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 364423390000670767252553765 68329385625125768859853831)
      ·
        refine ⟨102494078437688653289780747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68329385625125768859853831 102494078437688653289780747)
        ·
          refine ⟨153741117656532979934671121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102494078437688653289780747 153741117656532979934671121)
          ·
            refine ⟨115305838242399734951003341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153741117656532979934671121 115305838242399734951003341)
            ·
              refine ⟨43239689340899900606626253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 115305838242399734951003341 43239689340899900606626253)
              ·
                refine ⟨16214883502837462727484845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43239689340899900606626253 16214883502837462727484845)
                ·
                  refine ⟨6080581313564048522806817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16214883502837462727484845 6080581313564048522806817)
                  ·
                    refine ⟨4560435985173036392105113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6080581313564048522806817 4560435985173036392105113)
                    ·
                      refine ⟨3420326988879777294078835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4560435985173036392105113 3420326988879777294078835)
                      ·
                        rfl

theorem cell23_6661063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 3, 3, 2, 2].length) (baseStart_6661063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6661063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6661063 prefixEnd_6661063 := by exact prefixLift 6661063
  have htrace : WordTrace (prefixWord ++ tailWord_6661063) baseStart_6661063 baseEnd_6661063 := by
    simpa [prefixWord, tailWord_6661063, baseEnd_6661063] using wordTrace_append hprefix tailTrace_6661063
  have hstable : (prefixWord ++ tailWord_6661063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6661063).length < 2 ^ (prefixWord ++ tailWord_6661063).sum := by decide
  have hdescent : baseEnd_6661063 < baseStart_6661063 := by decide
  rcases family_descends (prefixWord ++ tailWord_6661063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6661073 : List Nat := [1, 2, 2, 1, 2, 1, 7, 1, 2, 4]
def baseStart_6661073 : Nat := 118140960795 + 6661073 * 2 ^ 59
def prefixEnd_6661073 : Nat := 4983230072969 + 3 ^ 40 * 6661073 * 2
def baseEnd_6661073 : Nat := 1140110707895440751651263

theorem tailTrace_6661073 : CollatzResearch.WordTrace tailWord_6661073 prefixEnd_6661073 1140110707895440751651263 := by
  unfold tailWord_6661073
  simp only [CollatzResearch.WordTrace]
  refine ⟨242949291397077616542899873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161966194264718411028599915 242949291397077616542899873)
  ·
    refine ⟨182211968547808212407174905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242949291397077616542899873 182211968547808212407174905)
    ·
      refine ⟨136658976410856159305381179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182211968547808212407174905 136658976410856159305381179)
      ·
        refine ⟨204988464616284238958071769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136658976410856159305381179 204988464616284238958071769)
        ·
          refine ⟨153741348462213179218553827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 204988464616284238958071769 153741348462213179218553827)
          ·
            refine ⟨230612022693319768827830741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153741348462213179218553827 230612022693319768827830741)
            ·
              refine ⟨5404969281874682081902283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 230612022693319768827830741 5404969281874682081902283)
              ·
                refine ⟨8107453922812023122853425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5404969281874682081902283 8107453922812023122853425)
                ·
                  refine ⟨6080590442109017342140069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8107453922812023122853425 6080590442109017342140069)
                  ·
                    refine ⟨1140110707895440751651263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6080590442109017342140069 1140110707895440751651263)
                    ·
                      rfl

theorem cell23_6661073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 7, 1, 2, 4].length) (baseStart_6661073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6661073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6661073 prefixEnd_6661073 := by exact prefixLift 6661073
  have htrace : WordTrace (prefixWord ++ tailWord_6661073) baseStart_6661073 baseEnd_6661073 := by
    simpa [prefixWord, tailWord_6661073, baseEnd_6661073] using wordTrace_append hprefix tailTrace_6661073
  have hstable : (prefixWord ++ tailWord_6661073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6661073).length < 2 ^ (prefixWord ++ tailWord_6661073).sum := by decide
  have hdescent : baseEnd_6661073 < baseStart_6661073 := by decide
  rcases family_descends (prefixWord ++ tailWord_6661073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6661076 : List Nat := [2, 4, 1, 2, 1, 3, 1, 1, 1, 1, 6]
def baseStart_6661076 : Nat := 118140960795 + 6661076 * 2 ^ 59
def prefixEnd_6661076 : Nat := 4983230072969 + 3 ^ 40 * 6661076 * 2
def baseEnd_6661076 : Nat := 3420333664128285743216275

theorem tailTrace_6661076 : CollatzResearch.WordTrace tailWord_6661076 prefixEnd_6661076 3420333664128285743216275 := by
  unfold tailWord_6661076
  simp only [CollatzResearch.WordTrace]
  refine ⟨121474700408033374027629541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161966267210711165370172721 121474700408033374027629541)
  ·
    refine ⟨22776506326506257630180539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 121474700408033374027629541 22776506326506257630180539)
    ·
      refine ⟨34164759489759386445270809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22776506326506257630180539 34164759489759386445270809)
      ·
        refine ⟨25623569617319539833953107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34164759489759386445270809 25623569617319539833953107)
        ·
          refine ⟨38435354425979309750929661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25623569617319539833953107 38435354425979309750929661)
          ·
            refine ⟨14413257909742241156598623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38435354425979309750929661 14413257909742241156598623)
            ·
              refine ⟨21619886864613361734897935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14413257909742241156598623 21619886864613361734897935)
              ·
                refine ⟨32429830296920042602346903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21619886864613361734897935 32429830296920042602346903)
                ·
                  refine ⟨48644745445380063903520355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32429830296920042602346903 48644745445380063903520355)
                  ·
                    refine ⟨72967118168070095855280533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48644745445380063903520355 72967118168070095855280533)
                    ·
                      refine ⟨3420333664128285743216275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72967118168070095855280533 3420333664128285743216275)
                      ·
                        rfl

theorem cell23_6661076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_6661076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6661076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6661076 prefixEnd_6661076 := by exact prefixLift 6661076
  have htrace : WordTrace (prefixWord ++ tailWord_6661076) baseStart_6661076 baseEnd_6661076 := by
    simpa [prefixWord, tailWord_6661076, baseEnd_6661076] using wordTrace_append hprefix tailTrace_6661076
  have hstable : (prefixWord ++ tailWord_6661076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6661076).length < 2 ^ (prefixWord ++ tailWord_6661076).sum := by decide
  have hdescent : baseEnd_6661076 < baseStart_6661076 := by decide
  rcases family_descends (prefixWord ++ tailWord_6661076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6661096 : List Nat := [2, 1, 4, 1, 1, 1, 2, 4, 1, 3, 3]
def baseStart_6661096 : Nat := 118140960795 + 6661096 * 2 ^ 59
def prefixEnd_6661096 : Nat := 4983230072969 + 3 ^ 40 * 6661096 * 2
def baseEnd_6661096 : Nat := 3420343933741375664966183

theorem tailTrace_6661096 : CollatzResearch.WordTrace tailWord_6661096 prefixEnd_6661096 3420343933741375664966183 := by
  unfold tailWord_6661096
  simp only [CollatzResearch.WordTrace]
  refine ⟨121475065137997145735493571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161966753517329527647324761 121475065137997145735493571)
  ·
    refine ⟨182212597706995718603240357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121475065137997145735493571 182212597706995718603240357)
    ·
      refine ⟨34164862070061697238107567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 182212597706995718603240357 34164862070061697238107567)
      ·
        refine ⟨51247293105092545857161351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34164862070061697238107567 51247293105092545857161351)
        ·
          refine ⟨76870939657638818785742027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51247293105092545857161351 76870939657638818785742027)
          ·
            refine ⟨115306409486458228178613041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76870939657638818785742027 115306409486458228178613041)
            ·
              refine ⟨86479807114843671133959781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115306409486458228178613041 86479807114843671133959781)
              ·
                refine ⟨16214963834033188337617459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 86479807114843671133959781 16214963834033188337617459)
                ·
                  refine ⟨24322445751049782506426189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16214963834033188337617459 24322445751049782506426189)
                  ·
                    refine ⟨9120917156643668439909821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24322445751049782506426189 9120917156643668439909821)
                    ·
                      refine ⟨3420343933741375664966183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9120917156643668439909821 3420343933741375664966183)
                      ·
                        rfl

theorem cell23_6661096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 4, 1, 3, 3].length) (baseStart_6661096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6661096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6661096 prefixEnd_6661096 := by exact prefixLift 6661096
  have htrace : WordTrace (prefixWord ++ tailWord_6661096) baseStart_6661096 baseEnd_6661096 := by
    simpa [prefixWord, tailWord_6661096, baseEnd_6661096] using wordTrace_append hprefix tailTrace_6661096
  have hstable : (prefixWord ++ tailWord_6661096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6661096).length < 2 ^ (prefixWord ++ tailWord_6661096).sum := by decide
  have hdescent : baseEnd_6661096 < baseStart_6661096 := by decide
  rcases family_descends (prefixWord ++ tailWord_6661096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6661108 : List Nat := [2, 6, 2, 1, 2, 1, 1, 1, 3, 1, 3]
def baseStart_6661108 : Nat := 118140960795 + 6661108 * 2 ^ 59
def prefixEnd_6661108 : Nat := 4983230072969 + 3 ^ 40 * 6661108 * 2
def baseEnd_6661108 : Nat := 3420350095509229618016129

theorem tailTrace_6661108 : CollatzResearch.WordTrace tailWord_6661108 prefixEnd_6661108 3420350095509229618016129 := by
  unfold tailWord_6661108
  simp only [CollatzResearch.WordTrace]
  refine ⟨121475283975975408760211989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161967045301300545013615985 121475283975975408760211989)
  ·
    refine ⟨5694153936373847285634937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 121475283975975408760211989 5694153936373847285634937)
    ·
      refine ⟨4270615452280385464226203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5694153936373847285634937 4270615452280385464226203)
      ·
        refine ⟨6405923178420578196339305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4270615452280385464226203 6405923178420578196339305)
        ·
          refine ⟨4804442383815433647254479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6405923178420578196339305 4804442383815433647254479)
          ·
            refine ⟨7206663575723150470881719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4804442383815433647254479 7206663575723150470881719)
            ·
              refine ⟨10809995363584725706322579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7206663575723150470881719 10809995363584725706322579)
              ·
                refine ⟨16214993045377088559483869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10809995363584725706322579 16214993045377088559483869)
                ·
                  refine ⟨6080622392016408209806451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16214993045377088559483869 6080622392016408209806451)
                  ·
                    refine ⟨9120933588024612314709677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6080622392016408209806451 9120933588024612314709677)
                    ·
                      refine ⟨3420350095509229618016129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9120933588024612314709677 3420350095509229618016129)
                      ·
                        rfl

theorem cell23_6661108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_6661108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6661108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6661108 prefixEnd_6661108 := by exact prefixLift 6661108
  have htrace : WordTrace (prefixWord ++ tailWord_6661108) baseStart_6661108 baseEnd_6661108 := by
    simpa [prefixWord, tailWord_6661108, baseEnd_6661108] using wordTrace_append hprefix tailTrace_6661108
  have hstable : (prefixWord ++ tailWord_6661108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6661108).length < 2 ^ (prefixWord ++ tailWord_6661108).sum := by decide
  have hdescent : baseEnd_6661108 < baseStart_6661108 := by decide
  rcases family_descends (prefixWord ++ tailWord_6661108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6661113 : List Nat := [1, 2, 1, 3, 1, 3, 2, 4, 2, 1, 3]
def baseStart_6661113 : Nat := 118140960795 + 6661113 * 2 ^ 59
def prefixEnd_6661113 : Nat := 4983230072969 + 3 ^ 40 * 6661113 * 2
def baseEnd_6661113 : Nat := 3420352662912502098453605

theorem tailTrace_6661113 : CollatzResearch.WordTrace tailWord_6661113 prefixEnd_6661113 3420352662912502098453605 := by
  unfold tailWord_6661113
  simp only [CollatzResearch.WordTrace]
  refine ⟨242950750316932703374355993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161967166877955135582903995 242950750316932703374355993)
  ·
    refine ⟨182213062737699527530766995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242950750316932703374355993 182213062737699527530766995)
    ·
      refine ⟨273319594106549291296150493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182213062737699527530766995 273319594106549291296150493)
      ·
        refine ⟨102494847789955984236056435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 273319594106549291296150493 102494847789955984236056435)
        ·
          refine ⟨153742271684933976354084653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102494847789955984236056435 153742271684933976354084653)
          ·
            refine ⟨57653351881850241132781745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 153742271684933976354084653 57653351881850241132781745)
            ·
              refine ⟨43240013911387680849586309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57653351881850241132781745 43240013911387680849586309)
              ·
                refine ⟨8107502608385190159297433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43240013911387680849586309 8107502608385190159297433)
                ·
                  refine ⟨6080626956288892619473075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8107502608385190159297433 6080626956288892619473075)
                  ·
                    refine ⟨9120940434433338929209613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6080626956288892619473075 9120940434433338929209613)
                    ·
                      refine ⟨3420352662912502098453605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9120940434433338929209613 3420352662912502098453605)
                      ·
                        rfl

theorem cell23_6661113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 4, 2, 1, 3].length) (baseStart_6661113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6661113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6661113 prefixEnd_6661113 := by exact prefixLift 6661113
  have htrace : WordTrace (prefixWord ++ tailWord_6661113) baseStart_6661113 baseEnd_6661113 := by
    simpa [prefixWord, tailWord_6661113, baseEnd_6661113] using wordTrace_append hprefix tailTrace_6661113
  have hstable : (prefixWord ++ tailWord_6661113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6661113).length < 2 ^ (prefixWord ++ tailWord_6661113).sum := by decide
  have hdescent : baseEnd_6661113 < baseStart_6661113 := by decide
  rcases family_descends (prefixWord ++ tailWord_6661113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6661129 : List Nat := [1, 2, 1, 1, 3, 1, 1, 5, 2, 6]
def baseStart_6661129 : Nat := 118140960795 + 6661129 * 2 ^ 59
def prefixEnd_6661129 : Nat := 4983230072969 + 3 ^ 40 * 6661129 * 2
def baseEnd_6661129 : Nat := 1140120292867658011951177

theorem tailTrace_6661129 : CollatzResearch.WordTrace tailWord_6661129 prefixEnd_6661129 1140120292867658011951177 := by
  unfold tailWord_6661129
  simp only [CollatzResearch.WordTrace]
  refine ⟨242951333884874738106938441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161967555923249825404625627 242951333884874738106938441)
  ·
    refine ⟨182213500413656053580203831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242951333884874738106938441 182213500413656053580203831)
    ·
      refine ⟨273320250620484080370305747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182213500413656053580203831 273320250620484080370305747)
      ·
        refine ⟨409980375930726120555458621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273320250620484080370305747 409980375930726120555458621)
        ·
          refine ⟨153742640974022295208296983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 409980375930726120555458621 153742640974022295208296983)
          ·
            refine ⟨230613961461033442812445475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153742640974022295208296983 230613961461033442812445475)
            ·
              refine ⟨345920942191550164218668213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 230613961461033442812445475 345920942191550164218668213)
              ·
                refine ⟨32430088330457827895500145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 345920942191550164218668213 32430088330457827895500145)
                ·
                  refine ⟨24322566247843370921625109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32430088330457827895500145 24322566247843370921625109)
                  ·
                    refine ⟨1140120292867658011951177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24322566247843370921625109 1140120292867658011951177)
                    ·
                      rfl

theorem cell23_6661129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 5, 2, 6].length) (baseStart_6661129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6661129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6661129 prefixEnd_6661129 := by exact prefixLift 6661129
  have htrace : WordTrace (prefixWord ++ tailWord_6661129) baseStart_6661129 baseEnd_6661129 := by
    simpa [prefixWord, tailWord_6661129, baseEnd_6661129] using wordTrace_append hprefix tailTrace_6661129
  have hstable : (prefixWord ++ tailWord_6661129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6661129).length < 2 ^ (prefixWord ++ tailWord_6661129).sum := by decide
  have hdescent : baseEnd_6661129 < baseStart_6661129 := by decide
  rcases family_descends (prefixWord ++ tailWord_6661129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6661130 : List Nat := [3, 1, 2, 2, 3, 2, 1, 3, 2, 1, 3]
def baseStart_6661130 : Nat := 118140960795 + 6661130 * 2 ^ 59
def prefixEnd_6661130 : Nat := 4983230072969 + 3 ^ 40 * 6661130 * 2
def baseEnd_6661130 : Nat := 3420361392083628531941027

theorem tailTrace_6661130 : CollatzResearch.WordTrace tailWord_6661130 prefixEnd_6661130 3420361392083628531941027 := by
  unfold tailWord_6661130
  simp only [CollatzResearch.WordTrace]
  refine ⟨60737842589467778819431211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161967580238580743518483229 60737842589467778819431211)
  ·
    refine ⟨91106763884201668229146817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60737842589467778819431211 91106763884201668229146817)
    ·
      refine ⟨68330072913151251171860113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91106763884201668229146817 68330072913151251171860113)
      ·
        refine ⟨51247554684863438378895085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68330072913151251171860113 51247554684863438378895085)
        ·
          refine ⟨19217833006823789392085657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51247554684863438378895085 19217833006823789392085657)
          ·
            refine ⟨14413374755117842044064243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19217833006823789392085657 14413374755117842044064243)
            ·
              refine ⟨21620062132676763066096365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14413374755117842044064243 21620062132676763066096365)
              ·
                refine ⟨8107523299753786149786137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21620062132676763066096365 8107523299753786149786137)
                ·
                  refine ⟨6080642474815339612339603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8107523299753786149786137 6080642474815339612339603)
                  ·
                    refine ⟨9120963712223009418509405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6080642474815339612339603 9120963712223009418509405)
                    ·
                      refine ⟨3420361392083628531941027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9120963712223009418509405 3420361392083628531941027)
                      ·
                        rfl

theorem cell23_6661130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 3, 2, 1, 3].length) (baseStart_6661130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6661130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6661130 prefixEnd_6661130 := by exact prefixLift 6661130
  have htrace : WordTrace (prefixWord ++ tailWord_6661130) baseStart_6661130 baseEnd_6661130 := by
    simpa [prefixWord, tailWord_6661130, baseEnd_6661130] using wordTrace_append hprefix tailTrace_6661130
  have hstable : (prefixWord ++ tailWord_6661130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6661130).length < 2 ^ (prefixWord ++ tailWord_6661130).sum := by decide
  have hdescent : baseEnd_6661130 < baseStart_6661130 := by decide
  rcases family_descends (prefixWord ++ tailWord_6661130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6661153 : List Nat := [1, 2, 3, 2, 3, 1, 1, 1, 3, 4, 2]
def baseStart_6661153 : Nat := 118140960795 + 6661153 * 2 ^ 59
def prefixEnd_6661153 : Nat := 4983230072969 + 3 ^ 40 * 6661153 * 2
def baseEnd_6661153 : Nat := 3420373202138681941953421

theorem tailTrace_6661153 : CollatzResearch.WordTrace tailWord_6661153 prefixEnd_6661153 3420373202138681941953421 := by
  unfold tailWord_6661153
  simp only [CollatzResearch.WordTrace]
  refine ⟨242952209236787790205812113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161968139491191860137208075 242952209236787790205812113)
  ·
    refine ⟨182214156927590842654359085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242952209236787790205812113 182214156927590842654359085)
    ·
      refine ⟨68330308847846565995384657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182214156927590842654359085 68330308847846565995384657)
      ·
        refine ⟨51247731635884924496538493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68330308847846565995384657 51247731635884924496538493)
        ·
          refine ⟨19217899363456846686201935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51247731635884924496538493 19217899363456846686201935)
          ·
            refine ⟨28826849045185270029302903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19217899363456846686201935 28826849045185270029302903)
            ·
              refine ⟨43240273567777905043954355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28826849045185270029302903 43240273567777905043954355)
              ·
                refine ⟨64860410351666857565931533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43240273567777905043954355 64860410351666857565931533)
                ·
                  refine ⟨24322653881875071587224325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64860410351666857565931533 24322653881875071587224325)
                  ·
                    refine ⟨4560497602851575922604561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24322653881875071587224325 4560497602851575922604561)
                    ·
                      refine ⟨3420373202138681941953421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4560497602851575922604561 3420373202138681941953421)
                      ·
                        rfl

theorem cell23_6661153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 1, 3, 4, 2].length) (baseStart_6661153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6661153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6661153 prefixEnd_6661153 := by exact prefixLift 6661153
  have htrace : WordTrace (prefixWord ++ tailWord_6661153) baseStart_6661153 baseEnd_6661153 := by
    simpa [prefixWord, tailWord_6661153, baseEnd_6661153] using wordTrace_append hprefix tailTrace_6661153
  have hstable : (prefixWord ++ tailWord_6661153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6661153).length < 2 ^ (prefixWord ++ tailWord_6661153).sum := by decide
  have hdescent : baseEnd_6661153 < baseStart_6661153 := by decide
  rcases family_descends (prefixWord ++ tailWord_6661153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6661287 : List Nat := [1, 1, 6, 2, 1, 3, 1, 1, 3, 4]
def baseStart_6661287 : Nat := 118140960795 + 6661287 * 2 ^ 59
def prefixEnd_6661287 : Nat := 4983230072969 + 3 ^ 40 * 6661287 * 2
def baseEnd_6661287 : Nat := 1140147336182128139225935

theorem tailTrace_6661287 : CollatzResearch.WordTrace tailWord_6661287 prefixEnd_6661287 1140147336182128139225935 := by
  unfold tailWord_6661287
  simp only [CollatzResearch.WordTrace]
  refine ⟨242957096618302331091190115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161971397745534887394126743 242957096618302331091190115)
  ·
    refine ⟨364435644927453496636785173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242957096618302331091190115 364435644927453496636785173)
    ·
      refine ⟨17082920855974382654849305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 364435644927453496636785173 17082920855974382654849305)
      ·
        refine ⟨12812190641980786991136979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17082920855974382654849305 12812190641980786991136979)
        ·
          refine ⟨19218285962971180486705469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12812190641980786991136979 19218285962971180486705469)
          ·
            refine ⟨7206857236114192682514551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19218285962971180486705469 7206857236114192682514551)
            ·
              refine ⟨10810285854171289023771827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7206857236114192682514551 10810285854171289023771827)
              ·
                refine ⟨16215428781256933535657741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10810285854171289023771827 16215428781256933535657741)
                ·
                  refine ⟨6080785792971350075871653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16215428781256933535657741 6080785792971350075871653)
                  ·
                    refine ⟨1140147336182128139225935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6080785792971350075871653 1140147336182128139225935)
                    ·
                      rfl

theorem cell23_6661287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 1, 1, 3, 4].length) (baseStart_6661287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6661287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6661287 prefixEnd_6661287 := by exact prefixLift 6661287
  have htrace : WordTrace (prefixWord ++ tailWord_6661287) baseStart_6661287 baseEnd_6661287 := by
    simpa [prefixWord, tailWord_6661287, baseEnd_6661287] using wordTrace_append hprefix tailTrace_6661287
  have hstable : (prefixWord ++ tailWord_6661287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6661287).length < 2 ^ (prefixWord ++ tailWord_6661287).sum := by decide
  have hdescent : baseEnd_6661287 < baseStart_6661287 := by decide
  rcases family_descends (prefixWord ++ tailWord_6661287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6661296 : List Nat := [2, 1, 1, 1, 2, 1, 2, 3, 5, 5]
def baseStart_6661296 : Nat := 118140960795 + 6661296 * 2 ^ 59
def prefixEnd_6661296 : Nat := 4983230072969 + 3 ^ 40 * 6661296 * 2
def baseEnd_6661296 : Nat := 1140148876624091627488421

theorem tailTrace_6661296 : CollatzResearch.WordTrace tailWord_6661296 prefixEnd_6661296 1140148876624091627488421 := by
  unfold tailWord_6661296
  simp only [CollatzResearch.WordTrace]
  refine ⟨121478712437634862814133871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161971616583513150418845161 121478712437634862814133871)
  ·
    refine ⟨182218068656452294221200807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121478712437634862814133871 182218068656452294221200807)
    ·
      refine ⟨273327102984678441331801211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182218068656452294221200807 273327102984678441331801211)
      ·
        refine ⟨409990654477017661997701817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273327102984678441331801211 409990654477017661997701817)
        ·
          refine ⟨307492990857763246498276363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 409990654477017661997701817 307492990857763246498276363)
          ·
            refine ⟨461239486286644869747414545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 307492990857763246498276363 461239486286644869747414545)
            ·
              refine ⟨345929614714983652310560909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 461239486286644869747414545 345929614714983652310560909)
              ·
                refine ⟨129723605518118869616460341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 345929614714983652310560909 129723605518118869616460341)
                ·
                  refine ⟨12161588017323644026543157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 129723605518118869616460341 12161588017323644026543157)
                  ·
                    refine ⟨1140148876624091627488421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12161588017323644026543157 1140148876624091627488421)
                    ·
                      rfl

theorem cell23_6661296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 5, 5].length) (baseStart_6661296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6661296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6661296 prefixEnd_6661296 := by exact prefixLift 6661296
  have htrace : WordTrace (prefixWord ++ tailWord_6661296) baseStart_6661296 baseEnd_6661296 := by
    simpa [prefixWord, tailWord_6661296, baseEnd_6661296] using wordTrace_append hprefix tailTrace_6661296
  have hstable : (prefixWord ++ tailWord_6661296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6661296).length < 2 ^ (prefixWord ++ tailWord_6661296).sum := by decide
  have hdescent : baseEnd_6661296 < baseStart_6661296 := by decide
  rcases family_descends (prefixWord ++ tailWord_6661296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6661320 : List Nat := [2, 1, 3, 1, 2, 1, 3, 3, 2, 3, 2]
def baseStart_6661320 : Nat := 118140960795 + 6661320 * 2 ^ 59
def prefixEnd_6661320 : Nat := 4983230072969 + 3 ^ 40 * 6661320 * 2
def baseEnd_6661320 : Nat := 3420458953407982788565153

theorem tailTrace_6661320 : CollatzResearch.WordTrace tailWord_6661320 prefixEnd_6661320 3420458953407982788565153 := by
  unfold tailWord_6661320
  simp only [CollatzResearch.WordTrace]
  refine ⟨121479150113591388863570707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161972200151455185151427609 121479150113591388863570707)
  ·
    refine ⟨182218725170387083295356061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121479150113591388863570707 182218725170387083295356061)
    ·
      refine ⟨68332021938895156235758523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182218725170387083295356061 68332021938895156235758523)
      ·
        refine ⟨102498032908342734353637785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68332021938895156235758523 102498032908342734353637785)
        ·
          refine ⟨76873524681257050765228339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102498032908342734353637785 76873524681257050765228339)
          ·
            refine ⟨115310287021885576147842509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76873524681257050765228339 115310287021885576147842509)
            ·
              refine ⟨43241357633207091055440941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 115310287021885576147842509 43241357633207091055440941)
              ·
                refine ⟨16215509112452659145790353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43241357633207091055440941 16215509112452659145790353)
                ·
                  refine ⟨12161631834339494359342765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16215509112452659145790353 12161631834339494359342765)
                  ·
                    refine ⟨4560611937877310384753537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12161631834339494359342765 4560611937877310384753537)
                    ·
                      refine ⟨3420458953407982788565153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4560611937877310384753537 3420458953407982788565153)
                      ·
                        rfl

theorem cell23_6661320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 3, 2, 3, 2].length) (baseStart_6661320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6661320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6661320 prefixEnd_6661320 := by exact prefixLift 6661320
  have htrace : WordTrace (prefixWord ++ tailWord_6661320) baseStart_6661320 baseEnd_6661320 := by
    simpa [prefixWord, tailWord_6661320, baseEnd_6661320] using wordTrace_append hprefix tailTrace_6661320
  have hstable : (prefixWord ++ tailWord_6661320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6661320).length < 2 ^ (prefixWord ++ tailWord_6661320).sum := by decide
  have hdescent : baseEnd_6661320 < baseStart_6661320 := by decide
  rcases family_descends (prefixWord ++ tailWord_6661320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6661343 : List Nat := [1, 1, 2, 3, 2, 1, 2, 3, 4, 4]
def baseStart_6661343 : Nat := 118140960795 + 6661343 * 2 ^ 59
def prefixEnd_6661343 : Nat := 4983230072969 + 3 ^ 40 * 6661343 * 2
def baseEnd_6661343 : Nat := 1140156921154345399525849

theorem tailTrace_6661343 : CollatzResearch.WordTrace tailWord_6661343 prefixEnd_6661343 1140156921154345399525849 := by
  unfold tailWord_6661343
  simp only [CollatzResearch.WordTrace]
  refine ⟨242959139106099452655228683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161972759404066301770152455 242959139106099452655228683)
  ·
    refine ⟨364438708659149178982843025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242959139106099452655228683 364438708659149178982843025)
    ·
      refine ⟨273329031494361884237132269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 364438708659149178982843025 273329031494361884237132269)
      ·
        refine ⟨102498386810385706588924601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 273329031494361884237132269 102498386810385706588924601)
        ·
          refine ⟨76873790107789279941693451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102498386810385706588924601 76873790107789279941693451)
          ·
            refine ⟨115310685161683919912540177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76873790107789279941693451 115310685161683919912540177)
            ·
              refine ⟨86483013871262939934405133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115310685161683919912540177 86483013871262939934405133)
              ·
                refine ⟨32431130201723602475401925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86483013871262939934405133 32431130201723602475401925)
                ·
                  refine ⟨6080836912823175464137861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32431130201723602475401925 6080836912823175464137861)
                  ·
                    refine ⟨1140156921154345399525849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6080836912823175464137861 1140156921154345399525849)
                    ·
                      rfl

theorem cell23_6661343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 3, 4, 4].length) (baseStart_6661343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6661343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6661343 prefixEnd_6661343 := by exact prefixLift 6661343
  have htrace : WordTrace (prefixWord ++ tailWord_6661343) baseStart_6661343 baseEnd_6661343 := by
    simpa [prefixWord, tailWord_6661343, baseEnd_6661343] using wordTrace_append hprefix tailTrace_6661343
  have hstable : (prefixWord ++ tailWord_6661343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6661343).length < 2 ^ (prefixWord ++ tailWord_6661343).sum := by decide
  have hdescent : baseEnd_6661343 < baseStart_6661343 := by decide
  rcases family_descends (prefixWord ++ tailWord_6661343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6661344 : List Nat := [2, 1, 1, 3, 1, 4, 4, 2, 1, 1, 3]
def baseStart_6661344 : Nat := 118140960795 + 6661344 * 2 ^ 59
def prefixEnd_6661344 : Nat := 4983230072969 + 3 ^ 40 * 6661344 * 2
def baseEnd_6661344 : Nat := 3420471276943690694665043

theorem tailTrace_6661344 : CollatzResearch.WordTrace tailWord_6661344 prefixEnd_6661344 3420471276943690694665043 := by
  unfold tailWord_6661344
  simp only [CollatzResearch.WordTrace]
  refine ⟨121479587789547914913007543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161972783719397219884010057 121479587789547914913007543)
  ·
    refine ⟨182219381684321872369511315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121479587789547914913007543 182219381684321872369511315)
    ·
      refine ⟨273329072526482808554266973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182219381684321872369511315 273329072526482808554266973)
      ·
        refine ⟨102498402197431053207850115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 273329072526482808554266973 102498402197431053207850115)
        ·
          refine ⟨153747603296146579811775173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102498402197431053207850115 153747603296146579811775173)
          ·
            refine ⟨28827675618027483714707845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 153747603296146579811775173 28827675618027483714707845)
            ·
              refine ⟨5405189178380153196507721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28827675618027483714707845 5405189178380153196507721)
              ·
                refine ⟨4053891883785114897380791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5405189178380153196507721 4053891883785114897380791)
                ·
                  refine ⟨6080837825677672346071187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4053891883785114897380791 6080837825677672346071187)
                  ·
                    refine ⟨9121256738516508519106781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6080837825677672346071187 9121256738516508519106781)
                    ·
                      refine ⟨3420471276943690694665043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9121256738516508519106781 3420471276943690694665043)
                      ·
                        rfl

theorem cell23_6661344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 4, 2, 1, 1, 3].length) (baseStart_6661344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6661344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6661344 prefixEnd_6661344 := by exact prefixLift 6661344
  have htrace : WordTrace (prefixWord ++ tailWord_6661344) baseStart_6661344 baseEnd_6661344 := by
    simpa [prefixWord, tailWord_6661344, baseEnd_6661344] using wordTrace_append hprefix tailTrace_6661344
  have hstable : (prefixWord ++ tailWord_6661344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6661344).length < 2 ^ (prefixWord ++ tailWord_6661344).sum := by decide
  have hdescent : baseEnd_6661344 < baseStart_6661344 := by decide
  rcases family_descends (prefixWord ++ tailWord_6661344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6661363 : List Nat := [1, 1, 1, 2, 2, 5, 1, 3, 1, 2, 4]
def baseStart_6661363 : Nat := 118140960795 + 6661363 * 2 ^ 59
def prefixEnd_6661363 : Nat := 4983230072969 + 3 ^ 40 * 6661363 * 2
def baseEnd_6661363 : Nat := 3420481033076126120327455

theorem tailTrace_6661363 : CollatzResearch.WordTrace tailWord_6661363 prefixEnd_6661363 3420481033076126120327455 := by
  unfold tailWord_6661363
  simp only [CollatzResearch.WordTrace]
  refine ⟨242959868566026996070956743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161973245710684664047304495 242959868566026996070956743)
  ·
    refine ⟨364439802849040494106435115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242959868566026996070956743 364439802849040494106435115)
    ·
      refine ⟨546659704273560741159652673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 364439802849040494106435115 546659704273560741159652673)
      ·
        refine ⟨409994778205170555869739505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 546659704273560741159652673 409994778205170555869739505)
        ·
          refine ⟨307496083653877916902304629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 409994778205170555869739505 307496083653877916902304629)
          ·
            refine ⟨28827757842551054709591059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 307496083653877916902304629 28827757842551054709591059)
            ·
              refine ⟨43241636763826582064386589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28827757842551054709591059 43241636763826582064386589)
              ·
                refine ⟨16215613786434968274144971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43241636763826582064386589 16215613786434968274144971)
                ·
                  refine ⟨24323420679652452411217457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16215613786434968274144971 24323420679652452411217457)
                  ·
                    refine ⟨18242565509739339308413093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24323420679652452411217457 18242565509739339308413093)
                    ·
                      refine ⟨3420481033076126120327455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18242565509739339308413093 3420481033076126120327455)
                      ·
                        rfl

theorem cell23_6661363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 3, 1, 2, 4].length) (baseStart_6661363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6661363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6661363 prefixEnd_6661363 := by exact prefixLift 6661363
  have htrace : WordTrace (prefixWord ++ tailWord_6661363) baseStart_6661363 baseEnd_6661363 := by
    simpa [prefixWord, tailWord_6661363, baseEnd_6661363] using wordTrace_append hprefix tailTrace_6661363
  have hstable : (prefixWord ++ tailWord_6661363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6661363).length < 2 ^ (prefixWord ++ tailWord_6661363).sum := by decide
  have hdescent : baseEnd_6661363 < baseStart_6661363 := by decide
  rcases family_descends (prefixWord ++ tailWord_6661363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6661370 : List Nat := [3, 1, 1, 1, 1, 4, 2, 4, 1, 2, 3]
def baseStart_6661370 : Nat := 118140960795 + 6661370 * 2 ^ 59
def prefixEnd_6661370 : Nat := 4983230072969 + 3 ^ 40 * 6661370 * 2
def baseEnd_6661370 : Nat := 3420484627440707592939923

theorem tailTrace_6661370 : CollatzResearch.WordTrace tailWord_6661370 prefixEnd_6661370 3420484627440707592939923 := by
  unfold tailWord_6661370
  simp only [CollatzResearch.WordTrace]
  refine ⟨60740030969250409066615391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161973415918001090844307709 60740030969250409066615391)
  ·
    refine ⟨91110046453875613599923087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60740030969250409066615391 91110046453875613599923087)
    ·
      refine ⟨136665069680813420399884631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91110046453875613599923087 136665069680813420399884631)
      ·
        refine ⟨204997604521220130599826947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136665069680813420399884631 204997604521220130599826947)
        ·
          refine ⟨307496406781830195899740421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204997604521220130599826947 307496406781830195899740421)
          ·
            refine ⟨57655576271593161731201329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 307496406781830195899740421 57655576271593161731201329)
            ·
              refine ⟨43241682203694871298400997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57655576271593161731201329 43241682203694871298400997)
              ·
                refine ⟨8107815413192788368450187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43241682203694871298400997 8107815413192788368450187)
                ·
                  refine ⟨12161723119789182552675281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8107815413192788368450187 12161723119789182552675281)
                  ·
                    refine ⟨9121292339841886914506461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12161723119789182552675281 9121292339841886914506461)
                    ·
                      refine ⟨3420484627440707592939923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9121292339841886914506461 3420484627440707592939923)
                      ·
                        rfl

theorem cell23_6661370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 4, 1, 2, 3].length) (baseStart_6661370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6661370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6661370 prefixEnd_6661370 := by exact prefixLift 6661370
  have htrace : WordTrace (prefixWord ++ tailWord_6661370) baseStart_6661370 baseEnd_6661370 := by
    simpa [prefixWord, tailWord_6661370, baseEnd_6661370] using wordTrace_append hprefix tailTrace_6661370
  have hstable : (prefixWord ++ tailWord_6661370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6661370).length < 2 ^ (prefixWord ++ tailWord_6661370).sum := by decide
  have hdescent : baseEnd_6661370 < baseStart_6661370 := by decide
  rcases family_descends (prefixWord ++ tailWord_6661370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6661380 : List Nat := [2, 3, 2, 2, 2, 1, 2, 2, 1, 2, 4]
def baseStart_6661380 : Nat := 118140960795 + 6661380 * 2 ^ 59
def prefixEnd_6661380 : Nat := 4983230072969 + 3 ^ 40 * 6661380 * 2
def baseEnd_6661380 : Nat := 3420489762247252553814877

theorem tailTrace_6661380 : CollatzResearch.WordTrace tailWord_6661380 prefixEnd_6661380 3420489762247252553814877 := by
  unfold tailWord_6661380
  simp only [CollatzResearch.WordTrace]
  refine ⟨121480244303482703987162797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161973659071310271982883729 121480244303482703987162797)
  ·
    refine ⟨45555091613806013995186049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121480244303482703987162797 45555091613806013995186049)
    ·
      refine ⟨34166318710354510496389537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45555091613806013995186049 34166318710354510496389537)
      ·
        refine ⟨25624739032765882872292153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34166318710354510496389537 25624739032765882872292153)
        ·
          refine ⟨19218554274574412154219115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25624739032765882872292153 19218554274574412154219115)
          ·
            refine ⟨28827831411861618231328673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19218554274574412154219115 28827831411861618231328673)
            ·
              refine ⟨21620873558896213673496505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28827831411861618231328673 21620873558896213673496505)
              ·
                refine ⟨16215655169172160255122379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21620873558896213673496505 16215655169172160255122379)
                ·
                  refine ⟨24323482753758240382683569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16215655169172160255122379 24323482753758240382683569)
                  ·
                    refine ⟨18242612065318680287012677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24323482753758240382683569 18242612065318680287012677)
                    ·
                      refine ⟨3420489762247252553814877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18242612065318680287012677 3420489762247252553814877)
                      ·
                        rfl

theorem cell23_6661380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_6661380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6661380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6661380 prefixEnd_6661380 := by exact prefixLift 6661380
  have htrace : WordTrace (prefixWord ++ tailWord_6661380) baseStart_6661380 baseEnd_6661380 := by
    simpa [prefixWord, tailWord_6661380, baseEnd_6661380] using wordTrace_append hprefix tailTrace_6661380
  have hstable : (prefixWord ++ tailWord_6661380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6661380).length < 2 ^ (prefixWord ++ tailWord_6661380).sum := by decide
  have hdescent : baseEnd_6661380 < baseStart_6661380 := by decide
  rcases family_descends (prefixWord ++ tailWord_6661380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6661384 : List Nat := [2, 1, 3, 2, 4, 2, 2, 1, 1, 1, 4]
def baseStart_6661384 : Nat := 118140960795 + 6661384 * 2 ^ 59
def prefixEnd_6661384 : Nat := 4983230072969 + 3 ^ 40 * 6661384 * 2
def baseEnd_6661384 : Nat := 3420491816169870538164859

theorem tailTrace_6661384 : CollatzResearch.WordTrace tailWord_6661384 prefixEnd_6661384 3420491816169870538164859 := by
  unfold tailWord_6661384
  simp only [CollatzResearch.WordTrace]
  refine ⟨121480317249475458328735603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161973756332633944438314137 121480317249475458328735603)
  ·
    refine ⟨182220475874213187493103405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121480317249475458328735603 182220475874213187493103405)
    ·
      refine ⟨68332678452829945309913777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182220475874213187493103405 68332678452829945309913777)
      ·
        refine ⟨51249508839622458982435333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68332678452829945309913777 51249508839622458982435333)
        ·
          refine ⟨9609282907429211059206625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51249508839622458982435333 9609282907429211059206625)
          ·
            refine ⟨7206962180571908294404969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9609282907429211059206625 7206962180571908294404969)
            ·
              refine ⟨5405221635428931220803727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7206962180571908294404969 5405221635428931220803727)
              ·
                refine ⟨8107832453143396831205591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5405221635428931220803727 8107832453143396831205591)
                ·
                  refine ⟨12161748679715095246808387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8107832453143396831205591 12161748679715095246808387)
                  ·
                    refine ⟨18242623019572642870212581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12161748679715095246808387 18242623019572642870212581)
                    ·
                      refine ⟨3420491816169870538164859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18242623019572642870212581 3420491816169870538164859)
                      ·
                        rfl

theorem cell23_6661384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 2, 1, 1, 1, 4].length) (baseStart_6661384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6661384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6661384 prefixEnd_6661384 := by exact prefixLift 6661384
  have htrace : WordTrace (prefixWord ++ tailWord_6661384) baseStart_6661384 baseEnd_6661384 := by
    simpa [prefixWord, tailWord_6661384, baseEnd_6661384] using wordTrace_append hprefix tailTrace_6661384
  have hstable : (prefixWord ++ tailWord_6661384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6661384).length < 2 ^ (prefixWord ++ tailWord_6661384).sum := by decide
  have hdescent : baseEnd_6661384 < baseStart_6661384 := by decide
  rcases family_descends (prefixWord ++ tailWord_6661384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6661387 : List Nat := [1, 1, 1, 1, 5, 3, 4, 1, 1, 2, 3]
def baseStart_6661387 : Nat := 118140960795 + 6661387 * 2 ^ 59
def prefixEnd_6661387 : Nat := 4983230072969 + 3 ^ 40 * 6661387 * 2
def baseEnd_6661387 : Nat := 3420493356611834026427345

theorem tailTrace_6661387 : CollatzResearch.WordTrace tailWord_6661387 prefixEnd_6661387 3420493356611834026427345 := by
  unfold tailWord_6661387
  simp only [CollatzResearch.WordTrace]
  refine ⟨242960743917940048169830415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161973829278626698779886943 242960743917940048169830415)
  ·
    refine ⟨364441115876910072254745623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242960743917940048169830415 364441115876910072254745623)
    ·
      refine ⟨546661673815365108382118435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 364441115876910072254745623 546661673815365108382118435)
      ·
        refine ⟨819992510723047662573177653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 546661673815365108382118435 819992510723047662573177653)
        ·
          refine ⟨76874297880285718366235405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 819992510723047662573177653 76874297880285718366235405)
          ·
            refine ⟨28827861705107144387338277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76874297880285718366235405 28827861705107144387338277)
            ·
              refine ⟨5405224069707589572625927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28827861705107144387338277 5405224069707589572625927)
              ·
                refine ⟨8107836104561384358938891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5405224069707589572625927 8107836104561384358938891)
                ·
                  refine ⟨12161754156842076538408337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8107836104561384358938891 12161754156842076538408337)
                  ·
                    refine ⟨9121315617631557403806253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12161754156842076538408337 9121315617631557403806253)
                    ·
                      refine ⟨3420493356611834026427345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9121315617631557403806253 3420493356611834026427345)
                      ·
                        rfl

theorem cell23_6661387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 4, 1, 1, 2, 3].length) (baseStart_6661387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6661387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6661387 prefixEnd_6661387 := by exact prefixLift 6661387
  have htrace : WordTrace (prefixWord ++ tailWord_6661387) baseStart_6661387 baseEnd_6661387 := by
    simpa [prefixWord, tailWord_6661387, baseEnd_6661387] using wordTrace_append hprefix tailTrace_6661387
  have hstable : (prefixWord ++ tailWord_6661387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6661387).length < 2 ^ (prefixWord ++ tailWord_6661387).sum := by decide
  have hdescent : baseEnd_6661387 < baseStart_6661387 := by decide
  rcases family_descends (prefixWord ++ tailWord_6661387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6661394 : List Nat := [3, 2, 4, 2, 1, 1, 1, 1, 4, 4]
def baseStart_6661394 : Nat := 118140960795 + 6661394 * 2 ^ 59
def prefixEnd_6661394 : Nat := 4983230072969 + 3 ^ 40 * 6661394 * 2
def baseEnd_6661394 : Nat := 1140165650325471833013271

theorem tailTrace_6661394 : CollatzResearch.WordTrace tailWord_6661394 prefixEnd_6661394 1140165650325471833013271 := by
  unfold tailWord_6661394
  simp only [CollatzResearch.WordTrace]
  refine ⟨60740249807228672091333809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161973999485943125576890157 60740249807228672091333809)
  ·
    refine ⟨45555187355421504068500357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60740249807228672091333809 45555187355421504068500357)
    ·
      refine ⟨8541597629141532012843817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45555187355421504068500357 8541597629141532012843817)
      ·
        refine ⟨6406198221856149009632863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8541597629141532012843817 6406198221856149009632863)
        ·
          refine ⟨9609297332784223514449295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6406198221856149009632863 9609297332784223514449295)
          ·
            refine ⟨14413945999176335271673943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9609297332784223514449295 14413945999176335271673943)
            ·
              refine ⟨21620918998764502907510915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14413945999176335271673943 21620918998764502907510915)
              ·
                refine ⟨32431378498146754361266373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21620918998764502907510915 32431378498146754361266373)
                ·
                  refine ⟨6080883468402516442737445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32431378498146754361266373 6080883468402516442737445)
                  ·
                    refine ⟨1140165650325471833013271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6080883468402516442737445 1140165650325471833013271)
                    ·
                      rfl

theorem cell23_6661394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_6661394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6661394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6661394 prefixEnd_6661394 := by exact prefixLift 6661394
  have htrace : WordTrace (prefixWord ++ tailWord_6661394) baseStart_6661394 baseEnd_6661394 := by
    simpa [prefixWord, tailWord_6661394, baseEnd_6661394] using wordTrace_append hprefix tailTrace_6661394
  have hstable : (prefixWord ++ tailWord_6661394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6661394).length < 2 ^ (prefixWord ++ tailWord_6661394).sum := by decide
  have hdescent : baseEnd_6661394 < baseStart_6661394 := by decide
  rcases family_descends (prefixWord ++ tailWord_6661394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6661427 : List Nat := [1, 1, 1, 2, 5, 2, 1, 4, 1, 3, 2]
def baseStart_6661427 : Nat := 118140960795 + 6661427 * 2 ^ 59
def prefixEnd_6661427 : Nat := 4983230072969 + 3 ^ 40 * 6661427 * 2
def baseEnd_6661427 : Nat := 3420513895838013869927161

theorem tailTrace_6661427 : CollatzResearch.WordTrace tailWord_6661427 prefixEnd_6661427 3420513895838013869927161 := by
  unfold tailWord_6661427
  simp only [CollatzResearch.WordTrace]
  refine ⟨242962202837795135001286535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161974801891863423334191023 242962202837795135001286535)
  ·
    refine ⟨364443304256692702501929803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242962202837795135001286535 364443304256692702501929803)
    ·
      refine ⟨546664956385039053752894705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 364443304256692702501929803 546664956385039053752894705)
      ·
        refine ⟨409998717288779290314671029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 546664956385039053752894705 409998717288779290314671029)
        ·
          refine ⟨38437379745823058467000409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 409998717288779290314671029 38437379745823058467000409)
          ·
            refine ⟨28828034809367293850250307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38437379745823058467000409 28828034809367293850250307)
            ·
              refine ⟨43242052214050940775375461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28828034809367293850250307 43242052214050940775375461)
              ·
                refine ⟨8107884790134551395382899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43242052214050940775375461 8107884790134551395382899)
                ·
                  refine ⟨12161827185201827093074349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8107884790134551395382899 12161827185201827093074349)
                  ·
                    refine ⟨4560685194450685159902881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12161827185201827093074349 4560685194450685159902881)
                    ·
                      refine ⟨3420513895838013869927161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4560685194450685159902881 3420513895838013869927161)
                      ·
                        rfl

theorem cell23_6661427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 4, 1, 3, 2].length) (baseStart_6661427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6661427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6661427 prefixEnd_6661427 := by exact prefixLift 6661427
  have htrace : WordTrace (prefixWord ++ tailWord_6661427) baseStart_6661427 baseEnd_6661427 := by
    simpa [prefixWord, tailWord_6661427, baseEnd_6661427] using wordTrace_append hprefix tailTrace_6661427
  have hstable : (prefixWord ++ tailWord_6661427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6661427).length < 2 ^ (prefixWord ++ tailWord_6661427).sum := by decide
  have hdescent : baseEnd_6661427 < baseStart_6661427 := by decide
  rcases family_descends (prefixWord ++ tailWord_6661427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6661440 : List Nat := [2, 1, 1, 2, 2, 1, 4, 1, 3, 4, 2]
def baseStart_6661440 : Nat := 118140960795 + 6661440 * 2 ^ 59
def prefixEnd_6661440 : Nat := 4983230072969 + 3 ^ 40 * 6661440 * 2
def baseEnd_6661440 : Nat := 3420520571086522319064601

theorem tailTrace_6661440 : CollatzResearch.WordTrace tailWord_6661440 prefixEnd_6661440 3420520571086522319064601 := by
  unfold tailWord_6661440
  simp only [CollatzResearch.WordTrace]
  refine ⟨121481338493374019110754887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161975117991165358814339849 121481338493374019110754887)
  ·
    refine ⟨182222007740061028666132331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121481338493374019110754887 182222007740061028666132331)
    ·
      refine ⟨273333011610091542999198497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182222007740061028666132331 273333011610091542999198497)
      ·
        refine ⟨204999758707568657249398873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 273333011610091542999198497 204999758707568657249398873)
        ·
          refine ⟨153749819030676492937049155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 204999758707568657249398873 153749819030676492937049155)
          ·
            refine ⟨230624728546014739405573733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153749819030676492937049155 230624728546014739405573733)
            ·
              refine ⟨43242136602377763638545075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 230624728546014739405573733 43242136602377763638545075)
              ·
                refine ⟨64863204903566645457817613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43242136602377763638545075 64863204903566645457817613)
                ·
                  refine ⟨24323701838837492046681605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64863204903566645457817613 24323701838837492046681605)
                  ·
                    refine ⟨4560694094782029758752801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24323701838837492046681605 4560694094782029758752801)
                    ·
                      refine ⟨3420520571086522319064601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4560694094782029758752801 3420520571086522319064601)
                      ·
                        rfl

theorem cell23_6661440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 1, 3, 4, 2].length) (baseStart_6661440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6661440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6661440 prefixEnd_6661440 := by exact prefixLift 6661440
  have htrace : WordTrace (prefixWord ++ tailWord_6661440) baseStart_6661440 baseEnd_6661440 := by
    simpa [prefixWord, tailWord_6661440, baseEnd_6661440] using wordTrace_append hprefix tailTrace_6661440
  have hstable : (prefixWord ++ tailWord_6661440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6661440).length < 2 ^ (prefixWord ++ tailWord_6661440).sum := by decide
  have hdescent : baseEnd_6661440 < baseStart_6661440 := by decide
  rcases family_descends (prefixWord ++ tailWord_6661440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6661443 : List Nat := [1, 1, 1, 3, 1, 3, 1, 2, 1, 6, 3]
def baseStart_6661443 : Nat := 118140960795 + 6661443 * 2 ^ 59
def prefixEnd_6661443 : Nat := 4983230072969 + 3 ^ 40 * 6661443 * 2
def baseEnd_6661443 : Nat := 3420522111528485807327087

theorem tailTrace_6661443 : CollatzResearch.WordTrace tailWord_6661443 prefixEnd_6661443 3420522111528485807327087 := by
  unfold tailWord_6661443
  simp only [CollatzResearch.WordTrace]
  refine ⟨242962786405737169733868983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161975190937158113155912655 242962786405737169733868983)
  ·
    refine ⟨364444179608605754600803475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242962786405737169733868983 364444179608605754600803475)
    ·
      refine ⟨546666269412908631901205213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 364444179608605754600803475 546666269412908631901205213)
      ·
        refine ⟨204999851029840736962951955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 546666269412908631901205213 204999851029840736962951955)
        ·
          refine ⟨307499776544761105444427933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204999851029840736962951955 307499776544761105444427933)
          ·
            refine ⟨115312416204285414541660475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 307499776544761105444427933 115312416204285414541660475)
            ·
              refine ⟨172968624306428121812490713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115312416204285414541660475 172968624306428121812490713)
              ·
                refine ⟨129726468229821091359368035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 172968624306428121812490713 129726468229821091359368035)
                ·
                  refine ⟨194589702344731637039052053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 129726468229821091359368035 194589702344731637039052053)
                  ·
                    refine ⟨9121392297409295486205565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 194589702344731637039052053 9121392297409295486205565)
                    ·
                      refine ⟨3420522111528485807327087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9121392297409295486205565 3420522111528485807327087)
                      ·
                        rfl

theorem cell23_6661443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 2, 1, 6, 3].length) (baseStart_6661443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6661443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6661443 prefixEnd_6661443 := by exact prefixLift 6661443
  have htrace : WordTrace (prefixWord ++ tailWord_6661443) baseStart_6661443 baseEnd_6661443 := by
    simpa [prefixWord, tailWord_6661443, baseEnd_6661443] using wordTrace_append hprefix tailTrace_6661443
  have hstable : (prefixWord ++ tailWord_6661443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6661443).length < 2 ^ (prefixWord ++ tailWord_6661443).sum := by decide
  have hdescent : baseEnd_6661443 < baseStart_6661443 := by decide
  rcases family_descends (prefixWord ++ tailWord_6661443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6661457 : List Nat := [1, 2, 2, 1, 4, 1, 1, 3, 4, 2, 2]
def baseStart_6661457 : Nat := 118140960795 + 6661457 * 2 ^ 59
def prefixEnd_6661457 : Nat := 4983230072969 + 3 ^ 40 * 6661457 * 2
def baseEnd_6661457 : Nat := 3420529300257648752552023

theorem tailTrace_6661457 : CollatzResearch.WordTrace tailWord_6661457 prefixEnd_6661457 3420529300257648752552023 := by
  unfold tailWord_6661457
  simp only [CollatzResearch.WordTrace]
  refine ⟨242963297027686450124878625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161975531351790966749919083 242963297027686450124878625)
  ·
    refine ⟨182222472770764837593658969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242963297027686450124878625 182222472770764837593658969)
    ·
      refine ⟨136666854578073628195244227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182222472770764837593658969 136666854578073628195244227)
      ·
        refine ⟨205000281867110442292866341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136666854578073628195244227 205000281867110442292866341)
        ·
          refine ⟨38437552850083207929912439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 205000281867110442292866341 38437552850083207929912439)
          ·
            refine ⟨57656329275124811894868659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38437552850083207929912439 57656329275124811894868659)
            ·
              refine ⟨86484493912687217842302989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57656329275124811894868659 86484493912687217842302989)
              ·
                refine ⟨32431685217257706690863621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86484493912687217842302989 32431685217257706690863621)
                ·
                  refine ⟨6080940978235820004536929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32431685217257706690863621 6080940978235820004536929)
                  ·
                    refine ⟨4560705733676865003402697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6080940978235820004536929 4560705733676865003402697)
                    ·
                      refine ⟨3420529300257648752552023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4560705733676865003402697 3420529300257648752552023)
                      ·
                        rfl

theorem cell23_6661457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 3, 4, 2, 2].length) (baseStart_6661457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6661457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6661457 prefixEnd_6661457 := by exact prefixLift 6661457
  have htrace : WordTrace (prefixWord ++ tailWord_6661457) baseStart_6661457 baseEnd_6661457 := by
    simpa [prefixWord, tailWord_6661457, baseEnd_6661457] using wordTrace_append hprefix tailTrace_6661457
  have hstable : (prefixWord ++ tailWord_6661457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6661457).length < 2 ^ (prefixWord ++ tailWord_6661457).sum := by decide
  have hdescent : baseEnd_6661457 < baseStart_6661457 := by decide
  rcases family_descends (prefixWord ++ tailWord_6661457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6661460 : List Nat := [2, 4, 1, 1, 2, 1, 2, 1, 2, 4, 3]
def baseStart_6661460 : Nat := 118140960795 + 6661460 * 2 ^ 59
def prefixEnd_6661460 : Nat := 4983230072969 + 3 ^ 40 * 6661460 * 2
def baseEnd_6661460 : Nat := 3420530840699612240814509

theorem tailTrace_6661460 : CollatzResearch.WordTrace tailWord_6661460 prefixEnd_6661460 3420530840699612240814509 := by
  unfold tailWord_6661460
  simp only [CollatzResearch.WordTrace]
  refine ⟨121481703223337790818618917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161975604297783721091491889 121481703223337790818618917)
  ·
    refine ⟨22777819354375835778491047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 121481703223337790818618917 22777819354375835778491047)
    ·
      refine ⟨34166729031563753667736571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22777819354375835778491047 34166729031563753667736571)
      ·
        refine ⟨51250093547345630501604857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34166729031563753667736571 51250093547345630501604857)
        ·
          refine ⟨38437570160509222876203643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51250093547345630501604857 38437570160509222876203643)
          ·
            refine ⟨57656355240763834314305465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38437570160509222876203643 57656355240763834314305465)
            ·
              refine ⟨43242266430572875735729099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57656355240763834314305465 43242266430572875735729099)
              ·
                refine ⟨64863399645859313603593649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43242266430572875735729099 64863399645859313603593649)
                ·
                  refine ⟨48647549734394485202695237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64863399645859313603593649 48647549734394485202695237)
                  ·
                    refine ⟨9121415575198965975505357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48647549734394485202695237 9121415575198965975505357)
                    ·
                      refine ⟨3420530840699612240814509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9121415575198965975505357 3420530840699612240814509)
                      ·
                        rfl

theorem cell23_6661460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 1, 2, 4, 3].length) (baseStart_6661460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6661460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6661460 prefixEnd_6661460 := by exact prefixLift 6661460
  have htrace : WordTrace (prefixWord ++ tailWord_6661460) baseStart_6661460 baseEnd_6661460 := by
    simpa [prefixWord, tailWord_6661460, baseEnd_6661460] using wordTrace_append hprefix tailTrace_6661460
  have hstable : (prefixWord ++ tailWord_6661460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6661460).length < 2 ^ (prefixWord ++ tailWord_6661460).sum := by decide
  have hdescent : baseEnd_6661460 < baseStart_6661460 := by decide
  rcases family_descends (prefixWord ++ tailWord_6661460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6661462 : List Nat := [5, 2, 3, 1, 2, 1, 2, 1, 2, 4]
def baseStart_6661462 : Nat := 118140960795 + 6661462 * 2 ^ 59
def prefixEnd_6661462 : Nat := 4983230072969 + 3 ^ 40 * 6661462 * 2
def baseEnd_6661462 : Nat := 1140177289220307077663167

theorem tailTrace_6661462 : CollatzResearch.WordTrace tailWord_6661462 prefixEnd_6661462 1140177289220307077663167 := by
  unfold tailWord_6661462
  simp only [CollatzResearch.WordTrace]
  refine ⟨15185217462041770998675665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 161975652928445557319207093 15185217462041770998675665)
  ·
    refine ⟨11388913096531328249006749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15185217462041770998675665 11388913096531328249006749)
    ·
      refine ⟨4270842411199248093377531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11388913096531328249006749 4270842411199248093377531)
      ·
        refine ⟨6406263616798872140066297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4270842411199248093377531 6406263616798872140066297)
        ·
          refine ⟨4804697712599154105049723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6406263616798872140066297 4804697712599154105049723)
          ·
            refine ⟨7207046568898731157574585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4804697712599154105049723 7207046568898731157574585)
            ·
              refine ⟨5405284926674048368180939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7207046568898731157574585 5405284926674048368180939)
              ·
                refine ⟨8107927390011072552271409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5405284926674048368180939 8107927390011072552271409)
                ·
                  refine ⟨6080945542508304414203557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8107927390011072552271409 6080945542508304414203557)
                  ·
                    refine ⟨1140177289220307077663167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6080945542508304414203557 1140177289220307077663167)
                    ·
                      rfl

theorem cell23_6661462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_6661462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6661462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6661462 prefixEnd_6661462 := by exact prefixLift 6661462
  have htrace : WordTrace (prefixWord ++ tailWord_6661462) baseStart_6661462 baseEnd_6661462 := by
    simpa [prefixWord, tailWord_6661462, baseEnd_6661462] using wordTrace_append hprefix tailTrace_6661462
  have hstable : (prefixWord ++ tailWord_6661462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6661462).length < 2 ^ (prefixWord ++ tailWord_6661462).sum := by decide
  have hdescent : baseEnd_6661462 < baseStart_6661462 := by decide
  rcases family_descends (prefixWord ++ tailWord_6661462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6661530 : List Nat := [3, 1, 1, 4, 1, 1, 2, 2, 1, 3, 4]
def baseStart_6661530 : Nat := 118140960795 + 6661530 * 2 ^ 59
def prefixEnd_6661530 : Nat := 4983230072969 + 3 ^ 40 * 6661530 * 2
def baseEnd_6661530 : Nat := 3420566784345426966939187

theorem tailTrace_6661530 : CollatzResearch.WordTrace tailWord_6661530 prefixEnd_6661530 3420566784345426966939187 := by
  unfold tailWord_6661530
  simp only [CollatzResearch.WordTrace]
  refine ⟨60741489889105495898071511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161977306370947989061524029 60741489889105495898071511)
  ·
    refine ⟨91112234833658243847107267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60741489889105495898071511 91112234833658243847107267)
    ·
      refine ⟨136668352250487365770660901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91112234833658243847107267 136668352250487365770660901)
      ·
        refine ⟨25625316046966381081998919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 136668352250487365770660901 25625316046966381081998919)
        ·
          refine ⟨38437974070449571622998379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25625316046966381081998919 38437974070449571622998379)
          ·
            refine ⟨57656961105674357434497569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38437974070449571622998379 57656961105674357434497569)
            ·
              refine ⟨43242720829255768075873177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57656961105674357434497569 43242720829255768075873177)
              ·
                refine ⟨32432040621941826056904883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43242720829255768075873177 32432040621941826056904883)
                ·
                  refine ⟨48648060932912739085357325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32432040621941826056904883 48648060932912739085357325)
                  ·
                    refine ⟨18243022849842277157008997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48648060932912739085357325 18243022849842277157008997)
                    ·
                      refine ⟨3420566784345426966939187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18243022849842277157008997 3420566784345426966939187)
                      ·
                        rfl

theorem cell23_6661530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_6661530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6661530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6661530 prefixEnd_6661530 := by exact prefixLift 6661530
  have htrace : WordTrace (prefixWord ++ tailWord_6661530) baseStart_6661530 baseEnd_6661530 := by
    simpa [prefixWord, tailWord_6661530, baseEnd_6661530] using wordTrace_append hprefix tailTrace_6661530
  have hstable : (prefixWord ++ tailWord_6661530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6661530).length < 2 ^ (prefixWord ++ tailWord_6661530).sum := by decide
  have hdescent : baseEnd_6661530 < baseStart_6661530 := by decide
  rcases family_descends (prefixWord ++ tailWord_6661530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6661617 : List Nat := [1, 2, 2, 2, 3, 2, 2, 3, 1, 5]
def baseStart_6661617 : Nat := 118140960795 + 6661617 * 2 ^ 59
def prefixEnd_6661617 : Nat := 4983230072969 + 3 ^ 40 * 6661617 * 2
def baseEnd_6661617 : Nat := 1140203819054122708850429

theorem tailTrace_6661617 : CollatzResearch.WordTrace tailWord_6661617 prefixEnd_6661617 1140203819054122708850429 := by
  unfold tailWord_6661617
  simp only [CollatzResearch.WordTrace]
  refine ⟨242969132707106797450703105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161979421804737864967135403 242969132707106797450703105)
  ·
    refine ⟨182226849530330098088027329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242969132707106797450703105 182226849530330098088027329)
    ·
      refine ⟨136670137147747573566020497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182226849530330098088027329 136670137147747573566020497)
      ·
        refine ⟨102502602860810680174515373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136670137147747573566020497 102502602860810680174515373)
        ·
          refine ⟨38438476072804005065443265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102502602860810680174515373 38438476072804005065443265)
          ·
            refine ⟨28828857054603003799082449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38438476072804005065443265 28828857054603003799082449)
            ·
              refine ⟨21621642790952252849311837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28828857054603003799082449 21621642790952252849311837)
              ·
                refine ⟨8108116046607094818491939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21621642790952252849311837 8108116046607094818491939)
                ·
                  refine ⟨12162174069910642227737909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8108116046607094818491939 12162174069910642227737909)
                  ·
                    refine ⟨1140203819054122708850429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12162174069910642227737909 1140203819054122708850429)
                    ·
                      rfl

theorem cell23_6661617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 3, 1, 5].length) (baseStart_6661617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6661617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6661617 prefixEnd_6661617 := by exact prefixLift 6661617
  have htrace : WordTrace (prefixWord ++ tailWord_6661617) baseStart_6661617 baseEnd_6661617 := by
    simpa [prefixWord, tailWord_6661617, baseEnd_6661617] using wordTrace_append hprefix tailTrace_6661617
  have hstable : (prefixWord ++ tailWord_6661617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6661617).length < 2 ^ (prefixWord ++ tailWord_6661617).sum := by decide
  have hdescent : baseEnd_6661617 < baseStart_6661617 := by decide
  rcases family_descends (prefixWord ++ tailWord_6661617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6661624 : List Nat := [2, 1, 2, 1, 1, 6, 1, 2, 2, 3, 2]
def baseStart_6661624 : Nat := 118140960795 + 6661624 * 2 ^ 59
def prefixEnd_6661624 : Nat := 4983230072969 + 3 ^ 40 * 6661624 * 2
def baseEnd_6661624 : Nat := 3420615051526949599163755

theorem tailTrace_6661624 : CollatzResearch.WordTrace tailWord_6661624 prefixEnd_6661624 3420615051526949599163755 := by
  unfold tailWord_6661624
  simp only [CollatzResearch.WordTrace]
  refine ⟨121484694009040718823103963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161979592012054291764138617 121484694009040718823103963)
  ·
    refine ⟨182227041013561078234655945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121484694009040718823103963 182227041013561078234655945)
    ·
      refine ⟨136670280760170808675991959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182227041013561078234655945 136670280760170808675991959)
      ·
        refine ⟨205005421140256213013987939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136670280760170808675991959 205005421140256213013987939)
        ·
          refine ⟨307508131710384319520981909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205005421140256213013987939 307508131710384319520981909)
          ·
            refine ⟨14414443673924264977546027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 307508131710384319520981909 14414443673924264977546027)
            ·
              refine ⟨21621665510886397466319041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14414443673924264977546027 21621665510886397466319041)
              ·
                refine ⟨16216249133164798099739281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21621665510886397466319041 16216249133164798099739281)
                ·
                  refine ⟨12162186849873598574804461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16216249133164798099739281 12162186849873598574804461)
                  ·
                    refine ⟨4560820068702599465551673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12162186849873598574804461 4560820068702599465551673)
                    ·
                      refine ⟨3420615051526949599163755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4560820068702599465551673 3420615051526949599163755)
                      ·
                        rfl

theorem cell23_6661624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 2, 2, 3, 2].length) (baseStart_6661624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6661624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6661624 prefixEnd_6661624 := by exact prefixLift 6661624
  have htrace : WordTrace (prefixWord ++ tailWord_6661624) baseStart_6661624 baseEnd_6661624 := by
    simpa [prefixWord, tailWord_6661624, baseEnd_6661624] using wordTrace_append hprefix tailTrace_6661624
  have hstable : (prefixWord ++ tailWord_6661624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6661624).length < 2 ^ (prefixWord ++ tailWord_6661624).sum := by decide
  have hdescent : baseEnd_6661624 < baseStart_6661624 := by decide
  rcases family_descends (prefixWord ++ tailWord_6661624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6661638 : List Nat := [6, 2, 1, 1, 2, 1, 1, 3, 6]
def baseStart_6661638 : Nat := 118140960795 + 6661638 * 2 ^ 59
def prefixEnd_6661638 : Nat := 4983230072969 + 3 ^ 40 * 6661638 * 2
def baseEnd_6661638 : Nat := 380069137806234727154299

theorem tailTrace_6661638 : CollatzResearch.WordTrace tailWord_6661638 prefixEnd_6661638 380069137806234727154299 := by
  unfold tailWord_6661638
  simp only [CollatzResearch.WordTrace]
  refine ⟨7592809332500959938663049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 161979932426687145358145045 7592809332500959938663049)
  ·
    refine ⟨5694606999375719953997287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7592809332500959938663049 5694606999375719953997287)
    ·
      refine ⟨8541910499063579930995931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5694606999375719953997287 8541910499063579930995931)
      ·
        refine ⟨12812865748595369896493897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8541910499063579930995931 12812865748595369896493897)
        ·
          refine ⟨9609649311446527422370423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12812865748595369896493897 9609649311446527422370423)
          ·
            refine ⟨14414473967169791133555635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9609649311446527422370423 14414473967169791133555635)
            ·
              refine ⟨21621710950754686700333453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14414473967169791133555635 21621710950754686700333453)
              ·
                refine ⟨8108141606533007512625045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21621710950754686700333453 8108141606533007512625045)
                ·
                  refine ⟨380069137806234727154299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8108141606533007512625045 380069137806234727154299)
                  ·
                    rfl

theorem cell23_6661638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 3, 6].length) (baseStart_6661638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6661638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6661638 prefixEnd_6661638 := by exact prefixLift 6661638
  have htrace : WordTrace (prefixWord ++ tailWord_6661638) baseStart_6661638 baseEnd_6661638 := by
    simpa [prefixWord, tailWord_6661638, baseEnd_6661638] using wordTrace_append hprefix tailTrace_6661638
  have hstable : (prefixWord ++ tailWord_6661638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6661638).length < 2 ^ (prefixWord ++ tailWord_6661638).sum := by decide
  have hdescent : baseEnd_6661638 < baseStart_6661638 := by decide
  rcases family_descends (prefixWord ++ tailWord_6661638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6661660 : List Nat := [2, 2, 3, 1, 2, 1, 1, 11]
def baseStart_6661660 : Nat := 118140960795 + 6661660 * 2 ^ 59
def prefixEnd_6661660 : Nat := 4983230072969 + 3 ^ 40 * 6661660 * 2
def baseEnd_6661660 : Nat := 126690130993722646604207

theorem tailTrace_6661660 : CollatzResearch.WordTrace tailWord_6661660 prefixEnd_6661660 126690130993722646604207 := by
  unfold tailWord_6661660
  simp only [CollatzResearch.WordTrace]
  refine ⟨121485350522975507897259217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161980467363967343863012289 121485350522975507897259217)
  ·
    refine ⟨91114012892231630922944413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121485350522975507897259217 91114012892231630922944413)
    ·
      refine ⟨34167754834586861596104155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91114012892231630922944413 34167754834586861596104155)
      ·
        refine ⟨51251632251880292394156233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34167754834586861596104155 51251632251880292394156233)
        ·
          refine ⟨38438724188910219295617175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51251632251880292394156233 38438724188910219295617175)
          ·
            refine ⟨57658086283365328943425763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38438724188910219295617175 57658086283365328943425763)
            ·
              refine ⟨86487129425047993415138645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57658086283365328943425763 86487129425047993415138645)
              ·
                refine ⟨126690130993722646604207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 86487129425047993415138645 126690130993722646604207)
                ·
                  rfl

theorem cell23_6661660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 11].length) (baseStart_6661660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6661660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6661660 prefixEnd_6661660 := by exact prefixLift 6661660
  have htrace : WordTrace (prefixWord ++ tailWord_6661660) baseStart_6661660 baseEnd_6661660 := by
    simpa [prefixWord, tailWord_6661660, baseEnd_6661660] using wordTrace_append hprefix tailTrace_6661660
  have hstable : (prefixWord ++ tailWord_6661660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6661660).length < 2 ^ (prefixWord ++ tailWord_6661660).sum := by decide
  have hdescent : baseEnd_6661660 < baseStart_6661660 := by decide
  rcases family_descends (prefixWord ++ tailWord_6661660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6661677 : List Nat := [1, 5, 4, 13]
def baseStart_6661677 : Nat := 118140960795 + 6661677 * 2 ^ 59
def prefixEnd_6661677 : Nat := 4983230072969 + 3 ^ 40 * 6661677 * 2
def baseEnd_6661677 : Nat := 1564079682671073567353

theorem tailTrace_6661677 : CollatzResearch.WordTrace tailWord_6661677 prefixEnd_6661677 1564079682671073567353 := by
  unfold tailWord_6661677
  simp only [CollatzResearch.WordTrace]
  refine ⟨242971321086889427697887285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161980880724592951798591523 242971321086889427697887285)
  ·
    refine ⟨22778561351895883846676933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 242971321086889427697887285 22778561351895883846676933)
    ·
      refine ⟨4270980253480478221251925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22778561351895883846676933 4270980253480478221251925)
      ·
        refine ⟨1564079682671073567353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 13 4270980253480478221251925 1564079682671073567353)
        ·
          rfl

theorem cell23_6661677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 13].length) (baseStart_6661677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6661677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6661677 prefixEnd_6661677 := by exact prefixLift 6661677
  have htrace : WordTrace (prefixWord ++ tailWord_6661677) baseStart_6661677 baseEnd_6661677 := by
    simpa [prefixWord, tailWord_6661677, baseEnd_6661677] using wordTrace_append hprefix tailTrace_6661677
  have hstable : (prefixWord ++ tailWord_6661677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6661677).length < 2 ^ (prefixWord ++ tailWord_6661677).sum := by decide
  have hdescent : baseEnd_6661677 < baseStart_6661677 := by decide
  rcases family_descends (prefixWord ++ tailWord_6661677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6661688 : List Nat := [2, 1, 2, 1, 4, 3, 1, 4, 1, 2, 2]
def baseStart_6661688 : Nat := 118140960795 + 6661688 * 2 ^ 59
def prefixEnd_6661688 : Nat := 4983230072969 + 3 ^ 40 * 6661688 * 2
def baseEnd_6661688 : Nat := 3420647914288837348763461

theorem tailTrace_6661688 : CollatzResearch.WordTrace tailWord_6661688 prefixEnd_6661688 3420647914288837348763461 := by
  unfold tailWord_6661688
  simp only [CollatzResearch.WordTrace]
  refine ⟨121485861144924788288268859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161981148193233051051025145 121485861144924788288268859)
  ·
    refine ⟨182228791717387182432403289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121485861144924788288268859 182228791717387182432403289)
    ·
      refine ⟨136671593788040386824302467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182228791717387182432403289 136671593788040386824302467)
      ·
        refine ⟨205007390682060580236453701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136671593788040386824302467 205007390682060580236453701)
        ·
          refine ⟨38438885752886358794335069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 205007390682060580236453701 38438885752886358794335069)
          ·
            refine ⟨14414582157332384547875651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38438885752886358794335069 14414582157332384547875651)
            ·
              refine ⟨21621873235998576821813477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14414582157332384547875651 21621873235998576821813477)
              ·
                refine ⟨4054101231749733154090027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21621873235998576821813477 4054101231749733154090027)
                ·
                  refine ⟨6081151847624599731135041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4054101231749733154090027 6081151847624599731135041)
                  ·
                    refine ⟨4560863885718449798351281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6081151847624599731135041 4560863885718449798351281)
                    ·
                      refine ⟨3420647914288837348763461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4560863885718449798351281 3420647914288837348763461)
                      ·
                        rfl

theorem cell23_6661688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 4, 1, 2, 2].length) (baseStart_6661688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6661688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6661688 prefixEnd_6661688 := by exact prefixLift 6661688
  have htrace : WordTrace (prefixWord ++ tailWord_6661688) baseStart_6661688 baseEnd_6661688 := by
    simpa [prefixWord, tailWord_6661688, baseEnd_6661688] using wordTrace_append hprefix tailTrace_6661688
  have hstable : (prefixWord ++ tailWord_6661688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6661688).length < 2 ^ (prefixWord ++ tailWord_6661688).sum := by decide
  have hdescent : baseEnd_6661688 < baseStart_6661688 := by decide
  rcases family_descends (prefixWord ++ tailWord_6661688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6661690 : List Nat := [3, 1, 1, 1, 3, 2, 1, 1, 1, 9]
def baseStart_6661690 : Nat := 118140960795 + 6661690 * 2 ^ 59
def prefixEnd_6661690 : Nat := 4983230072969 + 3 ^ 40 * 6661690 * 2
def baseEnd_6661690 : Nat := 1140216313750048780312817

theorem tailTrace_6661690 : CollatzResearch.WordTrace tailWord_6661690 prefixEnd_6661690 1140216313750048780312817 := by
  unfold tailWord_6661690
  simp only [CollatzResearch.WordTrace]
  refine ⟨60742948808960582729527631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161981196823894887278740349 60742948808960582729527631)
  ·
    refine ⟨91114423213440874094291447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60742948808960582729527631 91114423213440874094291447)
    ·
      refine ⟨136671634820161311141437171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91114423213440874094291447 136671634820161311141437171)
      ·
        refine ⟨205007452230241966712155757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136671634820161311141437171 205007452230241966712155757)
        ·
          refine ⟨76877794586340737517058409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 205007452230241966712155757 76877794586340737517058409)
          ·
            refine ⟨57658345939755553137793807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76877794586340737517058409 57658345939755553137793807)
            ·
              refine ⟨86487518909633329706690711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57658345939755553137793807 86487518909633329706690711)
              ·
                refine ⟨129731278364449994560036067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86487518909633329706690711 129731278364449994560036067)
                ·
                  refine ⟨194596917546674991840054101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 129731278364449994560036067 194596917546674991840054101)
                  ·
                    refine ⟨1140216313750048780312817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 194596917546674991840054101 1140216313750048780312817)
                    ·
                      rfl

theorem cell23_6661690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 1, 1, 9].length) (baseStart_6661690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6661690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6661690 prefixEnd_6661690 := by exact prefixLift 6661690
  have htrace : WordTrace (prefixWord ++ tailWord_6661690) baseStart_6661690 baseEnd_6661690 := by
    simpa [prefixWord, tailWord_6661690, baseEnd_6661690] using wordTrace_append hprefix tailTrace_6661690
  have hstable : (prefixWord ++ tailWord_6661690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6661690).length < 2 ^ (prefixWord ++ tailWord_6661690).sum := by decide
  have hdescent : baseEnd_6661690 < baseStart_6661690 := by decide
  rcases family_descends (prefixWord ++ tailWord_6661690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6661720 : List Nat := [2, 1, 2, 2, 1, 2, 1, 1, 3, 8]
def baseStart_6661720 : Nat := 118140960795 + 6661720 * 2 ^ 59
def prefixEnd_6661720 : Nat := 4983230072969 + 3 ^ 40 * 6661720 * 2
def baseEnd_6661720 : Nat := 1140221448556593741187771

theorem tailTrace_6661720 : CollatzResearch.WordTrace tailWord_6661720 prefixEnd_6661720 1140221448556593741187771 := by
  unfold tailWord_6661720
  simp only [CollatzResearch.WordTrace]
  refine ⟨121486444712866823020851307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161981926283822430694468409 121486444712866823020851307)
  ·
    refine ⟨182229667069300234531276961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121486444712866823020851307 182229667069300234531276961)
    ·
      refine ⟨136672250301975175898457721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182229667069300234531276961 136672250301975175898457721)
      ·
        refine ⟨102504187726481381923843291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136672250301975175898457721 102504187726481381923843291)
        ·
          refine ⟨153756281589722072885764937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102504187726481381923843291 153756281589722072885764937)
          ·
            refine ⟨115317211192291554664323703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153756281589722072885764937 115317211192291554664323703)
            ·
              refine ⟨172975816788437331996485555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115317211192291554664323703 172975816788437331996485555)
              ·
                refine ⟨259463725182655997994728333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 172975816788437331996485555 259463725182655997994728333)
                ·
                  refine ⟨97298896943495999248023125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 259463725182655997994728333 97298896943495999248023125)
                  ·
                    refine ⟨1140221448556593741187771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 97298896943495999248023125 1140221448556593741187771)
                    ·
                      rfl

theorem cell23_6661720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 3, 8].length) (baseStart_6661720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6661720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6661720 prefixEnd_6661720 := by exact prefixLift 6661720
  have htrace : WordTrace (prefixWord ++ tailWord_6661720) baseStart_6661720 baseEnd_6661720 := by
    simpa [prefixWord, tailWord_6661720, baseEnd_6661720] using wordTrace_append hprefix tailTrace_6661720
  have hstable : (prefixWord ++ tailWord_6661720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6661720).length < 2 ^ (prefixWord ++ tailWord_6661720).sum := by decide
  have hdescent : baseEnd_6661720 < baseStart_6661720 := by decide
  rcases family_descends (prefixWord ++ tailWord_6661720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6661731 : List Nat := [1, 1, 1, 5, 1, 4, 1, 3, 1, 3, 2]
def baseStart_6661731 : Nat := 118140960795 + 6661731 * 2 ^ 59
def prefixEnd_6661731 : Nat := 4983230072969 + 3 ^ 40 * 6661731 * 2
def baseEnd_6661731 : Nat := 3420669993956980680525763

theorem tailTrace_6661731 : CollatzResearch.WordTrace tailWord_6661731 prefixEnd_6661731 3420669993956980680525763 := by
  unfold tailWord_6661731
  simp only [CollatzResearch.WordTrace]
  refine ⟨242973290628693794920353047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161982193752462529946902031 242973290628693794920353047)
  ·
    refine ⟨364459935943040692380529571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242973290628693794920353047 364459935943040692380529571)
    ·
      refine ⟨546689903914561038570794357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 364459935943040692380529571 546689903914561038570794357)
      ·
        refine ⟨51252178491990097366011971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 546689903914561038570794357 51252178491990097366011971)
        ·
          refine ⟨76878267737985146049017957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51252178491990097366011971 76878267737985146049017957)
          ·
            refine ⟨14414675200872214884190867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76878267737985146049017957 14414675200872214884190867)
            ·
              refine ⟨21622012801308322326286301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14414675200872214884190867 21622012801308322326286301)
              ·
                refine ⟨8108254800490620872357363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21622012801308322326286301 8108254800490620872357363)
                ·
                  refine ⟨12162382200735931308536045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8108254800490620872357363 12162382200735931308536045)
                  ·
                    refine ⟨4560893325275974240701017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12162382200735931308536045 4560893325275974240701017)
                    ·
                      refine ⟨3420669993956980680525763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4560893325275974240701017 3420669993956980680525763)
                      ·
                        rfl

theorem cell23_6661731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 3, 1, 3, 2].length) (baseStart_6661731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6661731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6661731 prefixEnd_6661731 := by exact prefixLift 6661731
  have htrace : WordTrace (prefixWord ++ tailWord_6661731) baseStart_6661731 baseEnd_6661731 := by
    simpa [prefixWord, tailWord_6661731, baseEnd_6661731] using wordTrace_append hprefix tailTrace_6661731
  have hstable : (prefixWord ++ tailWord_6661731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6661731).length < 2 ^ (prefixWord ++ tailWord_6661731).sum := by decide
  have hdescent : baseEnd_6661731 < baseStart_6661731 := by decide
  rcases family_descends (prefixWord ++ tailWord_6661731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6661738 : List Nat := [3, 1, 3, 2, 1, 4, 1, 2, 2, 1, 3]
def baseStart_6661738 : Nat := 118140960795 + 6661738 * 2 ^ 59
def prefixEnd_6661738 : Nat := 4983230072969 + 3 ^ 40 * 6661738 * 2
def baseEnd_6661738 : Nat := 3420673588321562153138231

theorem tailTrace_6661738 : CollatzResearch.WordTrace tailWord_6661738 prefixEnd_6661738 3420673588321562153138231 := by
  unfold tailWord_6661738
  simp only [CollatzResearch.WordTrace]
  refine ⟨60743386484917108778964467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161982363959778956743905245 60743386484917108778964467)
  ·
    refine ⟨91115079727375663168446701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60743386484917108778964467 91115079727375663168446701)
    ·
      refine ⟨34168154897765873688167513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91115079727375663168446701 34168154897765873688167513)
      ·
        refine ⟨25626116173324405266125635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34168154897765873688167513 25626116173324405266125635)
        ·
          refine ⟨38439174259986607899188453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25626116173324405266125635 38439174259986607899188453)
          ·
            refine ⟨7207345173747488981097835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38439174259986607899188453 7207345173747488981097835)
            ·
              refine ⟨10811017760621233471646753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7207345173747488981097835 10811017760621233471646753)
              ·
                refine ⟨8108263320465925103735065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10811017760621233471646753 8108263320465925103735065)
                ·
                  refine ⟨6081197490349443827801299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8108263320465925103735065 6081197490349443827801299)
                  ·
                    refine ⟨9121796235524165741701949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6081197490349443827801299 9121796235524165741701949)
                    ·
                      refine ⟨3420673588321562153138231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9121796235524165741701949 3420673588321562153138231)
                      ·
                        rfl

theorem cell23_6661738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 1, 2, 2, 1, 3].length) (baseStart_6661738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6661738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6661738 prefixEnd_6661738 := by exact prefixLift 6661738
  have htrace : WordTrace (prefixWord ++ tailWord_6661738) baseStart_6661738 baseEnd_6661738 := by
    simpa [prefixWord, tailWord_6661738, baseEnd_6661738] using wordTrace_append hprefix tailTrace_6661738
  have hstable : (prefixWord ++ tailWord_6661738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6661738).length < 2 ^ (prefixWord ++ tailWord_6661738).sum := by decide
  have hdescent : baseEnd_6661738 < baseStart_6661738 := by decide
  rcases family_descends (prefixWord ++ tailWord_6661738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6661761 : List Nat := [1, 2, 4, 2, 1, 2, 3, 1, 1, 4, 2]
def baseStart_6661761 : Nat := 118140960795 + 6661761 * 2 ^ 59
def prefixEnd_6661761 : Nat := 4983230072969 + 3 ^ 40 * 6661761 * 2
def baseEnd_6661761 : Nat := 3420685398376615563150625

theorem tailTrace_6661761 : CollatzResearch.WordTrace tailWord_6661761 prefixEnd_6661761 3420685398376615563150625 := by
  unfold tailWord_6661761
  simp only [CollatzResearch.WordTrace]
  refine ⟨242974384818585110043945137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161982923212390073362630091 242974384818585110043945137)
  ·
    refine ⟨182230788613938832532958853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242974384818585110043945137 182230788613938832532958853)
    ·
      refine ⟨34168272865113531099929785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 182230788613938832532958853 34168272865113531099929785)
      ·
        refine ⟨25626204648835148324947339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34168272865113531099929785 25626204648835148324947339)
        ·
          refine ⟨38439306973252722487421009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25626204648835148324947339 38439306973252722487421009)
          ·
            refine ⟨28829480229939541865565757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38439306973252722487421009 28829480229939541865565757)
            ·
              refine ⟨10811055086227328199587159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28829480229939541865565757 10811055086227328199587159)
              ·
                refine ⟨16216582629340992299380739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10811055086227328199587159 16216582629340992299380739)
                ·
                  refine ⟨24324873944011488449071109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16216582629340992299380739 24324873944011488449071109)
                  ·
                    refine ⟨4560913864502154084200833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24324873944011488449071109 4560913864502154084200833)
                    ·
                      refine ⟨3420685398376615563150625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4560913864502154084200833 3420685398376615563150625)
                      ·
                        rfl

theorem cell23_6661761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 3, 1, 1, 4, 2].length) (baseStart_6661761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6661761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6661761 prefixEnd_6661761 := by exact prefixLift 6661761
  have htrace : WordTrace (prefixWord ++ tailWord_6661761) baseStart_6661761 baseEnd_6661761 := by
    simpa [prefixWord, tailWord_6661761, baseEnd_6661761] using wordTrace_append hprefix tailTrace_6661761
  have hstable : (prefixWord ++ tailWord_6661761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6661761).length < 2 ^ (prefixWord ++ tailWord_6661761).sum := by decide
  have hdescent : baseEnd_6661761 < baseStart_6661761 := by decide
  rcases family_descends (prefixWord ++ tailWord_6661761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6661767 : List Nat := [1, 1, 4, 2, 1, 3, 2, 2, 7]
def baseStart_6661767 : Nat := 118140960795 + 6661767 * 2 ^ 59
def prefixEnd_6661767 : Nat := 4983230072969 + 3 ^ 40 * 6661767 * 2
def baseEnd_6661767 : Nat := 380076497695615837741733

theorem tailTrace_6661767 : CollatzResearch.WordTrace tailWord_6661767 prefixEnd_6661767 380076497695615837741733 := by
  unfold tailWord_6661767
  simp only [CollatzResearch.WordTrace]
  refine ⟨242974603656563373068663555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161983069104375582045775703 242974603656563373068663555)
  ·
    refine ⟨364461905484845059602995333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242974603656563373068663555 364461905484845059602995333)
    ·
      refine ⟨68336607278408448675561625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 364461905484845059602995333 68336607278408448675561625)
      ·
        refine ⟨51252455458806336506671219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68336607278408448675561625 51252455458806336506671219)
        ·
          refine ⟨76878683188209504760006829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51252455458806336506671219 76878683188209504760006829)
          ·
            refine ⟨28829506195578564285002561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76878683188209504760006829 28829506195578564285002561)
            ·
              refine ⟨21622129646683923213751921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28829506195578564285002561 21622129646683923213751921)
              ·
                refine ⟨16216597235012942410313941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21622129646683923213751921 16216597235012942410313941)
                ·
                  refine ⟨380076497695615837741733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16216597235012942410313941 380076497695615837741733)
                  ·
                    rfl

theorem cell23_6661767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 2, 7].length) (baseStart_6661767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6661767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6661767 prefixEnd_6661767 := by exact prefixLift 6661767
  have htrace : WordTrace (prefixWord ++ tailWord_6661767) baseStart_6661767 baseEnd_6661767 := by
    simpa [prefixWord, tailWord_6661767, baseEnd_6661767] using wordTrace_append hprefix tailTrace_6661767
  have hstable : (prefixWord ++ tailWord_6661767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6661767).length < 2 ^ (prefixWord ++ tailWord_6661767).sum := by decide
  have hdescent : baseEnd_6661767 < baseStart_6661767 := by decide
  rcases family_descends (prefixWord ++ tailWord_6661767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6661777 : List Nat := [1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 3]
def baseStart_6661777 : Nat := 118140960795 + 6661777 * 2 ^ 59
def prefixEnd_6661777 : Nat := 4983230072969 + 3 ^ 40 * 6661777 * 2
def baseEnd_6661777 : Nat := 3420693614067087500550551

theorem tailTrace_6661777 : CollatzResearch.WordTrace tailWord_6661777 prefixEnd_6661777 3420693614067087500550551 := by
  unfold tailWord_6661777
  simp only [CollatzResearch.WordTrace]
  refine ⟨242974968386527144776527585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161983312257684763184351723 242974968386527144776527585)
  ·
    refine ⟨182231226289895358582395689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242974968386527144776527585 182231226289895358582395689)
    ·
      refine ⟨136673419717421518936796767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182231226289895358582395689 136673419717421518936796767)
      ·
        refine ⟨205010129576132278405195151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136673419717421518936796767 205010129576132278405195151)
        ·
          refine ⟨307515194364198417607792727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205010129576132278405195151 307515194364198417607792727)
          ·
            refine ⟨461272791546297626411689091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 307515194364198417607792727 461272791546297626411689091)
            ·
              refine ⟨691909187319446439617533637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 461272791546297626411689091 691909187319446439617533637)
              ·
                refine ⟨129732972622396207428287557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 691909187319446439617533637 129732972622396207428287557)
                ·
                  refine ⟨24324932366699288892803917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 129732972622396207428287557 24324932366699288892803917)
                  ·
                    refine ⟨9121849637512233334801469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24324932366699288892803917 9121849637512233334801469)
                    ·
                      refine ⟨3420693614067087500550551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9121849637512233334801469 3420693614067087500550551)
                      ·
                        rfl

theorem cell23_6661777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 3].length) (baseStart_6661777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6661777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6661777 prefixEnd_6661777 := by exact prefixLift 6661777
  have htrace : WordTrace (prefixWord ++ tailWord_6661777) baseStart_6661777 baseEnd_6661777 := by
    simpa [prefixWord, tailWord_6661777, baseEnd_6661777] using wordTrace_append hprefix tailTrace_6661777
  have hstable : (prefixWord ++ tailWord_6661777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6661777).length < 2 ^ (prefixWord ++ tailWord_6661777).sum := by decide
  have hdescent : baseEnd_6661777 < baseStart_6661777 := by decide
  rcases family_descends (prefixWord ++ tailWord_6661777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6661797 : List Nat := [1, 3, 1, 2, 1, 2, 3, 1, 4, 5]
def baseStart_6661797 : Nat := 118140960795 + 6661797 * 2 ^ 59
def prefixEnd_6661797 : Nat := 4983230072969 + 3 ^ 40 * 6661797 * 2
def baseEnd_6661797 : Nat := 1140234627893392474100153

theorem tailTrace_6661797 : CollatzResearch.WordTrace tailWord_6661797 prefixEnd_6661797 1140234627893392474100153 := by
  unfold tailWord_6661797
  simp only [CollatzResearch.WordTrace]
  refine ⟨242975697846454688192255645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161983798564303125461503763 242975697846454688192255645)
  ·
    refine ⟨91115886692420508072095867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 242975697846454688192255645 91115886692420508072095867)
    ·
      refine ⟨136673830038630762108143801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91115886692420508072095867 136673830038630762108143801)
      ·
        refine ⟨102505372528973071581107851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136673830038630762108143801 102505372528973071581107851)
        ·
          refine ⟨153758058793459607371661777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102505372528973071581107851 153758058793459607371661777)
          ·
            refine ⟨115318544095094705528746333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153758058793459607371661777 115318544095094705528746333)
            ·
              refine ⟨43244454035660514573279875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 115318544095094705528746333 43244454035660514573279875)
              ·
                refine ⟨64866681053490771859919813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43244454035660514573279875 64866681053490771859919813)
                ·
                  refine ⟨12162502697529519723734965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64866681053490771859919813 12162502697529519723734965)
                  ·
                    refine ⟨1140234627893392474100153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12162502697529519723734965 1140234627893392474100153)
                    ·
                      rfl

theorem cell23_6661797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 1, 4, 5].length) (baseStart_6661797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6661797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6661797 prefixEnd_6661797 := by exact prefixLift 6661797
  have htrace : WordTrace (prefixWord ++ tailWord_6661797) baseStart_6661797 baseEnd_6661797 := by
    simpa [prefixWord, tailWord_6661797, baseEnd_6661797] using wordTrace_append hprefix tailTrace_6661797
  have hstable : (prefixWord ++ tailWord_6661797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6661797).length < 2 ^ (prefixWord ++ tailWord_6661797).sum := by decide
  have hdescent : baseEnd_6661797 < baseStart_6661797 := by decide
  rcases family_descends (prefixWord ++ tailWord_6661797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6661807 : List Nat := [1, 1, 2, 1, 2, 4, 3, 1, 1, 2, 5]
def baseStart_6661807 : Nat := 118140960795 + 6661807 * 2 ^ 59
def prefixEnd_6661807 : Nat := 4983230072969 + 3 ^ 40 * 6661807 * 2
def baseEnd_6661807 : Nat := 3420709018486722383175413

theorem tailTrace_6661807 : CollatzResearch.WordTrace tailWord_6661807 prefixEnd_6661807 3420709018486722383175413 := by
  unfold tailWord_6661807
  simp only [CollatzResearch.WordTrace]
  refine ⟨242976062576418459900119675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161984041717612306600079783 242976062576418459900119675)
  ·
    refine ⟨364464093864627689850179513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242976062576418459900119675 364464093864627689850179513)
    ·
      refine ⟨273348070398470767387634635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 364464093864627689850179513 273348070398470767387634635)
      ·
        refine ⟨410022105597706151081451953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273348070398470767387634635 410022105597706151081451953)
        ·
          refine ⟨307516579198279613311088965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 410022105597706151081451953 307516579198279613311088965)
          ·
            refine ⟨57659358599677427495829181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 307516579198279613311088965 57659358599677427495829181)
            ·
              refine ⟨21622259474879035310935943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57659358599677427495829181 21622259474879035310935943)
              ·
                refine ⟨32433389212318552966403915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21622259474879035310935943 32433389212318552966403915)
                ·
                  refine ⟨48650083818477829449605873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32433389212318552966403915 48650083818477829449605873)
                  ·
                    refine ⟨36487562863858372087204405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48650083818477829449605873 36487562863858372087204405)
                    ·
                      refine ⟨3420709018486722383175413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36487562863858372087204405 3420709018486722383175413)
                      ·
                        rfl

theorem cell23_6661807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 1, 1, 2, 5].length) (baseStart_6661807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6661807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6661807 prefixEnd_6661807 := by exact prefixLift 6661807
  have htrace : WordTrace (prefixWord ++ tailWord_6661807) baseStart_6661807 baseEnd_6661807 := by
    simpa [prefixWord, tailWord_6661807, baseEnd_6661807] using wordTrace_append hprefix tailTrace_6661807
  have hstable : (prefixWord ++ tailWord_6661807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6661807).length < 2 ^ (prefixWord ++ tailWord_6661807).sum := by decide
  have hdescent : baseEnd_6661807 < baseStart_6661807 := by decide
  rcases family_descends (prefixWord ++ tailWord_6661807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6661817 : List Nat := [1, 2, 1, 4, 1, 1, 2, 1, 3, 3, 4]
def baseStart_6661817 : Nat := 118140960795 + 6661817 * 2 ^ 59
def prefixEnd_6661817 : Nat := 4983230072969 + 3 ^ 40 * 6661817 * 2
def baseEnd_6661817 : Nat := 3420714153293267344050367

theorem tailTrace_6661817 : CollatzResearch.WordTrace tailWord_6661817 prefixEnd_6661817 3420714153293267344050367 := by
  unfold tailWord_6661817
  simp only [CollatzResearch.WordTrace]
  refine ⟨242976427306382231607983705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161984284870921487738655803 242976427306382231607983705)
  ·
    refine ⟨182232320479786673705987779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242976427306382231607983705 182232320479786673705987779)
    ·
      refine ⟨273348480719680010558981669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182232320479786673705987779 273348480719680010558981669)
      ·
        refine ⟨51252840134940001979809063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 273348480719680010558981669 51252840134940001979809063)
        ·
          refine ⟨76879260202410002969713595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51252840134940001979809063 76879260202410002969713595)
          ·
            refine ⟨115318890303615004454570393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76879260202410002969713595 115318890303615004454570393)
            ·
              refine ⟨86489167727711253340927795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115318890303615004454570393 86489167727711253340927795)
              ·
                refine ⟨129733751591566880011391693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86489167727711253340927795 129733751591566880011391693)
                ·
                  refine ⟨48650156846837580004271885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 129733751591566880011391693 48650156846837580004271885)
                  ·
                    refine ⟨18243808817564092501601957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48650156846837580004271885 18243808817564092501601957)
                    ·
                      refine ⟨3420714153293267344050367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18243808817564092501601957 3420714153293267344050367)
                      ·
                        rfl

theorem cell23_6661817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 1, 3, 3, 4].length) (baseStart_6661817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6661817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6661817 prefixEnd_6661817 := by exact prefixLift 6661817
  have htrace : WordTrace (prefixWord ++ tailWord_6661817) baseStart_6661817 baseEnd_6661817 := by
    simpa [prefixWord, tailWord_6661817, baseEnd_6661817] using wordTrace_append hprefix tailTrace_6661817
  have hstable : (prefixWord ++ tailWord_6661817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6661817).length < 2 ^ (prefixWord ++ tailWord_6661817).sum := by decide
  have hdescent : baseEnd_6661817 < baseStart_6661817 := by decide
  rcases family_descends (prefixWord ++ tailWord_6661817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6661847 : List Nat := [1, 1, 3, 2, 1, 3, 2, 1, 2, 1, 6]
def baseStart_6661847 : Nat := 118140960795 + 6661847 * 2 ^ 59
def prefixEnd_6661847 : Nat := 4983230072969 + 3 ^ 40 * 6661847 * 2
def baseEnd_6661847 : Nat := 3420729557712902226675229

theorem tailTrace_6661847 : CollatzResearch.WordTrace tailWord_6661847 prefixEnd_6661847 3420729557712902226675229 := by
  unfold tailWord_6661847
  simp only [CollatzResearch.WordTrace]
  refine ⟨242977521496273546731575795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161985014330849031154383863 242977521496273546731575795)
  ·
    refine ⟨364466282244410320097363693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242977521496273546731575795 364466282244410320097363693)
    ·
      refine ⟨136674855841653870036511385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 364466282244410320097363693 136674855841653870036511385)
      ·
        refine ⟨102506141881240402527383539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136674855841653870036511385 102506141881240402527383539)
        ·
          refine ⟨153759212821860603791075309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102506141881240402527383539 153759212821860603791075309)
          ·
            refine ⟨57659704808197726421653241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 153759212821860603791075309 57659704808197726421653241)
            ·
              refine ⟨43244778606148294816239931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57659704808197726421653241 43244778606148294816239931)
              ·
                refine ⟨64867167909222442224359897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43244778606148294816239931 64867167909222442224359897)
                ·
                  refine ⟨48650375931916831668269923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64867167909222442224359897 48650375931916831668269923)
                  ·
                    refine ⟨72975563897875247502404885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48650375931916831668269923 72975563897875247502404885)
                    ·
                      refine ⟨3420729557712902226675229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72975563897875247502404885 3420729557712902226675229)
                      ·
                        rfl

theorem cell23_6661847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 1, 2, 1, 6].length) (baseStart_6661847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6661847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6661847 prefixEnd_6661847 := by exact prefixLift 6661847
  have htrace : WordTrace (prefixWord ++ tailWord_6661847) baseStart_6661847 baseEnd_6661847 := by
    simpa [prefixWord, tailWord_6661847, baseEnd_6661847] using wordTrace_append hprefix tailTrace_6661847
  have hstable : (prefixWord ++ tailWord_6661847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6661847).length < 2 ^ (prefixWord ++ tailWord_6661847).sum := by decide
  have hdescent : baseEnd_6661847 < baseStart_6661847 := by decide
  rcases family_descends (prefixWord ++ tailWord_6661847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6661852 : List Nat := [2, 2, 5, 1, 3, 1, 2, 2, 5]
def baseStart_6661852 : Nat := 118140960795 + 6661852 * 2 ^ 59
def prefixEnd_6661852 : Nat := 4983230072969 + 3 ^ 40 * 6661852 * 2
def baseEnd_6661852 : Nat := 380081347235130523012523

theorem tailTrace_6661852 : CollatzResearch.WordTrace tailWord_6661852 prefixEnd_6661852 380081347235130523012523 := by
  unfold tailWord_6661852
  simp only [CollatzResearch.WordTrace]
  refine ⟨121488851930627716292753905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161985135907503621723671873 121488851930627716292753905)
  ·
    refine ⟨91116638947970787219565429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121488851930627716292753905 91116638947970787219565429)
    ·
      refine ⟨8542184901372261301834259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 91116638947970787219565429 8542184901372261301834259)
      ·
        refine ⟨12813277352058391952751389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8542184901372261301834259 12813277352058391952751389)
        ·
          refine ⟨4804979007021896982281771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12813277352058391952751389 4804979007021896982281771)
          ·
            refine ⟨7207468510532845473422657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4804979007021896982281771 7207468510532845473422657)
            ·
              refine ⟨5405601382899634105066993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7207468510532845473422657 5405601382899634105066993)
              ·
                refine ⟨4054201037174725578800245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5405601382899634105066993 4054201037174725578800245)
                ·
                  refine ⟨380081347235130523012523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4054201037174725578800245 380081347235130523012523)
                  ·
                    rfl

theorem cell23_6661852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 2, 2, 5].length) (baseStart_6661852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6661852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6661852 prefixEnd_6661852 := by exact prefixLift 6661852
  have htrace : WordTrace (prefixWord ++ tailWord_6661852) baseStart_6661852 baseEnd_6661852 := by
    simpa [prefixWord, tailWord_6661852, baseEnd_6661852] using wordTrace_append hprefix tailTrace_6661852
  have hstable : (prefixWord ++ tailWord_6661852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6661852).length < 2 ^ (prefixWord ++ tailWord_6661852).sum := by decide
  have hdescent : baseEnd_6661852 < baseStart_6661852 := by decide
  rcases family_descends (prefixWord ++ tailWord_6661852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6661874 : List Nat := [3, 2, 1, 3, 1, 1, 1, 5, 6]
def baseStart_6661874 : Nat := 118140960795 + 6661874 * 2 ^ 59
def prefixEnd_6661874 : Nat := 4983230072969 + 3 ^ 40 * 6661874 * 2
def baseEnd_6661874 : Nat := 380082602410063735670845

theorem tailTrace_6661874 : CollatzResearch.WordTrace tailWord_6661874 prefixEnd_6661874 380082602410063735670845 := by
  unfold tailWord_6661874
  simp only [CollatzResearch.WordTrace]
  refine ⟨60744626566793932585702169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161985670844783820228539117 60744626566793932585702169)
  ·
    refine ⟨45558469925095449439276627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60744626566793932585702169 45558469925095449439276627)
    ·
      refine ⟨68337704887643174158914941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45558469925095449439276627 68337704887643174158914941)
      ·
        refine ⟨25626639332866190309593103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68337704887643174158914941 25626639332866190309593103)
        ·
          refine ⟨38439958999299285464389655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25626639332866190309593103 38439958999299285464389655)
          ·
            refine ⟨57659938498948928196584483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38439958999299285464389655 57659938498948928196584483)
            ·
              refine ⟨86489907748423392294876725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57659938498948928196584483 86489907748423392294876725)
              ·
                refine ⟨8108428851414693027644693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 86489907748423392294876725 8108428851414693027644693)
                ·
                  refine ⟨380082602410063735670845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8108428851414693027644693 380082602410063735670845)
                  ·
                    rfl

theorem cell23_6661874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 5, 6].length) (baseStart_6661874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6661874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6661874 prefixEnd_6661874 := by exact prefixLift 6661874
  have htrace : WordTrace (prefixWord ++ tailWord_6661874) baseStart_6661874 baseEnd_6661874 := by
    simpa [prefixWord, tailWord_6661874, baseEnd_6661874] using wordTrace_append hprefix tailTrace_6661874
  have hstable : (prefixWord ++ tailWord_6661874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6661874).length < 2 ^ (prefixWord ++ tailWord_6661874).sum := by decide
  have hdescent : baseEnd_6661874 < baseStart_6661874 := by decide
  rcases family_descends (prefixWord ++ tailWord_6661874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6661895 : List Nat := [1, 1, 4, 4, 2, 1, 2, 3, 1, 4]
def baseStart_6661895 : Nat := 118140960795 + 6661895 * 2 ^ 59
def prefixEnd_6661895 : Nat := 4983230072969 + 3 ^ 40 * 6661895 * 2
def baseEnd_6661895 : Nat := 1140251401594772679625003

theorem tailTrace_6661895 : CollatzResearch.WordTrace tailWord_6661895 prefixEnd_6661895 1140251401594772679625003 := by
  unfold tailWord_6661895
  simp only [CollatzResearch.WordTrace]
  refine ⟨242979272200099650929323139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161986181466733100619548759 242979272200099650929323139)
  ·
    refine ⟨364468908300149476393984709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242979272200099650929323139 364468908300149476393984709)
    ·
      refine ⟨68337920306278026823872133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 364468908300149476393984709 68337920306278026823872133)
      ·
        refine ⟨12813360057427130029476025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68337920306278026823872133 12813360057427130029476025)
        ·
          refine ⟨9610020043070347522107019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12813360057427130029476025 9610020043070347522107019)
          ·
            refine ⟨14415030064605521283160529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9610020043070347522107019 14415030064605521283160529)
            ·
              refine ⟨10811272548454140962370397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14415030064605521283160529 10811272548454140962370397)
              ·
                refine ⟨4054227205670302860888899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10811272548454140962370397 4054227205670302860888899)
                ·
                  refine ⟨6081340808505454291333349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4054227205670302860888899 6081340808505454291333349)
                  ·
                    refine ⟨1140251401594772679625003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6081340808505454291333349 1140251401594772679625003)
                    ·
                      rfl

theorem cell23_6661895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 2, 3, 1, 4].length) (baseStart_6661895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6661895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6661895 prefixEnd_6661895 := by exact prefixLift 6661895
  have htrace : WordTrace (prefixWord ++ tailWord_6661895) baseStart_6661895 baseEnd_6661895 := by
    simpa [prefixWord, tailWord_6661895, baseEnd_6661895] using wordTrace_append hprefix tailTrace_6661895
  have hstable : (prefixWord ++ tailWord_6661895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6661895).length < 2 ^ (prefixWord ++ tailWord_6661895).sum := by decide
  have hdescent : baseEnd_6661895 < baseStart_6661895 := by decide
  rcases family_descends (prefixWord ++ tailWord_6661895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6661897 : List Nat := [1, 2, 1, 1, 3, 2, 1, 1, 2, 4, 5]
def baseStart_6661897 : Nat := 118140960795 + 6661897 * 2 ^ 59
def prefixEnd_6661897 : Nat := 4983230072969 + 3 ^ 40 * 6661897 * 2
def baseEnd_6661897 : Nat := 3420755231745627031049999

theorem tailTrace_6661897 : CollatzResearch.WordTrace tailWord_6661897 prefixEnd_6661897 3420755231745627031049999 := by
  unfold tailWord_6661897
  simp only [CollatzResearch.WordTrace]
  refine ⟨242979345146092405270895945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161986230097394936847263963 242979345146092405270895945)
  ·
    refine ⟨182234508859569303953171959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242979345146092405270895945 182234508859569303953171959)
    ·
      refine ⟨273351763289353955929757939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182234508859569303953171959 273351763289353955929757939)
      ·
        refine ⟨410027644934030933894636909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273351763289353955929757939 410027644934030933894636909)
        ·
          refine ⟨153760366850261600210488841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 410027644934030933894636909 153760366850261600210488841)
          ·
            refine ⟨115320275137696200157866631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153760366850261600210488841 115320275137696200157866631)
            ·
              refine ⟨172980412706544300236799947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115320275137696200157866631 172980412706544300236799947)
              ·
                refine ⟨259470619059816450355199921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 172980412706544300236799947 259470619059816450355199921)
                ·
                  refine ⟨194602964294862337766399941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 259470619059816450355199921 194602964294862337766399941)
                  ·
                    refine ⟨36488055805286688331199989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 194602964294862337766399941 36488055805286688331199989)
                    ·
                      refine ⟨3420755231745627031049999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36488055805286688331199989 3420755231745627031049999)
                      ·
                        rfl

theorem cell23_6661897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 4, 5].length) (baseStart_6661897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6661897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6661897 prefixEnd_6661897 := by exact prefixLift 6661897
  have htrace : WordTrace (prefixWord ++ tailWord_6661897) baseStart_6661897 baseEnd_6661897 := by
    simpa [prefixWord, tailWord_6661897, baseEnd_6661897] using wordTrace_append hprefix tailTrace_6661897
  have hstable : (prefixWord ++ tailWord_6661897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6661897).length < 2 ^ (prefixWord ++ tailWord_6661897).sum := by decide
  have hdescent : baseEnd_6661897 < baseStart_6661897 := by decide
  rcases family_descends (prefixWord ++ tailWord_6661897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6661961 : List Nat := [1, 2, 1, 1, 2, 4, 1, 5, 1, 2, 3]
def baseStart_6661961 : Nat := 118140960795 + 6661961 * 2 ^ 59
def prefixEnd_6661961 : Nat := 4983230072969 + 3 ^ 40 * 6661961 * 2
def baseEnd_6661961 : Nat := 3420788094507514780649705

theorem tailTrace_6661961 : CollatzResearch.WordTrace tailWord_6661961 prefixEnd_6661961 3420788094507514780649705 := by
  unfold tailWord_6661961
  simp only [CollatzResearch.WordTrace]
  refine ⟨242981679417860544201225737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161987786278573696134150491 242981679417860544201225737)
  ·
    refine ⟨182236259563395408150919303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242981679417860544201225737 182236259563395408150919303)
    ·
      refine ⟨273354389345093112226378955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182236259563395408150919303 273354389345093112226378955)
      ·
        refine ⟨410031584017639668339568433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273354389345093112226378955 410031584017639668339568433)
        ·
          refine ⟨307523688013229751254676325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 410031584017639668339568433 307523688013229751254676325)
          ·
            refine ⟨57660691502480578360251811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 307523688013229751254676325 57660691502480578360251811)
            ·
              refine ⟨86491037253720867540377717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57660691502480578360251811 86491037253720867540377717)
              ·
                refine ⟨8108534742536331331910411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 86491037253720867540377717 8108534742536331331910411)
                ·
                  refine ⟨12162802113804496997865617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8108534742536331331910411 12162802113804496997865617)
                  ·
                    refine ⟨9122101585353372748399213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12162802113804496997865617 9122101585353372748399213)
                    ·
                      refine ⟨3420788094507514780649705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9122101585353372748399213 3420788094507514780649705)
                      ·
                        rfl

theorem cell23_6661961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 5, 1, 2, 3].length) (baseStart_6661961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6661961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6661961 prefixEnd_6661961 := by exact prefixLift 6661961
  have htrace : WordTrace (prefixWord ++ tailWord_6661961) baseStart_6661961 baseEnd_6661961 := by
    simpa [prefixWord, tailWord_6661961, baseEnd_6661961] using wordTrace_append hprefix tailTrace_6661961
  have hstable : (prefixWord ++ tailWord_6661961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6661961).length < 2 ^ (prefixWord ++ tailWord_6661961).sum := by decide
  have hdescent : baseEnd_6661961 < baseStart_6661961 := by decide
  rcases family_descends (prefixWord ++ tailWord_6661961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6661991 : List Nat := [1, 1, 5, 1, 2, 1, 2, 3, 1, 3, 3]
def baseStart_6661991 : Nat := 118140960795 + 6661991 * 2 ^ 59
def prefixEnd_6661991 : Nat := 4983230072969 + 3 ^ 40 * 6661991 * 2
def baseEnd_6661991 : Nat := 3420803498927149663274567

theorem tailTrace_6661991 : CollatzResearch.WordTrace tailWord_6661991 prefixEnd_6661991 3420803498927149663274567 := by
  unfold tailWord_6661991
  simp only [CollatzResearch.WordTrace]
  refine ⟨242982773607751859324817827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161988515738501239549878551 242982773607751859324817827)
  ·
    refine ⟨364474160411627788987226741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242982773607751859324817827 364474160411627788987226741)
    ·
      refine ⟨34169452538590105217552507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 364474160411627788987226741 34169452538590105217552507)
      ·
        refine ⟨51254178807885157826328761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34169452538590105217552507 51254178807885157826328761)
        ·
          refine ⟨38440634105913868369746571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51254178807885157826328761 38440634105913868369746571)
          ·
            refine ⟨57660951158870802554619857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38440634105913868369746571 57660951158870802554619857)
            ·
              refine ⟨43245713369153101915964893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57660951158870802554619857 43245713369153101915964893)
              ·
                refine ⟨16217142513432413218486835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43245713369153101915964893 16217142513432413218486835)
                ·
                  refine ⟨24325713770148619827730253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16217142513432413218486835 24325713770148619827730253)
                  ·
                    refine ⟨9122142663805732435398845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24325713770148619827730253 9122142663805732435398845)
                    ·
                      refine ⟨3420803498927149663274567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9122142663805732435398845 3420803498927149663274567)
                      ·
                        rfl

theorem cell23_6661991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 3, 1, 3, 3].length) (baseStart_6661991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6661991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6661991 prefixEnd_6661991 := by exact prefixLift 6661991
  have htrace : WordTrace (prefixWord ++ tailWord_6661991) baseStart_6661991 baseEnd_6661991 := by
    simpa [prefixWord, tailWord_6661991, baseEnd_6661991] using wordTrace_append hprefix tailTrace_6661991
  have hstable : (prefixWord ++ tailWord_6661991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6661991).length < 2 ^ (prefixWord ++ tailWord_6661991).sum := by decide
  have hdescent : baseEnd_6661991 < baseStart_6661991 := by decide
  rcases family_descends (prefixWord ++ tailWord_6661991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6662026 : List Nat := [3, 1, 2, 4, 2, 2, 2, 2, 1, 2, 2]
def baseStart_6662026 : Nat := 118140960795 + 6662026 * 2 ^ 59
def prefixEnd_6662026 : Nat := 4983230072969 + 3 ^ 40 * 6662026 * 2
def baseEnd_6662026 : Nat := 3420821470750057026336907

theorem tailTrace_6662026 : CollatzResearch.WordTrace tailWord_6662026 prefixEnd_6662026 3420821470750057026336907 := by
  unfold tailWord_6662026
  simp only [CollatzResearch.WordTrace]
  refine ⟨60746012540656265075585483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161989366775083373534894621 60746012540656265075585483)
  ·
    refine ⟨91119018810984397613378225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60746012540656265075585483 91119018810984397613378225)
    ·
      refine ⟨68339264108238298210033669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91119018810984397613378225 68339264108238298210033669)
      ·
        refine ⟨12813612020294680914381313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68339264108238298210033669 12813612020294680914381313)
        ·
          refine ⟨9610209015221010685785985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12813612020294680914381313 9610209015221010685785985)
          ·
            refine ⟨7207656761415758014339489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9610209015221010685785985 7207656761415758014339489)
            ·
              refine ⟨5405742571061818510754617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7207656761415758014339489 5405742571061818510754617)
              ·
                refine ⟨4054306928296363883065963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5405742571061818510754617 4054306928296363883065963)
                ·
                  refine ⟨6081460392444545824598945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4054306928296363883065963 6081460392444545824598945)
                  ·
                    refine ⟨4561095294333409368449209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6081460392444545824598945 4561095294333409368449209)
                    ·
                      refine ⟨3420821470750057026336907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4561095294333409368449209 3420821470750057026336907)
                      ·
                        rfl

theorem cell23_6662026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 2, 2, 1, 2, 2].length) (baseStart_6662026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6662026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6662026 prefixEnd_6662026 := by exact prefixLift 6662026
  have htrace : WordTrace (prefixWord ++ tailWord_6662026) baseStart_6662026 baseEnd_6662026 := by
    simpa [prefixWord, tailWord_6662026, baseEnd_6662026] using wordTrace_append hprefix tailTrace_6662026
  have hstable : (prefixWord ++ tailWord_6662026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6662026).length < 2 ^ (prefixWord ++ tailWord_6662026).sum := by decide
  have hdescent : baseEnd_6662026 < baseStart_6662026 := by decide
  rcases family_descends (prefixWord ++ tailWord_6662026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6662048 : List Nat := [2, 1, 1, 4, 1, 1, 1, 2, 6, 2, 2]
def baseStart_6662048 : Nat := 118140960795 + 6662048 * 2 ^ 59
def prefixEnd_6662048 : Nat := 4983230072969 + 3 ^ 40 * 6662048 * 2
def baseEnd_6662048 : Nat := 3420832767324455940261805

theorem tailTrace_6662048 : CollatzResearch.WordTrace tailWord_6662048 prefixEnd_6662048 3420832767324455940261805 := by
  unfold tailWord_6662048
  simp only [CollatzResearch.WordTrace]
  refine ⟨121492426284272679029821399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161989901712363572039761865 121492426284272679029821399)
  ·
    refine ⟨182238639426409018544732099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121492426284272679029821399 182238639426409018544732099)
    ·
      refine ⟨273357959139613527817098149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182238639426409018544732099 273357959139613527817098149)
      ·
        refine ⟨51254617338677536465705903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 273357959139613527817098149 51254617338677536465705903)
        ·
          refine ⟨76881926008016304698558855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51254617338677536465705903 76881926008016304698558855)
          ·
            refine ⟨115322889012024457047838283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76881926008016304698558855 115322889012024457047838283)
            ·
              refine ⟨172984333518036685571757425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115322889012024457047838283 172984333518036685571757425)
              ·
                refine ⟨129738250138527514178818069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 172984333518036685571757425 129738250138527514178818069)
                ·
                  refine ⟨6081480475243477227132097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 129738250138527514178818069 6081480475243477227132097)
                  ·
                    refine ⟨4561110356432607920349073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6081480475243477227132097 4561110356432607920349073)
                    ·
                      refine ⟨3420832767324455940261805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4561110356432607920349073 3420832767324455940261805)
                      ·
                        rfl

theorem cell23_6662048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 2, 6, 2, 2].length) (baseStart_6662048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6662048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6662048 prefixEnd_6662048 := by exact prefixLift 6662048
  have htrace : WordTrace (prefixWord ++ tailWord_6662048) baseStart_6662048 baseEnd_6662048 := by
    simpa [prefixWord, tailWord_6662048, baseEnd_6662048] using wordTrace_append hprefix tailTrace_6662048
  have hstable : (prefixWord ++ tailWord_6662048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6662048).length < 2 ^ (prefixWord ++ tailWord_6662048).sum := by decide
  have hdescent : baseEnd_6662048 < baseStart_6662048 := by decide
  rcases family_descends (prefixWord ++ tailWord_6662048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6662088 : List Nat := [2, 1, 3, 1, 4, 1, 2, 4, 5]
def baseStart_6662088 : Nat := 118140960795 + 6662088 * 2 ^ 59
def prefixEnd_6662088 : Nat := 4983230072969 + 3 ^ 40 * 6662088 * 2
def baseEnd_6662088 : Nat := 380094811838959531529069

theorem tailTrace_6662088 : CollatzResearch.WordTrace tailWord_6662088 prefixEnd_6662088 380094811838959531529069 := by
  unfold tailWord_6662088
  simp only [CollatzResearch.WordTrace]
  refine ⟨121493155744200222445549459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161990874325600296594065945 121493155744200222445549459)
  ·
    refine ⟨182239733616300333668324189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121493155744200222445549459 182239733616300333668324189)
    ·
      refine ⟨68339900106112625125621571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182239733616300333668324189 68339900106112625125621571)
      ·
        refine ⟨102509850159168937688432357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68339900106112625125621571 102509850159168937688432357)
        ·
          refine ⟨19220596904844175816581067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102509850159168937688432357 19220596904844175816581067)
          ·
            refine ⟨28830895357266263724871601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19220596904844175816581067 28830895357266263724871601)
            ·
              refine ⟨21623171517949697793653701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28830895357266263724871601 21623171517949697793653701)
              ·
                refine ⟨4054344659615568336310069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21623171517949697793653701 4054344659615568336310069)
                ·
                  refine ⟨380094811838959531529069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4054344659615568336310069 380094811838959531529069)
                  ·
                    rfl

theorem cell23_6662088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 4, 5].length) (baseStart_6662088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6662088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6662088 prefixEnd_6662088 := by exact prefixLift 6662088
  have htrace : WordTrace (prefixWord ++ tailWord_6662088) baseStart_6662088 baseEnd_6662088 := by
    simpa [prefixWord, tailWord_6662088, baseEnd_6662088] using wordTrace_append hprefix tailTrace_6662088
  have hstable : (prefixWord ++ tailWord_6662088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6662088).length < 2 ^ (prefixWord ++ tailWord_6662088).sum := by decide
  have hdescent : baseEnd_6662088 < baseStart_6662088 := by decide
  rcases family_descends (prefixWord ++ tailWord_6662088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6662101 : List Nat := [1, 3, 2, 3, 2, 1, 1, 2, 1, 7]
def baseStart_6662101 : Nat := 118140960795 + 6662101 * 2 ^ 59
def prefixEnd_6662101 : Nat := 4983230072969 + 3 ^ 40 * 6662101 * 2
def baseEnd_6662101 : Nat := 1140286660599714744299687

theorem tailTrace_6662101 : CollatzResearch.WordTrace tailWord_6662101 prefixEnd_6662101 1140286660599714744299687 := by
  unfold tailWord_6662101
  simp only [CollatzResearch.WordTrace]
  refine ⟨242986785637353348111322157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161991190424902232074214771 242986785637353348111322157)
  ·
    refine ⟨91120044614007505541745809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 242986785637353348111322157 91120044614007505541745809)
    ·
      refine ⟨68340033460505629156309357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91120044614007505541745809 68340033460505629156309357)
      ·
        refine ⟨25627512547689610933616009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68340033460505629156309357 25627512547689610933616009)
        ·
          refine ⟨19220634410767208200212007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25627512547689610933616009 19220634410767208200212007)
          ·
            refine ⟨28830951616150812300318011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19220634410767208200212007 28830951616150812300318011)
            ·
              refine ⟨43246427424226218450477017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28830951616150812300318011 43246427424226218450477017)
              ·
                refine ⟨32434820568169663837857763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43246427424226218450477017 32434820568169663837857763)
                ·
                  refine ⟨48652230852254495756786645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32434820568169663837857763 48652230852254495756786645)
                  ·
                    refine ⟨1140286660599714744299687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48652230852254495756786645 1140286660599714744299687)
                    ·
                      rfl

theorem cell23_6662101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 2, 1, 7].length) (baseStart_6662101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6662101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6662101 prefixEnd_6662101 := by exact prefixLift 6662101
  have htrace : WordTrace (prefixWord ++ tailWord_6662101) baseStart_6662101 baseEnd_6662101 := by
    simpa [prefixWord, tailWord_6662101, baseEnd_6662101] using wordTrace_append hprefix tailTrace_6662101
  have hstable : (prefixWord ++ tailWord_6662101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6662101).length < 2 ^ (prefixWord ++ tailWord_6662101).sum := by decide
  have hdescent : baseEnd_6662101 < baseStart_6662101 := by decide
  rcases family_descends (prefixWord ++ tailWord_6662101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6662131 : List Nat := [1, 1, 1, 2, 2, 2, 1, 4, 5, 4]
def baseStart_6662131 : Nat := 118140960795 + 6662131 * 2 ^ 59
def prefixEnd_6662131 : Nat := 4983230072969 + 3 ^ 40 * 6662131 * 2
def baseEnd_6662131 : Nat := 1140291795406259705174641

theorem tailTrace_6662131 : CollatzResearch.WordTrace tailWord_6662131 prefixEnd_6662131 1140291795406259705174641 := by
  unfold tailWord_6662131
  simp only [CollatzResearch.WordTrace]
  refine ⟨242987879827244663234914247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161991919884829775489942831 242987879827244663234914247)
  ·
    refine ⟨364481819740866994852371371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242987879827244663234914247 364481819740866994852371371)
    ·
      refine ⟨546722729611300492278557057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 364481819740866994852371371 546722729611300492278557057)
      ·
        refine ⟨410042047208475369208917793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 546722729611300492278557057 410042047208475369208917793)
        ·
          refine ⟨307531535406356526906688345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 410042047208475369208917793 307531535406356526906688345)
          ·
            refine ⟨230648651554767395180016259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 307531535406356526906688345 230648651554767395180016259)
            ·
              refine ⟨345972977332151092770024389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 230648651554767395180016259 345972977332151092770024389)
              ·
                refine ⟨64869933249778329894379573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 345972977332151092770024389 64869933249778329894379573)
                ·
                  refine ⟨6081556242166718427598085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 64869933249778329894379573 6081556242166718427598085)
                  ·
                    refine ⟨1140291795406259705174641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6081556242166718427598085 1140291795406259705174641)
                    ·
                      rfl

theorem cell23_6662131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 4, 5, 4].length) (baseStart_6662131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6662131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6662131 prefixEnd_6662131 := by exact prefixLift 6662131
  have htrace : WordTrace (prefixWord ++ tailWord_6662131) baseStart_6662131 baseEnd_6662131 := by
    simpa [prefixWord, tailWord_6662131, baseEnd_6662131] using wordTrace_append hprefix tailTrace_6662131
  have hstable : (prefixWord ++ tailWord_6662131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6662131).length < 2 ^ (prefixWord ++ tailWord_6662131).sum := by decide
  have hdescent : baseEnd_6662131 < baseStart_6662131 := by decide
  rcases family_descends (prefixWord ++ tailWord_6662131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6662158 : List Nat := [4, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3]
def baseStart_6662158 : Nat := 118140960795 + 6662158 * 2 ^ 59
def prefixEnd_6662158 : Nat := 4983230072969 + 3 ^ 40 * 6662158 * 2
def baseEnd_6662158 : Nat := 3420889250196450509886299

theorem tailTrace_6662158 : CollatzResearch.WordTrace tailWord_6662158 prefixEnd_6662158 3420889250196450509886299 := by
  unfold tailWord_6662158
  simp only [CollatzResearch.WordTrace]
  refine ⟨30373608074768355855768391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 161992576398764564564098085 30373608074768355855768391)
  ·
    refine ⟨45560412112152533783652587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30373608074768355855768391 45560412112152533783652587)
    ·
      refine ⟨68340618168228800675478881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45560412112152533783652587 68340618168228800675478881)
      ·
        refine ⟨51255463626171600506609161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68340618168228800675478881 51255463626171600506609161)
        ·
          refine ⟨38441597719628700379956871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51255463626171600506609161 38441597719628700379956871)
          ·
            refine ⟨57662396579443050569935307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38441597719628700379956871 57662396579443050569935307)
            ·
              refine ⟨86493594869164575854902961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57662396579443050569935307 86493594869164575854902961)
              ·
                refine ⟨64870196151873431891177221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86493594869164575854902961 64870196151873431891177221)
                ·
                  refine ⟨12163161778476268479595729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64870196151873431891177221 12163161778476268479595729)
                  ·
                    refine ⟨9122371333857201359696797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12163161778476268479595729 9122371333857201359696797)
                    ·
                      refine ⟨3420889250196450509886299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9122371333857201359696797 3420889250196450509886299)
                      ·
                        rfl

theorem cell23_6662158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3].length) (baseStart_6662158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6662158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6662158 prefixEnd_6662158 := by exact prefixLift 6662158
  have htrace : WordTrace (prefixWord ++ tailWord_6662158) baseStart_6662158 baseEnd_6662158 := by
    simpa [prefixWord, tailWord_6662158, baseEnd_6662158] using wordTrace_append hprefix tailTrace_6662158
  have hstable : (prefixWord ++ tailWord_6662158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6662158).length < 2 ^ (prefixWord ++ tailWord_6662158).sum := by decide
  have hdescent : baseEnd_6662158 < baseStart_6662158 := by decide
  rcases family_descends (prefixWord ++ tailWord_6662158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6662188 : List Nat := [2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 3]
def baseStart_6662188 : Nat := 118140960795 + 6662188 * 2 ^ 59
def prefixEnd_6662188 : Nat := 4983230072969 + 3 ^ 40 * 6662188 * 2
def baseEnd_6662188 : Nat := 3420904654616085392511161

theorem tailTrace_6662188 : CollatzResearch.WordTrace tailWord_6662188 prefixEnd_6662188 3420904654616085392511161 := by
  unfold tailWord_6662188
  simp only [CollatzResearch.WordTrace]
  refine ⟨121494979394019080984869609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161993305858692107979826145 121494979394019080984869609)
  ·
    refine ⟨91121234545514310738652207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 121494979394019080984869609 91121234545514310738652207)
    ·
      refine ⟨136681851818271466107978311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91121234545514310738652207 136681851818271466107978311)
      ·
        refine ⟨205022777727407199161967467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136681851818271466107978311 205022777727407199161967467)
        ·
          refine ⟨307534166591110798742951201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205022777727407199161967467 307534166591110798742951201)
          ·
            refine ⟨230650624943333099057213401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 307534166591110798742951201 230650624943333099057213401)
            ·
              refine ⟨172987968707499824292910051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 230650624943333099057213401 172987968707499824292910051)
              ·
                refine ⟨259481953061249736439365077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 172987968707499824292910051 259481953061249736439365077)
                ·
                  refine ⟨6081608274873040697797619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 259481953061249736439365077 6081608274873040697797619)
                  ·
                    refine ⟨9122412412309561046696429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6081608274873040697797619 9122412412309561046696429)
                    ·
                      refine ⟨3420904654616085392511161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9122412412309561046696429 3420904654616085392511161)
                      ·
                        rfl

theorem cell23_6662188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 3].length) (baseStart_6662188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6662188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6662188 prefixEnd_6662188 := by exact prefixLift 6662188
  have htrace : WordTrace (prefixWord ++ tailWord_6662188) baseStart_6662188 baseEnd_6662188 := by
    simpa [prefixWord, tailWord_6662188, baseEnd_6662188] using wordTrace_append hprefix tailTrace_6662188
  have hstable : (prefixWord ++ tailWord_6662188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6662188).length < 2 ^ (prefixWord ++ tailWord_6662188).sum := by decide
  have hdescent : baseEnd_6662188 < baseStart_6662188 := by decide
  rcases family_descends (prefixWord ++ tailWord_6662188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6662198 : List Nat := [5, 1, 2, 1, 1, 1, 2, 1, 1, 2, 6]
def baseStart_6662198 : Nat := 118140960795 + 6662198 * 2 ^ 59
def prefixEnd_6662198 : Nat := 4983230072969 + 3 ^ 40 * 6662198 * 2
def baseEnd_6662198 : Nat := 3420909789422630353386115

theorem tailTrace_6662198 : CollatzResearch.WordTrace tailWord_6662198 prefixEnd_6662198 3420909789422630353386115 := by
  unfold tailWord_6662198
  simp only [CollatzResearch.WordTrace]
  refine ⟨15186895219875120854850203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 161993549012001289118402165 15186895219875120854850203)
  ·
    refine ⟨22780342829812681282275305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15186895219875120854850203 22780342829812681282275305)
    ·
      refine ⟨17085257122359510961706479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22780342829812681282275305 17085257122359510961706479)
      ·
        refine ⟨25627885683539266442559719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17085257122359510961706479 25627885683539266442559719)
        ·
          refine ⟨38441828525308899663839579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25627885683539266442559719 38441828525308899663839579)
          ·
            refine ⟨57662742787963349495759369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38441828525308899663839579 57662742787963349495759369)
            ·
              refine ⟨43247057090972512121819527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57662742787963349495759369 43247057090972512121819527)
              ·
                refine ⟨64870585636458768182729291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43247057090972512121819527 64870585636458768182729291)
                ·
                  refine ⟨97305878454688152274093937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64870585636458768182729291 97305878454688152274093937)
                  ·
                    refine ⟨72979408841016114205570453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 97305878454688152274093937 72979408841016114205570453)
                    ·
                      refine ⟨3420909789422630353386115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72979408841016114205570453 3420909789422630353386115)
                      ·
                        rfl

theorem cell23_6662198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_6662198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6662198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6662198 prefixEnd_6662198 := by exact prefixLift 6662198
  have htrace : WordTrace (prefixWord ++ tailWord_6662198) baseStart_6662198 baseEnd_6662198 := by
    simpa [prefixWord, tailWord_6662198, baseEnd_6662198] using wordTrace_append hprefix tailTrace_6662198
  have hstable : (prefixWord ++ tailWord_6662198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6662198).length < 2 ^ (prefixWord ++ tailWord_6662198).sum := by decide
  have hdescent : baseEnd_6662198 < baseStart_6662198 := by decide
  rcases family_descends (prefixWord ++ tailWord_6662198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6662205 : List Nat := [1, 4, 1, 3, 1, 1, 2, 3, 3, 1, 3]
def baseStart_6662205 : Nat := 118140960795 + 6662205 * 2 ^ 59
def prefixEnd_6662205 : Nat := 4983230072969 + 3 ^ 40 * 6662205 * 2
def baseEnd_6662205 : Nat := 3420913383787211825998583

theorem tailTrace_6662205 : CollatzResearch.WordTrace tailWord_6662205 prefixEnd_6662205 3420913383787211825998583 := by
  unfold tailWord_6662205
  simp only [CollatzResearch.WordTrace]
  refine ⟨242990578828976573873108069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161993719219317715915405379 242990578828976573873108069)
  ·
    refine ⟨45560733530433107601207763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 242990578828976573873108069 45560733530433107601207763)
    ·
      refine ⟨68341100295649661401811645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45560733530433107601207763 68341100295649661401811645)
      ·
        refine ⟨25627912610868623025679367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68341100295649661401811645 25627912610868623025679367)
        ·
          refine ⟨38441868916302934538519051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25627912610868623025679367 38441868916302934538519051)
          ·
            refine ⟨57662803374454401807778577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38441868916302934538519051 57662803374454401807778577)
            ·
              refine ⟨43247102530840801355833933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57662803374454401807778577 43247102530840801355833933)
              ·
                refine ⟨16217663449065300508437725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43247102530840801355833933 16217663449065300508437725)
                ·
                  refine ⟨6081623793399487690664147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16217663449065300508437725 6081623793399487690664147)
                  ·
                    refine ⟨9122435690099231535996221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6081623793399487690664147 9122435690099231535996221)
                    ·
                      refine ⟨3420913383787211825998583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9122435690099231535996221 3420913383787211825998583)
                      ·
                        rfl

theorem cell23_6662205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 3, 3, 1, 3].length) (baseStart_6662205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6662205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6662205 prefixEnd_6662205 := by exact prefixLift 6662205
  have htrace : WordTrace (prefixWord ++ tailWord_6662205) baseStart_6662205 baseEnd_6662205 := by
    simpa [prefixWord, tailWord_6662205, baseEnd_6662205] using wordTrace_append hprefix tailTrace_6662205
  have hstable : (prefixWord ++ tailWord_6662205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6662205).length < 2 ^ (prefixWord ++ tailWord_6662205).sum := by decide
  have hdescent : baseEnd_6662205 < baseStart_6662205 := by decide
  rcases family_descends (prefixWord ++ tailWord_6662205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6662232 : List Nat := [2, 1, 2, 2, 1, 6, 1, 1, 2, 3, 2]
def baseStart_6662232 : Nat := 118140960795 + 6662232 * 2 ^ 59
def prefixEnd_6662232 : Nat := 4983230072969 + 3 ^ 40 * 6662232 * 2
def baseEnd_6662232 : Nat := 3420927247764883220360959

theorem tailTrace_6662232 : CollatzResearch.WordTrace tailWord_6662232 prefixEnd_6662232 3420927247764883220360959 := by
  unfold tailWord_6662232
  simp only [CollatzResearch.WordTrace]
  refine ⟨121495781799939378742170475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 161994375733252504989560633 121495781799939378742170475)
  ·
    refine ⟨182243672699909068113255713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121495781799939378742170475 182243672699909068113255713)
    ·
      refine ⟨136682754524931801084941785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182243672699909068113255713 136682754524931801084941785)
      ·
        refine ⟨102512065893698850813706339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 136682754524931801084941785 102512065893698850813706339)
        ·
          refine ⟨153768098840548276220559509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102512065893698850813706339 153768098840548276220559509)
          ·
            refine ⟨7207879633150700447838727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 153768098840548276220559509 7207879633150700447838727)
            ·
              refine ⟨10811819449726050671758091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7207879633150700447838727 10811819449726050671758091)
              ·
                refine ⟨16217729174589076007637137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10811819449726050671758091 16217729174589076007637137)
                ·
                  refine ⟨12163296880941807005727853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16217729174589076007637137 12163296880941807005727853)
                  ·
                    refine ⟨4561236330353177627147945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12163296880941807005727853 4561236330353177627147945)
                    ·
                      refine ⟨3420927247764883220360959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4561236330353177627147945 3420927247764883220360959)
                      ·
                        rfl

theorem cell23_6662232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 1, 1, 2, 3, 2].length) (baseStart_6662232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6662232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6662232 prefixEnd_6662232 := by exact prefixLift 6662232
  have htrace : WordTrace (prefixWord ++ tailWord_6662232) baseStart_6662232 baseEnd_6662232 := by
    simpa [prefixWord, tailWord_6662232, baseEnd_6662232] using wordTrace_append hprefix tailTrace_6662232
  have hstable : (prefixWord ++ tailWord_6662232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6662232).length < 2 ^ (prefixWord ++ tailWord_6662232).sum := by decide
  have hdescent : baseEnd_6662232 < baseStart_6662232 := by decide
  rcases family_descends (prefixWord ++ tailWord_6662232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6662241 : List Nat := [1, 2, 3, 1, 1, 2, 1, 2, 3, 1, 6]
def baseStart_6662241 : Nat := 118140960795 + 6662241 * 2 ^ 59
def prefixEnd_6662241 : Nat := 4983230072969 + 3 ^ 40 * 6662241 * 2
def baseEnd_6662241 : Nat := 3420931869090773685148417

theorem tailTrace_6662241 : CollatzResearch.WordTrace tailWord_6662241 prefixEnd_6662241 3420931869090773685148417 := by
  unfold tailWord_6662241
  simp only [CollatzResearch.WordTrace]
  refine ⟨242991891856846152021418577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161994594571230768014279051 242991891856846152021418577)
  ·
    refine ⟨182243918892634614016063933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242991891856846152021418577 182243918892634614016063933)
    ·
      refine ⟨68341469584737980256023975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182243918892634614016063933 68341469584737980256023975)
      ·
        refine ⟨102512204377106970384035963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68341469584737980256023975 102512204377106970384035963)
        ·
          refine ⟨153768306565660455576053945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102512204377106970384035963 153768306565660455576053945)
          ·
            refine ⟨115326229924245341682040459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153768306565660455576053945 115326229924245341682040459)
            ·
              refine ⟨172989344886368012523060689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115326229924245341682040459 172989344886368012523060689)
              ·
                refine ⟨129742008664776009392295517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 172989344886368012523060689 129742008664776009392295517)
                ·
                  refine ⟨48653253249291003522110819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 129742008664776009392295517 48653253249291003522110819)
                  ·
                    refine ⟨72979879873936505283166229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48653253249291003522110819 72979879873936505283166229)
                    ·
                      refine ⟨3420931869090773685148417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72979879873936505283166229 3420931869090773685148417)
                      ·
                        rfl

theorem cell23_6662241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 2, 3, 1, 6].length) (baseStart_6662241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6662241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6662241 prefixEnd_6662241 := by exact prefixLift 6662241
  have htrace : WordTrace (prefixWord ++ tailWord_6662241) baseStart_6662241 baseEnd_6662241 := by
    simpa [prefixWord, tailWord_6662241, baseEnd_6662241] using wordTrace_append hprefix tailTrace_6662241
  have hstable : (prefixWord ++ tailWord_6662241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6662241).length < 2 ^ (prefixWord ++ tailWord_6662241).sum := by decide
  have hdescent : baseEnd_6662241 < baseStart_6662241 := by decide
  rcases family_descends (prefixWord ++ tailWord_6662241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6662242 : List Nat := [3, 3, 2, 2, 2, 1, 1, 3, 1, 5]
def baseStart_6662242 : Nat := 118140960795 + 6662242 * 2 ^ 59
def prefixEnd_6662242 : Nat := 4983230072969 + 3 ^ 40 * 6662242 * 2
def baseEnd_6662242 : Nat := 1140310794190476060411971

theorem tailTrace_6662242 : CollatzResearch.WordTrace tailWord_6662242 prefixEnd_6662242 1140310794190476060411971 := by
  unfold tailWord_6662242
  simp only [CollatzResearch.WordTrace]
  refine ⟨60747982082460632298051245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161994618886561686128136653 60747982082460632298051245)
  ·
    refine ⟨22780493280922737111769217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60747982082460632298051245 22780493280922737111769217)
    ·
      refine ⟨17085369960692052833826913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22780493280922737111769217 17085369960692052833826913)
      ·
        refine ⟨12814027470519039625370185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17085369960692052833826913 12814027470519039625370185)
        ·
          refine ⟨9610520602889279719027639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12814027470519039625370185 9610520602889279719027639)
          ·
            refine ⟨14415780904333919578541459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9610520602889279719027639 14415780904333919578541459)
            ·
              refine ⟨21623671356500879367812189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14415780904333919578541459 21623671356500879367812189)
              ·
                refine ⟨8108876758687829762929571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21623671356500879367812189 8108876758687829762929571)
                ·
                  refine ⟨12163315138031744644394357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8108876758687829762929571 12163315138031744644394357)
                  ·
                    refine ⟨1140310794190476060411971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12163315138031744644394357 1140310794190476060411971)
                    ·
                      rfl

theorem cell23_6662242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 3, 1, 5].length) (baseStart_6662242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6662242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6662242 prefixEnd_6662242 := by exact prefixLift 6662242
  have htrace : WordTrace (prefixWord ++ tailWord_6662242) baseStart_6662242 baseEnd_6662242 := by
    simpa [prefixWord, tailWord_6662242, baseEnd_6662242] using wordTrace_append hprefix tailTrace_6662242
  have hstable : (prefixWord ++ tailWord_6662242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6662242).length < 2 ^ (prefixWord ++ tailWord_6662242).sum := by decide
  have hdescent : baseEnd_6662242 < baseStart_6662242 := by decide
  rcases family_descends (prefixWord ++ tailWord_6662242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6662245 : List Nat := [1, 3, 1, 3, 2, 3, 1, 3, 1, 1, 4]
def baseStart_6662245 : Nat := 118140960795 + 6662245 * 2 ^ 59
def prefixEnd_6662245 : Nat := 4983230072969 + 3 ^ 40 * 6662245 * 2
def baseEnd_6662245 : Nat := 3420933923013391669498399

theorem tailTrace_6662245 : CollatzResearch.WordTrace tailWord_6662245 prefixEnd_6662245 3420933923013391669498399 := by
  unfold tailWord_6662245
  simp only [CollatzResearch.WordTrace]
  refine ⟨242992037748831660704564189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161994691832554440469709459 242992037748831660704564189)
  ·
    refine ⟨91122014155811872764211571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 242992037748831660704564189 91122014155811872764211571)
    ·
      refine ⟨136683021233717809146317357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91122014155811872764211571 136683021233717809146317357)
      ·
        refine ⟨51256132962644178429869009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 136683021233717809146317357 51256132962644178429869009)
        ·
          refine ⟨38442099721983133822401757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51256132962644178429869009 38442099721983133822401757)
          ·
            refine ⟨14415787395743675183400659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38442099721983133822401757 14415787395743675183400659)
            ·
              refine ⟨21623681093615512775100989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14415787395743675183400659 21623681093615512775100989)
              ·
                refine ⟨8108880410105817290662871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21623681093615512775100989 8108880410105817290662871)
                ·
                  refine ⟨12163320615158725935994307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8108880410105817290662871 12163320615158725935994307)
                  ·
                    refine ⟨18244980922738088903991461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12163320615158725935994307 18244980922738088903991461)
                    ·
                      refine ⟨3420933923013391669498399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18244980922738088903991461 3420933923013391669498399)
                      ·
                        rfl

theorem cell23_6662245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 3, 1, 1, 4].length) (baseStart_6662245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6662245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6662245 prefixEnd_6662245 := by exact prefixLift 6662245
  have htrace : WordTrace (prefixWord ++ tailWord_6662245) baseStart_6662245 baseEnd_6662245 := by
    simpa [prefixWord, tailWord_6662245, baseEnd_6662245] using wordTrace_append hprefix tailTrace_6662245
  have hstable : (prefixWord ++ tailWord_6662245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6662245).length < 2 ^ (prefixWord ++ tailWord_6662245).sum := by decide
  have hdescent : baseEnd_6662245 < baseStart_6662245 := by decide
  rcases family_descends (prefixWord ++ tailWord_6662245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6662255 : List Nat := [1, 1, 2, 1, 3, 4, 3, 2, 2, 4]
def baseStart_6662255 : Nat := 118140960795 + 6662255 * 2 ^ 59
def prefixEnd_6662255 : Nat := 4983230072969 + 3 ^ 40 * 6662255 * 2
def baseEnd_6662255 : Nat := 1140313019273312210124451

theorem tailTrace_6662255 : CollatzResearch.WordTrace tailWord_6662255 prefixEnd_6662255 1140313019273312210124451 := by
  unfold tailWord_6662255
  simp only [CollatzResearch.WordTrace]
  refine ⟨242992402478795432412428219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161994934985863621608285479 242992402478795432412428219)
  ·
    refine ⟨364488603718193148618642329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242992402478795432412428219 364488603718193148618642329)
    ·
      refine ⟨273366452788644861463981747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 364488603718193148618642329 273366452788644861463981747)
      ·
        refine ⟨410049679182967292195972621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273366452788644861463981747 410049679182967292195972621)
        ·
          refine ⟨153768629693612734573489733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 410049679182967292195972621 153768629693612734573489733)
          ·
            refine ⟨28831618067552387732529325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 153768629693612734573489733 28831618067552387732529325)
            ·
              refine ⟨10811856775332145399698497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28831618067552387732529325 10811856775332145399698497)
              ·
                refine ⟨8108892581499109049773873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10811856775332145399698497 8108892581499109049773873)
                ·
                  refine ⟨6081669436124331787330405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8108892581499109049773873 6081669436124331787330405)
                  ·
                    refine ⟨1140313019273312210124451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6081669436124331787330405 1140313019273312210124451)
                    ·
                      rfl

theorem cell23_6662255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 3, 2, 2, 4].length) (baseStart_6662255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6662255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6662255 prefixEnd_6662255 := by exact prefixLift 6662255
  have htrace : WordTrace (prefixWord ++ tailWord_6662255) baseStart_6662255 baseEnd_6662255 := by
    simpa [prefixWord, tailWord_6662255, baseEnd_6662255] using wordTrace_append hprefix tailTrace_6662255
  have hstable : (prefixWord ++ tailWord_6662255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6662255).length < 2 ^ (prefixWord ++ tailWord_6662255).sum := by decide
  have hdescent : baseEnd_6662255 < baseStart_6662255 := by decide
  rcases family_descends (prefixWord ++ tailWord_6662255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6662275 : List Nat := [1, 1, 1, 3, 3, 5, 1, 1, 1, 2, 4]
def baseStart_6662275 : Nat := 118140960795 + 6662275 * 2 ^ 59
def prefixEnd_6662275 : Nat := 4983230072969 + 3 ^ 40 * 6662275 * 2
def baseEnd_6662275 : Nat := 3420949327433026552123261

theorem tailTrace_6662275 : CollatzResearch.WordTrace tailWord_6662275 prefixEnd_6662275 3420949327433026552123261 := by
  unfold tailWord_6662275
  simp only [CollatzResearch.WordTrace]
  refine ⟨242993131938722975828156279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161995421292481983885437519 242993131938722975828156279)
  ·
    refine ⟨364489697908084463742234419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242993131938722975828156279 364489697908084463742234419)
    ·
      refine ⟨546734546862126695613351629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 364489697908084463742234419 546734546862126695613351629)
      ·
        refine ⟨205025455073297510855006861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 546734546862126695613351629 205025455073297510855006861)
        ·
          refine ⟨76884545652486566570627573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 205025455073297510855006861 76884545652486566570627573)
          ·
            refine ⟨7207926154920615615996335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 76884545652486566570627573 7207926154920615615996335)
            ·
              refine ⟨10811889232380923423994503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7207926154920615615996335 10811889232380923423994503)
              ·
                refine ⟨16217833848571385135991755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10811889232380923423994503 16217833848571385135991755)
                ·
                  refine ⟨24326750772857077703987633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16217833848571385135991755 24326750772857077703987633)
                  ·
                    refine ⟨18245063079642808277990725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24326750772857077703987633 18245063079642808277990725)
                    ·
                      refine ⟨3420949327433026552123261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18245063079642808277990725 3420949327433026552123261)
                      ·
                        rfl

theorem cell23_6662275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 1, 1, 1, 2, 4].length) (baseStart_6662275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6662275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6662275 prefixEnd_6662275 := by exact prefixLift 6662275
  have htrace : WordTrace (prefixWord ++ tailWord_6662275) baseStart_6662275 baseEnd_6662275 := by
    simpa [prefixWord, tailWord_6662275, baseEnd_6662275] using wordTrace_append hprefix tailTrace_6662275
  have hstable : (prefixWord ++ tailWord_6662275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6662275).length < 2 ^ (prefixWord ++ tailWord_6662275).sum := by decide
  have hdescent : baseEnd_6662275 < baseStart_6662275 := by decide
  rcases family_descends (prefixWord ++ tailWord_6662275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6662282 : List Nat := [3, 1, 2, 3, 1, 3, 2, 2, 1, 2, 3]
def baseStart_6662282 : Nat := 118140960795 + 6662282 * 2 ^ 59
def prefixEnd_6662282 : Nat := 4983230072969 + 3 ^ 40 * 6662282 * 2
def baseEnd_6662282 : Nat := 3420952921797608024735729

theorem tailTrace_6662282 : CollatzResearch.WordTrace tailWord_6662282 prefixEnd_6662282 3420952921797608024735729 := by
  unfold tailWord_6662282
  simp only [CollatzResearch.WordTrace]
  refine ⟨60748346812424404005915275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 161995591499798410682440733 60748346812424404005915275)
  ·
    refine ⟨91122520218636606008872913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60748346812424404005915275 91122520218636606008872913)
    ·
      refine ⟨68341890163977454506654685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91122520218636606008872913 68341890163977454506654685)
      ·
        refine ⟨25628208811491545439995507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68341890163977454506654685 25628208811491545439995507)
        ·
          refine ⟨38442313217237318159993261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25628208811491545439995507 38442313217237318159993261)
          ·
            refine ⟨14415867456463994309997473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38442313217237318159993261 14415867456463994309997473)
            ·
              refine ⟨10811900592347995732498105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14415867456463994309997473 10811900592347995732498105)
              ·
                refine ⟨8108925444260996799373579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10811900592347995732498105 8108925444260996799373579)
                ·
                  refine ⟨12163388166391495199060369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8108925444260996799373579 12163388166391495199060369)
                  ·
                    refine ⟨9122541124793621399295277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12163388166391495199060369 9122541124793621399295277)
                    ·
                      refine ⟨3420952921797608024735729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9122541124793621399295277 3420952921797608024735729)
                      ·
                        rfl

theorem cell23_6662282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 2, 2, 1, 2, 3].length) (baseStart_6662282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6662282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6662282 prefixEnd_6662282 := by exact prefixLift 6662282
  have htrace : WordTrace (prefixWord ++ tailWord_6662282) baseStart_6662282 baseEnd_6662282 := by
    simpa [prefixWord, tailWord_6662282, baseEnd_6662282] using wordTrace_append hprefix tailTrace_6662282
  have hstable : (prefixWord ++ tailWord_6662282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6662282).length < 2 ^ (prefixWord ++ tailWord_6662282).sum := by decide
  have hdescent : baseEnd_6662282 < baseStart_6662282 := by decide
  rcases family_descends (prefixWord ++ tailWord_6662282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6662302 : List Nat := [4, 3, 1, 1, 4, 1, 9]
def baseStart_6662302 : Nat := 118140960795 + 6662302 * 2 ^ 59
def prefixEnd_6662302 : Nat := 4983230072969 + 3 ^ 40 * 6662302 * 2
def baseEnd_6662302 : Nat := 42234113474206147487477

theorem tailTrace_6662302 : CollatzResearch.WordTrace tailWord_6662302 prefixEnd_6662302 42234113474206147487477 := by
  unfold tailWord_6662302
  simp only [CollatzResearch.WordTrace]
  refine ⟨30374264588703144929923645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 161996077806416772959592773 30374264588703144929923645)
  ·
    refine ⟨11390349220763679348721367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30374264588703144929923645 11390349220763679348721367)
    ·
      refine ⟨17085523831145519023082051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11390349220763679348721367 17085523831145519023082051)
      ·
        refine ⟨25628285746718278534623077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17085523831145519023082051 25628285746718278534623077)
        ·
          refine ⟨4805303577509677225241827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25628285746718278534623077 4805303577509677225241827)
          ·
            refine ⟨7207955366264515837862741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4805303577509677225241827 7207955366264515837862741)
            ·
              refine ⟨42234113474206147487477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7207955366264515837862741 42234113474206147487477)
              ·
                rfl

theorem cell23_6662302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 9].length) (baseStart_6662302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6662302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6662302 prefixEnd_6662302 := by exact prefixLift 6662302
  have htrace : WordTrace (prefixWord ++ tailWord_6662302) baseStart_6662302 baseEnd_6662302 := by
    simpa [prefixWord, tailWord_6662302, baseEnd_6662302] using wordTrace_append hprefix tailTrace_6662302
  have hstable : (prefixWord ++ tailWord_6662302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6662302).length < 2 ^ (prefixWord ++ tailWord_6662302).sum := by decide
  have hdescent : baseEnd_6662302 < baseStart_6662302 := by decide
  rcases family_descends (prefixWord ++ tailWord_6662302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6662335 : List Nat := [1, 1, 2, 2, 2, 2, 1, 5, 1, 4, 2]
def baseStart_6662335 : Nat := 118140960795 + 6662335 * 2 ^ 59
def prefixEnd_6662335 : Nat := 4983230072969 + 3 ^ 40 * 6662335 * 2
def baseEnd_6662335 : Nat := 3420980136272296317372985

theorem tailTrace_6662335 : CollatzResearch.WordTrace tailWord_6662335 prefixEnd_6662335 3420980136272296317372985 := by
  unfold tailWord_6662335
  simp only [CollatzResearch.WordTrace]
  refine ⟨242995320318505606075340459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161996880212337070716893639 242995320318505606075340459)
  ·
    refine ⟨364492980477758409113010689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 242995320318505606075340459 364492980477758409113010689)
    ·
      refine ⟨273369735358318806834758017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 364492980477758409113010689 273369735358318806834758017)
      ·
        refine ⟨205027301518739105126068513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 273369735358318806834758017 205027301518739105126068513)
        ·
          refine ⟨153770476139054328844551385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 205027301518739105126068513 153770476139054328844551385)
          ·
            refine ⟨115327857104290746633413539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153770476139054328844551385 115327857104290746633413539)
            ·
              refine ⟨172991785656436119950120309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115327857104290746633413539 172991785656436119950120309)
              ·
                refine ⟨16217979905290886245323779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 172991785656436119950120309 16217979905290886245323779)
                ·
                  refine ⟨24326969857936329367985669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16217979905290886245323779 24326969857936329367985669)
                  ·
                    refine ⟨4561306848363061756497313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24326969857936329367985669 4561306848363061756497313)
                    ·
                      refine ⟨3420980136272296317372985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4561306848363061756497313 3420980136272296317372985)
                      ·
                        rfl

theorem cell23_6662335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 5, 1, 4, 2].length) (baseStart_6662335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6662335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6662335 prefixEnd_6662335 := by exact prefixLift 6662335
  have htrace : WordTrace (prefixWord ++ tailWord_6662335) baseStart_6662335 baseEnd_6662335 := by
    simpa [prefixWord, tailWord_6662335, baseEnd_6662335] using wordTrace_append hprefix tailTrace_6662335
  have hstable : (prefixWord ++ tailWord_6662335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6662335).length < 2 ^ (prefixWord ++ tailWord_6662335).sum := by decide
  have hdescent : baseEnd_6662335 < baseStart_6662335 := by decide
  rcases family_descends (prefixWord ++ tailWord_6662335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6662369 : List Nat := [1, 2, 3, 1, 3, 1, 4, 2, 2, 2, 2]
def baseStart_6662369 : Nat := 118140960795 + 6662369 * 2 ^ 59
def prefixEnd_6662369 : Nat := 4983230072969 + 3 ^ 40 * 6662369 * 2
def baseEnd_6662369 : Nat := 3420997594614549184347829

theorem tailTrace_6662369 : CollatzResearch.WordTrace tailWord_6662369 prefixEnd_6662369 3420997594614549184347829 := by
  unfold tailWord_6662369
  simp only [CollatzResearch.WordTrace]
  refine ⟨242996560400382429882078161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 161997706933588286588052107 242996560400382429882078161)
  ·
    refine ⟨182247420300286822411558621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242996560400382429882078161 182247420300286822411558621)
    ·
      refine ⟨68342782612607558404334483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182247420300286822411558621 68342782612607558404334483)
      ·
        refine ⟨102514173918911337606501725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68342782612607558404334483 102514173918911337606501725)
        ·
          refine ⟨38442815219591751602438147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 102514173918911337606501725 38442815219591751602438147)
          ·
            refine ⟨57664222829387627403657221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38442815219591751602438147 57664222829387627403657221)
            ·
              refine ⟨10812041780510180138185729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57664222829387627403657221 10812041780510180138185729)
              ·
                refine ⟨8109031335382635103639297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10812041780510180138185729 8109031335382635103639297)
                ·
                  refine ⟨6081773501536976327729473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8109031335382635103639297 6081773501536976327729473)
                  ·
                    refine ⟨4561330126152732245797105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6081773501536976327729473 4561330126152732245797105)
                    ·
                      refine ⟨3420997594614549184347829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4561330126152732245797105 3420997594614549184347829)
                      ·
                        rfl

theorem cell23_6662369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 4, 2, 2, 2, 2].length) (baseStart_6662369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6662369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6662369 prefixEnd_6662369 := by exact prefixLift 6662369
  have htrace : WordTrace (prefixWord ++ tailWord_6662369) baseStart_6662369 baseEnd_6662369 := by
    simpa [prefixWord, tailWord_6662369, baseEnd_6662369] using wordTrace_append hprefix tailTrace_6662369
  have hstable : (prefixWord ++ tailWord_6662369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6662369).length < 2 ^ (prefixWord ++ tailWord_6662369).sum := by decide
  have hdescent : baseEnd_6662369 < baseStart_6662369 := by decide
  rcases family_descends (prefixWord ++ tailWord_6662369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6662462 : List Nat := [4, 2, 1, 2, 1, 2, 2, 1, 1, 4, 3]
def baseStart_6662462 : Nat := 118140960795 + 6662462 * 2 ^ 59
def prefixEnd_6662462 : Nat := 4983230072969 + 3 ^ 40 * 6662462 * 2
def baseEnd_6662462 : Nat := 3421045348315417320484901

theorem tailTrace_6662462 : CollatzResearch.WordTrace tailWord_6662462 prefixEnd_6662462 3421045348315417320484901 := by
  unfold tailWord_6662462
  simp only [CollatzResearch.WordTrace]
  refine ⟨30374994048630688345651705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 161999968259363671176809093 30374994048630688345651705)
  ·
    refine ⟨22781245536473016259238779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30374994048630688345651705 22781245536473016259238779)
    ·
      refine ⟨34171868304709524388858169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22781245536473016259238779 34171868304709524388858169)
      ·
        refine ⟨25628901228532143291643627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34171868304709524388858169 25628901228532143291643627)
        ·
          refine ⟨38443351842798214937465441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25628901228532143291643627 38443351842798214937465441)
          ·
            refine ⟨28832513882098661203099081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38443351842798214937465441 28832513882098661203099081)
            ·
              refine ⟨21624385411573995902324311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28832513882098661203099081 21624385411573995902324311)
              ·
                refine ⟨32436578117360993853486467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21624385411573995902324311 32436578117360993853486467)
                ·
                  refine ⟨48654867176041490780229701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32436578117360993853486467 48654867176041490780229701)
                  ·
                    refine ⟨9122787595507779521293069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48654867176041490780229701 9122787595507779521293069)
                    ·
                      refine ⟨3421045348315417320484901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9122787595507779521293069 3421045348315417320484901)
                      ·
                        rfl

theorem cell23_6662462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 1, 1, 4, 3].length) (baseStart_6662462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6662462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6662462 prefixEnd_6662462 := by exact prefixLift 6662462
  have htrace : WordTrace (prefixWord ++ tailWord_6662462) baseStart_6662462 baseEnd_6662462 := by
    simpa [prefixWord, tailWord_6662462, baseEnd_6662462] using wordTrace_append hprefix tailTrace_6662462
  have hstable : (prefixWord ++ tailWord_6662462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6662462).length < 2 ^ (prefixWord ++ tailWord_6662462).sum := by decide
  have hdescent : baseEnd_6662462 < baseStart_6662462 := by decide
  rcases family_descends (prefixWord ++ tailWord_6662462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6662512 : List Nat := [2, 1, 1, 1, 4, 3, 3, 2, 1, 5]
def baseStart_6662512 : Nat := 118140960795 + 6662512 * 2 ^ 59
def prefixEnd_6662512 : Nat := 4983230072969 + 3 ^ 40 * 6662512 * 2
def baseEnd_6662512 : Nat := 1140357007449380708286557

theorem tailTrace_6662512 : CollatzResearch.WordTrace tailWord_6662512 prefixEnd_6662512 1140357007449380708286557 := by
  unfold tailWord_6662512
  simp only [CollatzResearch.WordTrace]
  refine ⟨121500888019432182652266895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162001184025909576869689193 121500888019432182652266895)
  ·
    refine ⟨182251332029148273978400343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121500888019432182652266895 182251332029148273978400343)
    ·
      refine ⟨273376998043722410967600515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182251332029148273978400343 273376998043722410967600515)
      ·
        refine ⟨410065497065583616451400773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273376998043722410967600515 410065497065583616451400773)
        ·
          refine ⟨76887280699796928084637645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 410065497065583616451400773 76887280699796928084637645)
          ·
            refine ⟨28832730262423848031739117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76887280699796928084637645 28832730262423848031739117)
            ·
              refine ⟨10812273848408943011902169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28832730262423848031739117 10812273848408943011902169)
              ·
                refine ⟨8109205386306707258926627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10812273848408943011902169 8109205386306707258926627)
                ·
                  refine ⟨12163808079460060888389941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8109205386306707258926627 12163808079460060888389941)
                  ·
                    refine ⟨1140357007449380708286557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12163808079460060888389941 1140357007449380708286557)
                    ·
                      rfl

theorem cell23_6662512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 3, 2, 1, 5].length) (baseStart_6662512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6662512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6662512 prefixEnd_6662512 := by exact prefixLift 6662512
  have htrace : WordTrace (prefixWord ++ tailWord_6662512) baseStart_6662512 baseEnd_6662512 := by
    simpa [prefixWord, tailWord_6662512, baseEnd_6662512] using wordTrace_append hprefix tailTrace_6662512
  have hstable : (prefixWord ++ tailWord_6662512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6662512).length < 2 ^ (prefixWord ++ tailWord_6662512).sum := by decide
  have hdescent : baseEnd_6662512 < baseStart_6662512 := by decide
  rcases family_descends (prefixWord ++ tailWord_6662512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6662515 : List Nat := [1, 1, 1, 2, 2, 1, 2, 5, 3, 1, 4]
def baseStart_6662515 : Nat := 118140960795 + 6662515 * 2 ^ 59
def prefixEnd_6662515 : Nat := 4983230072969 + 3 ^ 40 * 6662515 * 2
def baseEnd_6662515 : Nat := 3421072562790105613122157

theorem tailTrace_6662515 : CollatzResearch.WordTrace tailWord_6662515 prefixEnd_6662515 3421072562790105613122157 := by
  unfold tailWord_6662515
  simp only [CollatzResearch.WordTrace]
  refine ⟨243001885457853496816892999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162001256971902331211261999 243001885457853496816892999)
  ·
    refine ⟨364502828186780245225339499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243001885457853496816892999 364502828186780245225339499)
    ·
      refine ⟨546754242280170367838009249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 364502828186780245225339499 546754242280170367838009249)
      ·
        refine ⟨410065681710127775878506937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 546754242280170367838009249 410065681710127775878506937)
        ·
          refine ⟨307549261282595831908880203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 410065681710127775878506937 307549261282595831908880203)
          ·
            refine ⟨461323891923893747863320305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 307549261282595831908880203 461323891923893747863320305)
            ·
              refine ⟨345992918942920310897490229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 461323891923893747863320305 345992918942920310897490229)
              ·
                refine ⟨32436836150898779146639709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 345992918942920310897490229 32436836150898779146639709)
                ·
                  refine ⟨12163813556587042179989891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32436836150898779146639709 12163813556587042179989891)
                  ·
                    refine ⟨18245720334880563269984837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12163813556587042179989891 18245720334880563269984837)
                    ·
                      refine ⟨3421072562790105613122157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18245720334880563269984837 3421072562790105613122157)
                      ·
                        rfl

theorem cell23_6662515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 5, 3, 1, 4].length) (baseStart_6662515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6662515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6662515 prefixEnd_6662515 := by exact prefixLift 6662515
  have htrace : WordTrace (prefixWord ++ tailWord_6662515) baseStart_6662515 baseEnd_6662515 := by
    simpa [prefixWord, tailWord_6662515, baseEnd_6662515] using wordTrace_append hprefix tailTrace_6662515
  have hstable : (prefixWord ++ tailWord_6662515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6662515).length < 2 ^ (prefixWord ++ tailWord_6662515).sum := by decide
  have hdescent : baseEnd_6662515 < baseStart_6662515 := by decide
  rcases family_descends (prefixWord ++ tailWord_6662515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6662525 : List Nat := [1, 4, 1, 1, 2, 3, 1, 1, 3, 6]
def baseStart_6662525 : Nat := 118140960795 + 6662525 * 2 ^ 59
def prefixEnd_6662525 : Nat := 4983230072969 + 3 ^ 40 * 6662525 * 2
def baseEnd_6662525 : Nat := 1140359232532216857999037

theorem tailTrace_6662525 : CollatzResearch.WordTrace tailWord_6662525 prefixEnd_6662525 1140359232532216857999037 := by
  unfold tailWord_6662525
  simp only [CollatzResearch.WordTrace]
  refine ⟨243002250187817268524757029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162001500125211512349838019 243002250187817268524757029)
  ·
    refine ⟨45562921910215737848391943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 243002250187817268524757029 45562921910215737848391943)
    ·
      refine ⟨68344382865323606772587915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45562921910215737848391943 68344382865323606772587915)
      ·
        refine ⟨102516574297985410158881873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68344382865323606772587915 102516574297985410158881873)
        ·
          refine ⟨76887430723489057619161405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102516574297985410158881873 76887430723489057619161405)
          ·
            refine ⟨28832786521308396607185527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76887430723489057619161405 28832786521308396607185527)
            ·
              refine ⟨43249179781962594910778291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28832786521308396607185527 43249179781962594910778291)
              ·
                refine ⟨64873769672943892366167437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43249179781962594910778291 64873769672943892366167437)
                ·
                  refine ⟨24327663627353959637312789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64873769672943892366167437 24327663627353959637312789)
                  ·
                    refine ⟨1140359232532216857999037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24327663627353959637312789 1140359232532216857999037)
                    ·
                      rfl

theorem cell23_6662525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 1, 3, 6].length) (baseStart_6662525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6662525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6662525 prefixEnd_6662525 := by exact prefixLift 6662525
  have htrace : WordTrace (prefixWord ++ tailWord_6662525) baseStart_6662525 baseEnd_6662525 := by
    simpa [prefixWord, tailWord_6662525, baseEnd_6662525] using wordTrace_append hprefix tailTrace_6662525
  have hstable : (prefixWord ++ tailWord_6662525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6662525).length < 2 ^ (prefixWord ++ tailWord_6662525).sum := by decide
  have hdescent : baseEnd_6662525 < baseStart_6662525 := by decide
  rcases family_descends (prefixWord ++ tailWord_6662525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6662549 : List Nat := [1, 3, 2, 1, 1, 2, 1, 5, 3, 2, 2]
def baseStart_6662549 : Nat := 118140960795 + 6662549 * 2 ^ 59
def prefixEnd_6662549 : Nat := 4983230072969 + 3 ^ 40 * 6662549 * 2
def baseEnd_6662549 : Nat := 3421090021132358480097001

theorem tailTrace_6662549 : CollatzResearch.WordTrace tailWord_6662549 prefixEnd_6662549 3421090021132358480097001 := by
  unfold tailWord_6662549
  simp only [CollatzResearch.WordTrace]
  refine ⟨243003125539730320623630701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162002083693153547082420467 243003125539730320623630701)
  ·
    refine ⟨91126172077398870233861513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 243003125539730320623630701 91126172077398870233861513)
    ·
      refine ⟨68344629058049152675396135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91126172077398870233861513 68344629058049152675396135)
      ·
        refine ⟨102516943587073729013094203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68344629058049152675396135 102516943587073729013094203)
        ·
          refine ⟨153775415380610593519641305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102516943587073729013094203 153775415380610593519641305)
          ·
            refine ⟨115331561535457945139730979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 153775415380610593519641305 115331561535457945139730979)
            ·
              refine ⟨172997342303186917709596469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115331561535457945139730979 172997342303186917709596469)
              ·
                refine ⟨16218500840923773535274669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 172997342303186917709596469 16218500840923773535274669)
                ·
                  refine ⟨6081937815346415075728001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16218500840923773535274669 6081937815346415075728001)
                  ·
                    refine ⟨4561453361509811306796001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6081937815346415075728001 4561453361509811306796001)
                    ·
                      refine ⟨3421090021132358480097001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4561453361509811306796001 3421090021132358480097001)
                      ·
                        rfl

theorem cell23_6662549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 5, 3, 2, 2].length) (baseStart_6662549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6662549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6662549 prefixEnd_6662549 := by exact prefixLift 6662549
  have htrace : WordTrace (prefixWord ++ tailWord_6662549) baseStart_6662549 baseEnd_6662549 := by
    simpa [prefixWord, tailWord_6662549, baseEnd_6662549] using wordTrace_append hprefix tailTrace_6662549
  have hstable : (prefixWord ++ tailWord_6662549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6662549).length < 2 ^ (prefixWord ++ tailWord_6662549).sum := by decide
  have hdescent : baseEnd_6662549 < baseStart_6662549 := by decide
  rcases family_descends (prefixWord ++ tailWord_6662549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6662580 : List Nat := [2, 5, 2, 2, 1, 2, 2, 1, 1, 5]
def baseStart_6662580 : Nat := 118140960795 + 6662580 * 2 ^ 59
def prefixEnd_6662580 : Nat := 4983230072969 + 3 ^ 40 * 6662580 * 2
def baseEnd_6662580 : Nat := 1140368646344215952936453

theorem tailTrace_6662580 : CollatzResearch.WordTrace tailWord_6662580 prefixEnd_6662580 1140368646344215952936453 := by
  unfold tailWord_6662580
  simp only [CollatzResearch.WordTrace]
  refine ⟨121502128101309006459004597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162002837468412008612006129 121502128101309006459004597)
  ·
    refine ⟨11390824509497719355531681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 121502128101309006459004597 11390824509497719355531681)
    ·
      refine ⟨8543118382123289516648761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11390824509497719355531681 8543118382123289516648761)
      ·
        refine ⟨6407338786592467137486571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8543118382123289516648761 6407338786592467137486571)
        ·
          refine ⟨9611008179888700706229857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6407338786592467137486571 9611008179888700706229857)
          ·
            refine ⟨7208256134916525529672393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9611008179888700706229857 7208256134916525529672393)
            ·
              refine ⟨5406192101187394147254295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7208256134916525529672393 5406192101187394147254295)
              ·
                refine ⟨8109288151781091220881443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5406192101187394147254295 8109288151781091220881443)
                ·
                  refine ⟨12163932227671636831322165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8109288151781091220881443 12163932227671636831322165)
                  ·
                    refine ⟨1140368646344215952936453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12163932227671636831322165 1140368646344215952936453)
                    ·
                      rfl

theorem cell23_6662580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_6662580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6662580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6662580 prefixEnd_6662580 := by exact prefixLift 6662580
  have htrace : WordTrace (prefixWord ++ tailWord_6662580) baseStart_6662580 baseEnd_6662580 := by
    simpa [prefixWord, tailWord_6662580, baseEnd_6662580] using wordTrace_append hprefix tailTrace_6662580
  have hstable : (prefixWord ++ tailWord_6662580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6662580).length < 2 ^ (prefixWord ++ tailWord_6662580).sum := by decide
  have hdescent : baseEnd_6662580 < baseStart_6662580 := by decide
  rcases family_descends (prefixWord ++ tailWord_6662580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6662583 : List Nat := [1, 1, 3, 1, 3, 4, 2, 3, 1, 2, 2]
def baseStart_6662583 : Nat := 118140960795 + 6662583 * 2 ^ 59
def prefixEnd_6662583 : Nat := 4983230072969 + 3 ^ 40 * 6662583 * 2
def baseEnd_6662583 : Nat := 3421107479474611347071845

theorem tailTrace_6662583 : CollatzResearch.WordTrace tailWord_6662583 prefixEnd_6662583 3421107479474611347071845 := by
  unfold tailWord_6662583
  simp only [CollatzResearch.WordTrace]
  refine ⟨243004365621607144430368403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162002910414404762953578935 243004365621607144430368403)
  ·
    refine ⟨364506548432410716645552605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243004365621607144430368403 364506548432410716645552605)
    ·
      refine ⟨136689955662154018742082227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 364506548432410716645552605 136689955662154018742082227)
      ·
        refine ⟨205034933493231028113123341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136689955662154018742082227 205034933493231028113123341)
        ·
          refine ⟨76888100059961635542421253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 205034933493231028113123341 76888100059961635542421253)
          ·
            refine ⟨14416518761242806664203985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76888100059961635542421253 14416518761242806664203985)
            ·
              refine ⟨10812389070932104998152989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14416518761242806664203985 10812389070932104998152989)
              ·
                refine ⟨4054645901599539374307371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10812389070932104998152989 4054645901599539374307371)
                ·
                  refine ⟨6081968852399309061461057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4054645901599539374307371 6081968852399309061461057)
                  ·
                    refine ⟨4561476639299481796095793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6081968852399309061461057 4561476639299481796095793)
                    ·
                      refine ⟨3421107479474611347071845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4561476639299481796095793 3421107479474611347071845)
                      ·
                        rfl

theorem cell23_6662583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 2, 3, 1, 2, 2].length) (baseStart_6662583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6662583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6662583 prefixEnd_6662583 := by exact prefixLift 6662583
  have htrace : WordTrace (prefixWord ++ tailWord_6662583) baseStart_6662583 baseEnd_6662583 := by
    simpa [prefixWord, tailWord_6662583, baseEnd_6662583] using wordTrace_append hprefix tailTrace_6662583
  have hstable : (prefixWord ++ tailWord_6662583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6662583).length < 2 ^ (prefixWord ++ tailWord_6662583).sum := by decide
  have hdescent : baseEnd_6662583 < baseStart_6662583 := by decide
  rcases family_descends (prefixWord ++ tailWord_6662583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6662593 : List Nat := [1, 2, 7, 1, 1, 1, 1, 1, 4, 4]
def baseStart_6662593 : Nat := 118140960795 + 6662593 * 2 ^ 59
def prefixEnd_6662593 : Nat := 4983230072969 + 3 ^ 40 * 6662593 * 2
def baseEnd_6662593 : Nat := 1140370871427052102648933

theorem tailTrace_6662593 : CollatzResearch.WordTrace tailWord_6662593 prefixEnd_6662593 1140370871427052102648933 := by
  unfold tailWord_6662593
  simp only [CollatzResearch.WordTrace]
  refine ⟨243004730351570916138232433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162003153567713944092154955 243004730351570916138232433)
  ·
    refine ⟨182253547763678187103674325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243004730351570916138232433 182253547763678187103674325)
    ·
      refine ⟨4271567525711207510242367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 182253547763678187103674325 4271567525711207510242367)
      ·
        refine ⟨6407351288566811265363551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4271567525711207510242367 6407351288566811265363551)
        ·
          refine ⟨9611026932850216898045327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6407351288566811265363551 9611026932850216898045327)
          ·
            refine ⟨14416540399275325347067991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9611026932850216898045327 14416540399275325347067991)
            ·
              refine ⟨21624810598912988020601987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14416540399275325347067991 21624810598912988020601987)
              ·
                refine ⟨32437215898369482030902981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21624810598912988020601987 32437215898369482030902981)
                ·
                  refine ⟨6081977980944277880794309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32437215898369482030902981 6081977980944277880794309)
                  ·
                    refine ⟨1140370871427052102648933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6081977980944277880794309 1140370871427052102648933)
                    ·
                      rfl

theorem cell23_6662593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_6662593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6662593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6662593 prefixEnd_6662593 := by exact prefixLift 6662593
  have htrace : WordTrace (prefixWord ++ tailWord_6662593) baseStart_6662593 baseEnd_6662593 := by
    simpa [prefixWord, tailWord_6662593, baseEnd_6662593] using wordTrace_append hprefix tailTrace_6662593
  have hstable : (prefixWord ++ tailWord_6662593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6662593).length < 2 ^ (prefixWord ++ tailWord_6662593).sum := by decide
  have hdescent : baseEnd_6662593 < baseStart_6662593 := by decide
  rcases family_descends (prefixWord ++ tailWord_6662593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6662599 : List Nat := [1, 1, 4, 1, 1, 5, 1, 1, 4, 1, 3]
def baseStart_6662599 : Nat := 118140960795 + 6662599 * 2 ^ 59
def prefixEnd_6662599 : Nat := 4983230072969 + 3 ^ 40 * 6662599 * 2
def baseEnd_6662599 : Nat := 3421115695165083284471771

theorem tailTrace_6662599 : CollatzResearch.WordTrace tailWord_6662599 prefixEnd_6662599 3421115695165083284471771 := by
  unfold tailWord_6662599
  simp only [CollatzResearch.WordTrace]
  refine ⟨243004949189549179162950851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162003299459699452775300567 243004949189549179162950851)
  ·
    refine ⟨364507423784323768744426277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243004949189549179162950851 364507423784323768744426277)
    ·
      refine ⟨68345141959560706639579927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 364507423784323768744426277 68345141959560706639579927)
      ·
        refine ⟨102517712939341059959369891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68345141959560706639579927 102517712939341059959369891)
        ·
          refine ⟨153776569409011589939054837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102517712939341059959369891 153776569409011589939054837)
          ·
            refine ⟨14416553382094836556786391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 153776569409011589939054837 14416553382094836556786391)
            ·
              refine ⟨21624830073142254835179587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14416553382094836556786391 21624830073142254835179587)
              ·
                refine ⟨32437245109713382252769381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21624830073142254835179587 32437245109713382252769381)
                ·
                  refine ⟨6081983458071259172394259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32437245109713382252769381 6081983458071259172394259)
                  ·
                    refine ⟨9122975187106888758591389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6081983458071259172394259 9122975187106888758591389)
                    ·
                      refine ⟨3421115695165083284471771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9122975187106888758591389 3421115695165083284471771)
                      ·
                        rfl

theorem cell23_6662599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 1, 4, 1, 3].length) (baseStart_6662599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6662599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6662599 prefixEnd_6662599 := by exact prefixLift 6662599
  have htrace : WordTrace (prefixWord ++ tailWord_6662599) baseStart_6662599 baseEnd_6662599 := by
    simpa [prefixWord, tailWord_6662599, baseEnd_6662599] using wordTrace_append hprefix tailTrace_6662599
  have hstable : (prefixWord ++ tailWord_6662599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6662599).length < 2 ^ (prefixWord ++ tailWord_6662599).sum := by decide
  have hdescent : baseEnd_6662599 < baseStart_6662599 := by decide
  rcases family_descends (prefixWord ++ tailWord_6662599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6662655 : List Nat := [1, 1, 2, 2, 1, 2, 3, 1, 1, 2, 7]
def baseStart_6662655 : Nat := 118140960795 + 6662655 * 2 ^ 59
def prefixEnd_6662655 : Nat := 4983230072969 + 3 ^ 40 * 6662655 * 2
def baseEnd_6662655 : Nat := 3421144450081735065371513

theorem tailTrace_6662655 : CollatzResearch.WordTrace tailWord_6662655 prefixEnd_6662655 3421144450081735065371513 := by
  unfold tailWord_6662655
  simp only [CollatzResearch.WordTrace]
  refine ⟨243006991677346300726989419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162004661118230867151326279 243006991677346300726989419)
  ·
    refine ⟨364510487516019451090484129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243006991677346300726989419 364510487516019451090484129)
    ·
      refine ⟨273382865637014588317863097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 364510487516019451090484129 273382865637014588317863097)
      ·
        refine ⟨205037149227760941238397323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 273382865637014588317863097 205037149227760941238397323)
        ·
          refine ⟨307555723841641411857595985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205037149227760941238397323 307555723841641411857595985)
          ·
            refine ⟨230666792881231058893196989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 307555723841641411857595985 230666792881231058893196989)
            ·
              refine ⟨86500047330461647084948871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 230666792881231058893196989 86500047330461647084948871)
              ·
                refine ⟨129750070995692470627423307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86500047330461647084948871 129750070995692470627423307)
                ·
                  refine ⟨194625106493538705941134961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 129750070995692470627423307 194625106493538705941134961)
                  ·
                    refine ⟨145968829870154029455851221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 194625106493538705941134961 145968829870154029455851221)
                    ·
                      refine ⟨3421144450081735065371513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 145968829870154029455851221 3421144450081735065371513)
                      ·
                        rfl

theorem cell23_6662655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 1, 1, 2, 7].length) (baseStart_6662655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6662655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6662655 prefixEnd_6662655 := by exact prefixLift 6662655
  have htrace : WordTrace (prefixWord ++ tailWord_6662655) baseStart_6662655 baseEnd_6662655 := by
    simpa [prefixWord, tailWord_6662655, baseEnd_6662655] using wordTrace_append hprefix tailTrace_6662655
  have hstable : (prefixWord ++ tailWord_6662655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6662655).length < 2 ^ (prefixWord ++ tailWord_6662655).sum := by decide
  have hdescent : baseEnd_6662655 < baseStart_6662655 := by decide
  rcases family_descends (prefixWord ++ tailWord_6662655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6662665 : List Nat := [1, 2, 1, 1, 3, 1, 2, 1, 2, 1, 8]
def baseStart_6662665 : Nat := 118140960795 + 6662665 * 2 ^ 59
def prefixEnd_6662665 : Nat := 4983230072969 + 3 ^ 40 * 6662665 * 2
def baseEnd_6662665 : Nat := 3421149584888280026246467

theorem tailTrace_6662665 : CollatzResearch.WordTrace tailWord_6662665 prefixEnd_6662665 3421149584888280026246467 := by
  unfold tailWord_6662665
  simp only [CollatzResearch.WordTrace]
  refine ⟨243007356407310072434853449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162004904271540048289902299 243007356407310072434853449)
  ·
    refine ⟨182255517305482554326140087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243007356407310072434853449 182255517305482554326140087)
    ·
      refine ⟨273383275958223831489210131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182255517305482554326140087 273383275958223831489210131)
      ·
        refine ⟨410074913937335747233815197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273383275958223831489210131 410074913937335747233815197)
        ·
          refine ⟨153778092726500905212680699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 410074913937335747233815197 153778092726500905212680699)
          ·
            refine ⟨230667139089751357819021049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153778092726500905212680699 230667139089751357819021049)
            ·
              refine ⟨173000354317313518364265787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 230667139089751357819021049 173000354317313518364265787)
              ·
                refine ⟨259500531475970277546398681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 173000354317313518364265787 259500531475970277546398681)
                ·
                  refine ⟨194625398606977708159799011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 259500531475970277546398681 194625398606977708159799011)
                  ·
                    refine ⟨291938097910466562239698517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 194625398606977708159799011 291938097910466562239698517)
                    ·
                      refine ⟨3421149584888280026246467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 291938097910466562239698517 3421149584888280026246467)
                      ·
                        rfl

theorem cell23_6662665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 1, 8].length) (baseStart_6662665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6662665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6662665 prefixEnd_6662665 := by exact prefixLift 6662665
  have htrace : WordTrace (prefixWord ++ tailWord_6662665) baseStart_6662665 baseEnd_6662665 := by
    simpa [prefixWord, tailWord_6662665, baseEnd_6662665] using wordTrace_append hprefix tailTrace_6662665
  have hstable : (prefixWord ++ tailWord_6662665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6662665).length < 2 ^ (prefixWord ++ tailWord_6662665).sum := by decide
  have hdescent : baseEnd_6662665 < baseStart_6662665 := by decide
  rcases family_descends (prefixWord ++ tailWord_6662665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6662773 : List Nat := [1, 3, 4, 2, 2, 1, 2, 1, 3, 4]
def baseStart_6662773 : Nat := 118140960795 + 6662773 * 2 ^ 59
def prefixEnd_6662773 : Nat := 4983230072969 + 3 ^ 40 * 6662773 * 2
def baseEnd_6662773 : Nat := 1140401680266321867898657

theorem tailTrace_6662773 : CollatzResearch.WordTrace tailWord_6662773 prefixEnd_6662773 1140401680266321867898657 := by
  unfold tailWord_6662773
  simp only [CollatzResearch.WordTrace]
  refine ⟨243011295490918806879784973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162007530327279204586523315 243011295490918806879784973)
  ·
    refine ⟨91129235809094552579919365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 243011295490918806879784973 91129235809094552579919365)
    ·
      refine ⟨17086731714205228608734881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91129235809094552579919365 17086731714205228608734881)
      ·
        refine ⟨12815048785653921456551161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17086731714205228608734881 12815048785653921456551161)
        ·
          refine ⟨9611286589240441092413371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12815048785653921456551161 9611286589240441092413371)
          ·
            refine ⟨14416929883860661638620057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9611286589240441092413371 14416929883860661638620057)
            ·
              refine ⟨10812697412895496228965043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14416929883860661638620057 10812697412895496228965043)
              ·
                refine ⟨16219046119343244343447565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10812697412895496228965043 16219046119343244343447565)
                ·
                  refine ⟨6082142294753716628792837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16219046119343244343447565 6082142294753716628792837)
                  ·
                    refine ⟨1140401680266321867898657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6082142294753716628792837 1140401680266321867898657)
                    ·
                      rfl

theorem cell23_6662773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 2, 1, 3, 4].length) (baseStart_6662773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6662773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6662773 prefixEnd_6662773 := by exact prefixLift 6662773
  have htrace : WordTrace (prefixWord ++ tailWord_6662773) baseStart_6662773 baseEnd_6662773 := by
    simpa [prefixWord, tailWord_6662773, baseEnd_6662773] using wordTrace_append hprefix tailTrace_6662773
  have hstable : (prefixWord ++ tailWord_6662773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6662773).length < 2 ^ (prefixWord ++ tailWord_6662773).sum := by decide
  have hdescent : baseEnd_6662773 < baseStart_6662773 := by decide
  rcases family_descends (prefixWord ++ tailWord_6662773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6662830 : List Nat := [4, 1, 4, 1, 1, 1, 3, 1, 3, 1, 3]
def baseStart_6662830 : Nat := 118140960795 + 6662830 * 2 ^ 59
def prefixEnd_6662830 : Nat := 4983230072969 + 3 ^ 40 * 6662830 * 2
def baseEnd_6662830 : Nat := 3421234309196271880683209

theorem tailTrace_6662830 : CollatzResearch.WordTrace tailWord_6662830 prefixEnd_6662830 3421234309196271880683209 := by
  unfold tailWord_6662830
  simp only [CollatzResearch.WordTrace]
  refine ⟨30376671806464038201826243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 162008916301141537076406629 30376671806464038201826243)
  ·
    refine ⟨45565007709696057302739365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30376671806464038201826243 45565007709696057302739365)
    ·
      refine ⟨8543438945568010744263631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45565007709696057302739365 8543438945568010744263631)
      ·
        refine ⟨12815158418352016116395447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8543438945568010744263631 12815158418352016116395447)
        ·
          refine ⟨19222737627528024174593171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12815158418352016116395447 19222737627528024174593171)
          ·
            refine ⟨28834106441292036261889757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19222737627528024174593171 28834106441292036261889757)
            ·
              refine ⟨10812789915484513598208659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28834106441292036261889757 10812789915484513598208659)
              ·
                refine ⟨16219184873226770397312989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10812789915484513598208659 16219184873226770397312989)
                ·
                  refine ⟨6082194327460038898992371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16219184873226770397312989 6082194327460038898992371)
                  ·
                    refine ⟨9123291491190058348488557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6082194327460038898992371 9123291491190058348488557)
                    ·
                      refine ⟨3421234309196271880683209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9123291491190058348488557 3421234309196271880683209)
                      ·
                        rfl

theorem cell23_6662830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_6662830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6662830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6662830 prefixEnd_6662830 := by exact prefixLift 6662830
  have htrace : WordTrace (prefixWord ++ tailWord_6662830) baseStart_6662830 baseEnd_6662830 := by
    simpa [prefixWord, tailWord_6662830, baseEnd_6662830] using wordTrace_append hprefix tailTrace_6662830
  have hstable : (prefixWord ++ tailWord_6662830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6662830).length < 2 ^ (prefixWord ++ tailWord_6662830).sum := by decide
  have hdescent : baseEnd_6662830 < baseStart_6662830 := by decide
  rcases family_descends (prefixWord ++ tailWord_6662830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6662856 : List Nat := [2, 1, 3, 1, 2, 4, 1, 1, 3, 2, 3]
def baseStart_6662856 : Nat := 118140960795 + 6662856 * 2 ^ 59
def prefixEnd_6662856 : Nat := 4983230072969 + 3 ^ 40 * 6662856 * 2
def baseEnd_6662856 : Nat := 3421247659693288778958089

theorem tailTrace_6662856 : CollatzResearch.WordTrace tailWord_6662856 prefixEnd_6662856 3421247659693288778958089 := by
  unfold tailWord_6662856
  simp only [CollatzResearch.WordTrace]
  refine ⟨121507161374809056027528211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162009548499745408036704281 121507161374809056027528211)
  ·
    refine ⟨182260742062213584041292317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121507161374809056027528211 182260742062213584041292317)
    ·
      refine ⟨68347778273330094015484619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182260742062213584041292317 68347778273330094015484619)
      ·
        refine ⟨102521667409995141023226929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68347778273330094015484619 102521667409995141023226929)
        ·
          refine ⟨76891250557496355767420197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102521667409995141023226929 76891250557496355767420197)
          ·
            refine ⟨14417109479530566706391287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76891250557496355767420197 14417109479530566706391287)
            ·
              refine ⟨21625664219295850059586931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14417109479530566706391287 21625664219295850059586931)
              ·
                refine ⟨32438496328943775089380397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21625664219295850059586931 32438496328943775089380397)
                ·
                  refine ⟨12164436123353915658517649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32438496328943775089380397 12164436123353915658517649)
                  ·
                    refine ⟨9123327092515436743888237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12164436123353915658517649 9123327092515436743888237)
                    ·
                      refine ⟨3421247659693288778958089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9123327092515436743888237 3421247659693288778958089)
                      ·
                        rfl

theorem cell23_6662856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 1, 3, 2, 3].length) (baseStart_6662856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6662856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6662856 prefixEnd_6662856 := by exact prefixLift 6662856
  have htrace : WordTrace (prefixWord ++ tailWord_6662856) baseStart_6662856 baseEnd_6662856 := by
    simpa [prefixWord, tailWord_6662856, baseEnd_6662856] using wordTrace_append hprefix tailTrace_6662856
  have hstable : (prefixWord ++ tailWord_6662856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6662856).length < 2 ^ (prefixWord ++ tailWord_6662856).sum := by decide
  have hdescent : baseEnd_6662856 < baseStart_6662856 := by decide
  rcases family_descends (prefixWord ++ tailWord_6662856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6662873 : List Nat := [1, 2, 1, 2, 3, 2, 5, 1, 1, 2, 3]
def baseStart_6662873 : Nat := 118140960795 + 6662873 * 2 ^ 59
def prefixEnd_6662873 : Nat := 4983230072969 + 3 ^ 40 * 6662873 * 2
def baseEnd_6662873 : Nat := 3421256388864415212445511

theorem tailTrace_6662873 : CollatzResearch.WordTrace tailWord_6662873 prefixEnd_6662873 3421256388864415212445511 := by
  unfold tailWord_6662873
  simp only [CollatzResearch.WordTrace]
  refine ⟨243014942790556523958425273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162009961860371015972283515 243014942790556523958425273)
  ·
    refine ⟨182261207092917392968818955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243014942790556523958425273 182261207092917392968818955)
    ·
      refine ⟨273391810639376089453228433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182261207092917392968818955 273391810639376089453228433)
      ·
        refine ⟨205043857979532067089921325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 273391810639376089453228433 205043857979532067089921325)
        ·
          refine ⟨76891446742324525158720497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 205043857979532067089921325 76891446742324525158720497)
          ·
            refine ⟨57668585056743393869040373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76891446742324525158720497 57668585056743393869040373)
            ·
              refine ⟨5406429849069693175222535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57668585056743393869040373 5406429849069693175222535)
              ·
                refine ⟨8109644773604539762833803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5406429849069693175222535 8109644773604539762833803)
                ·
                  refine ⟨12164467160406809644250705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8109644773604539762833803 12164467160406809644250705)
                  ·
                    refine ⟨9123350370305107233188029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12164467160406809644250705 9123350370305107233188029)
                    ·
                      refine ⟨3421256388864415212445511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9123350370305107233188029 3421256388864415212445511)
                      ·
                        rfl

theorem cell23_6662873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 5, 1, 1, 2, 3].length) (baseStart_6662873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6662873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6662873 prefixEnd_6662873 := by exact prefixLift 6662873
  have htrace : WordTrace (prefixWord ++ tailWord_6662873) baseStart_6662873 baseEnd_6662873 := by
    simpa [prefixWord, tailWord_6662873, baseEnd_6662873] using wordTrace_append hprefix tailTrace_6662873
  have hstable : (prefixWord ++ tailWord_6662873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6662873).length < 2 ^ (prefixWord ++ tailWord_6662873).sum := by decide
  have hdescent : baseEnd_6662873 < baseStart_6662873 := by decide
  rcases family_descends (prefixWord ++ tailWord_6662873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6662896 : List Nat := [2, 1, 1, 1, 3, 1, 3, 1, 5, 3, 2]
def baseStart_6662896 : Nat := 118140960795 + 6662896 * 2 ^ 59
def prefixEnd_6662896 : Nat := 4983230072969 + 3 ^ 40 * 6662896 * 2
def baseEnd_6662896 : Nat := 3421268198919468622457905

theorem tailTrace_6662896 : CollatzResearch.WordTrace tailWord_6662896 prefixEnd_6662896 3421268198919468622457905 := by
  unfold tailWord_6662896
  simp only [CollatzResearch.WordTrace]
  refine ⟨121507890834736599443256271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162010521112982132591008361 121507890834736599443256271)
  ·
    refine ⟨182261836252104899164884407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 121507890834736599443256271 182261836252104899164884407)
    ·
      refine ⟨273392754378157348747326611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182261836252104899164884407 273392754378157348747326611)
      ·
        refine ⟨410089131567236023120989917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 273392754378157348747326611 410089131567236023120989917)
        ·
          refine ⟨153783424337713508670371219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 410089131567236023120989917 153783424337713508670371219)
          ·
            refine ⟨230675136506570263005556829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153783424337713508670371219 230675136506570263005556829)
            ·
              refine ⟨86503176189963848627083811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 230675136506570263005556829 86503176189963848627083811)
              ·
                refine ⟨129754764284945772940625717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86503176189963848627083811 129754764284945772940625717)
                ·
                  refine ⟨12164509151713666213183661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 129754764284945772940625717 12164509151713666213183661)
                  ·
                    refine ⟨4561690931892624829943873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12164509151713666213183661 4561690931892624829943873)
                    ·
                      refine ⟨3421268198919468622457905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4561690931892624829943873 3421268198919468622457905)
                      ·
                        rfl

theorem cell23_6662896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 5, 3, 2].length) (baseStart_6662896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6662896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6662896 prefixEnd_6662896 := by exact prefixLift 6662896
  have htrace : WordTrace (prefixWord ++ tailWord_6662896) baseStart_6662896 baseEnd_6662896 := by
    simpa [prefixWord, tailWord_6662896, baseEnd_6662896] using wordTrace_append hprefix tailTrace_6662896
  have hstable : (prefixWord ++ tailWord_6662896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6662896).length < 2 ^ (prefixWord ++ tailWord_6662896).sum := by decide
  have hdescent : baseEnd_6662896 < baseStart_6662896 := by decide
  rcases family_descends (prefixWord ++ tailWord_6662896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6662909 : List Nat := [1, 4, 1, 1, 1, 1, 3, 2, 2, 3, 4]
def baseStart_6662909 : Nat := 118140960795 + 6662909 * 2 ^ 59
def prefixEnd_6662909 : Nat := 4983230072969 + 3 ^ 40 * 6662909 * 2
def baseEnd_6662909 : Nat := 3421274874167977071595345

theorem tailTrace_6662909 : CollatzResearch.WordTrace tailWord_6662909 prefixEnd_6662909 3421274874167977071595345 := by
  unfold tailWord_6662909
  simp only [CollatzResearch.WordTrace]
  refine ⟨243016255818426102106735781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162010837212284068071157187 243016255818426102106735781)
  ·
    refine ⟨45565547965954894145012959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 243016255818426102106735781 45565547965954894145012959)
    ·
      refine ⟨68348321948932341217519439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45565547965954894145012959 68348321948932341217519439)
      ·
        refine ⟨102522482923398511826279159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68348321948932341217519439 102522482923398511826279159)
        ·
          refine ⟨153783724385097767739418739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102522482923398511826279159 153783724385097767739418739)
          ·
            refine ⟨230675586577646651609128109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153783724385097767739418739 230675586577646651609128109)
            ·
              refine ⟨86503344966617494353423041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 230675586577646651609128109 86503344966617494353423041)
              ·
                refine ⟨64877508724963120765067281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86503344966617494353423041 64877508724963120765067281)
                ·
                  refine ⟨48658131543722340573800461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64877508724963120765067281 48658131543722340573800461)
                  ·
                    refine ⟨18246799328895877715175173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48658131543722340573800461 18246799328895877715175173)
                    ·
                      refine ⟨3421274874167977071595345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18246799328895877715175173 3421274874167977071595345)
                      ·
                        rfl

theorem cell23_6662909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 2, 2, 3, 4].length) (baseStart_6662909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6662909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6662909 prefixEnd_6662909 := by exact prefixLift 6662909
  have htrace : WordTrace (prefixWord ++ tailWord_6662909) baseStart_6662909 baseEnd_6662909 := by
    simpa [prefixWord, tailWord_6662909, baseEnd_6662909] using wordTrace_append hprefix tailTrace_6662909
  have hstable : (prefixWord ++ tailWord_6662909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6662909).length < 2 ^ (prefixWord ++ tailWord_6662909).sum := by decide
  have hdescent : baseEnd_6662909 < baseStart_6662909 := by decide
  rcases family_descends (prefixWord ++ tailWord_6662909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6662913 : List Nat := [1, 2, 4, 1, 1, 1, 1, 6, 1, 3, 2]
def baseStart_6662913 : Nat := 118140960795 + 6662913 * 2 ^ 59
def prefixEnd_6662913 : Nat := 4983230072969 + 3 ^ 40 * 6662913 * 2
def baseEnd_6662913 : Nat := 3421276928090595055945327

theorem tailTrace_6662913 : CollatzResearch.WordTrace tailWord_6662913 prefixEnd_6662913 3421276928090595055945327 := by
  unfold tailWord_6662913
  simp only [CollatzResearch.WordTrace]
  refine ⟨243016401710411610789881393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162010934473607740526587595 243016401710411610789881393)
  ·
    refine ⟨182262301282808708092411045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243016401710411610789881393 182262301282808708092411045)
    ·
      refine ⟨34174181490526632767327071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 182262301282808708092411045 34174181490526632767327071)
      ·
        refine ⟨51261272235789949150990607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34174181490526632767327071 51261272235789949150990607)
        ·
          refine ⟨76891908353684923726485911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51261272235789949150990607 76891908353684923726485911)
          ·
            refine ⟨115337862530527385589728867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76891908353684923726485911 115337862530527385589728867)
            ·
              refine ⟨173006793795791078384593301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115337862530527385589728867 173006793795791078384593301)
              ·
                refine ⟨8109693459177706799277811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 173006793795791078384593301 8109693459177706799277811)
                ·
                  refine ⟨12164540188766560198916717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8109693459177706799277811 12164540188766560198916717)
                  ·
                    refine ⟨4561702570787460074593769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12164540188766560198916717 4561702570787460074593769)
                    ·
                      refine ⟨3421276928090595055945327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4561702570787460074593769 3421276928090595055945327)
                      ·
                        rfl

theorem cell23_6662913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 6, 1, 3, 2].length) (baseStart_6662913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6662913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6662913 prefixEnd_6662913 := by exact prefixLift 6662913
  have htrace : WordTrace (prefixWord ++ tailWord_6662913) baseStart_6662913 baseEnd_6662913 := by
    simpa [prefixWord, tailWord_6662913, baseEnd_6662913] using wordTrace_append hprefix tailTrace_6662913
  have hstable : (prefixWord ++ tailWord_6662913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6662913).length < 2 ^ (prefixWord ++ tailWord_6662913).sum := by decide
  have hdescent : baseEnd_6662913 < baseStart_6662913 := by decide
  rcases family_descends (prefixWord ++ tailWord_6662913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6662929 : List Nat := [1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 5]
def baseStart_6662929 : Nat := 118140960795 + 6662929 * 2 ^ 59
def prefixEnd_6662929 : Nat := 4983230072969 + 3 ^ 40 * 6662929 * 2
def baseEnd_6662929 : Nat := 3421285143781066993345253

theorem tailTrace_6662929 : CollatzResearch.WordTrace tailWord_6662929 prefixEnd_6662929 3421285143781066993345253 := by
  unfold tailWord_6662929
  simp only [CollatzResearch.WordTrace]
  refine ⟨243016985278353645522463841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162011323518902430348309227 243016985278353645522463841)
  ·
    refine ⟨182262738958765234141847881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243016985278353645522463841 182262738958765234141847881)
    ·
      refine ⟨136697054219073925606385911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 182262738958765234141847881 136697054219073925606385911)
      ·
        refine ⟨205045581328610888409578867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136697054219073925606385911 205045581328610888409578867)
        ·
          refine ⟨307568371992916332614368301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205045581328610888409578867 307568371992916332614368301)
          ·
            refine ⟨115338139497343624730388113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 307568371992916332614368301 115338139497343624730388113)
            ·
              refine ⟨86503604623007718547791085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115338139497343624730388113 86503604623007718547791085)
              ·
                refine ⟨32438851733627894455421657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86503604623007718547791085 32438851733627894455421657)
                ·
                  refine ⟨24329138800220920841566243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32438851733627894455421657 24329138800220920841566243)
                  ·
                    refine ⟨36493708200331381262349365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24329138800220920841566243 36493708200331381262349365)
                    ·
                      refine ⟨3421285143781066993345253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36493708200331381262349365 3421285143781066993345253)
                      ·
                        rfl

theorem cell23_6662929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 5].length) (baseStart_6662929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6662929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6662929 prefixEnd_6662929 := by exact prefixLift 6662929
  have htrace : WordTrace (prefixWord ++ tailWord_6662929) baseStart_6662929 baseEnd_6662929 := by
    simpa [prefixWord, tailWord_6662929, baseEnd_6662929] using wordTrace_append hprefix tailTrace_6662929
  have hstable : (prefixWord ++ tailWord_6662929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6662929).length < 2 ^ (prefixWord ++ tailWord_6662929).sum := by decide
  have hdescent : baseEnd_6662929 < baseStart_6662929 := by decide
  rcases family_descends (prefixWord ++ tailWord_6662929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6662954 : List Nat := [3, 1, 4, 3, 1, 1, 3, 1, 2, 1, 3]
def baseStart_6662954 : Nat := 118140960795 + 6662954 * 2 ^ 59
def prefixEnd_6662954 : Nat := 4983230072969 + 3 ^ 40 * 6662954 * 2
def baseEnd_6662954 : Nat := 3421297980797429395532639

theorem tailTrace_6662954 : CollatzResearch.WordTrace tailWord_6662954 prefixEnd_6662954 3421297980797429395532639 := by
  unfold tailWord_6662954
  simp only [CollatzResearch.WordTrace]
  refine ⟨60754474275815768698030979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 162011931402175383194749277 60754474275815768698030979)
  ·
    refine ⟨91131711413723653047046469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60754474275815768698030979 91131711413723653047046469)
    ·
      refine ⟨17087195890073184946321213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91131711413723653047046469 17087195890073184946321213)
      ·
        refine ⟨6407698458777444354870455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17087195890073184946321213 6407698458777444354870455)
        ·
          refine ⟨9611547688166166532305683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6407698458777444354870455 9611547688166166532305683)
          ·
            refine ⟨14417321532249249798458525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9611547688166166532305683 14417321532249249798458525)
            ·
              refine ⟨5406495574593468674421947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14417321532249249798458525 5406495574593468674421947)
              ·
                refine ⟨8109743361890203011632921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5406495574593468674421947 8109743361890203011632921)
                ·
                  refine ⟨6082307521417652258724691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8109743361890203011632921 6082307521417652258724691)
                  ·
                    refine ⟨9123461282126478388087037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6082307521417652258724691 9123461282126478388087037)
                    ·
                      refine ⟨3421297980797429395532639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9123461282126478388087037 3421297980797429395532639)
                      ·
                        rfl

theorem cell23_6662954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_6662954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6662954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6662954 prefixEnd_6662954 := by exact prefixLift 6662954
  have htrace : WordTrace (prefixWord ++ tailWord_6662954) baseStart_6662954 baseEnd_6662954 := by
    simpa [prefixWord, tailWord_6662954, baseEnd_6662954] using wordTrace_append hprefix tailTrace_6662954
  have hstable : (prefixWord ++ tailWord_6662954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6662954).length < 2 ^ (prefixWord ++ tailWord_6662954).sum := by decide
  have hdescent : baseEnd_6662954 < baseStart_6662954 := by decide
  rcases family_descends (prefixWord ++ tailWord_6662954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6662979 : List Nat := [1, 1, 1, 3, 1, 4, 1, 3, 1, 7]
def baseStart_6662979 : Nat := 118140960795 + 6662979 * 2 ^ 59
def prefixEnd_6662979 : Nat := 4983230072969 + 3 ^ 40 * 6662979 * 2
def baseEnd_6662979 : Nat := 1140436939271263932573341

theorem tailTrace_6662979 : CollatzResearch.WordTrace tailWord_6662979 prefixEnd_6662979 1140436939271263932573341 := by
  unfold tailWord_6662979
  simp only [CollatzResearch.WordTrace]
  refine ⟨243018808928172504061783991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162012539285448336041189327 243018808928172504061783991)
  ·
    refine ⟨364528213392258756092675987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243018808928172504061783991 364528213392258756092675987)
    ·
      refine ⟨546792320088388134139013981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 364528213392258756092675987 546792320088388134139013981)
      ·
        refine ⟨205047120033145550302130243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 546792320088388134139013981 205047120033145550302130243)
        ·
          refine ⟨307570680049718325453195365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205047120033145550302130243 307570680049718325453195365)
          ·
            refine ⟨57669502509322186022474131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 307570680049718325453195365 57669502509322186022474131)
            ·
              refine ⟨86504253763983279033711197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57669502509322186022474131 86504253763983279033711197)
              ·
                refine ⟨32439095161493729637641699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86504253763983279033711197 32439095161493729637641699)
                ·
                  refine ⟨48658642742240594456462549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32439095161493729637641699 48658642742240594456462549)
                  ·
                    refine ⟨1140436939271263932573341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48658642742240594456462549 1140436939271263932573341)
                    ·
                      rfl

theorem cell23_6662979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 3, 1, 7].length) (baseStart_6662979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6662979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6662979 prefixEnd_6662979 := by exact prefixLift 6662979
  have htrace : WordTrace (prefixWord ++ tailWord_6662979) baseStart_6662979 baseEnd_6662979 := by
    simpa [prefixWord, tailWord_6662979, baseEnd_6662979] using wordTrace_append hprefix tailTrace_6662979
  have hstable : (prefixWord ++ tailWord_6662979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6662979).length < 2 ^ (prefixWord ++ tailWord_6662979).sum := by decide
  have hdescent : baseEnd_6662979 < baseStart_6662979 := by decide
  rcases family_descends (prefixWord ++ tailWord_6662979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6662980 : List Nat := [2, 3, 4, 2, 1, 1, 1, 1, 2, 1, 5]
def baseStart_6662980 : Nat := 118140960795 + 6662980 * 2 ^ 59
def prefixEnd_6662980 : Nat := 4983230072969 + 3 ^ 40 * 6662980 * 2
def baseEnd_6662980 : Nat := 3421311331294446293807519

theorem tailTrace_6662980 : CollatzResearch.WordTrace tailWord_6662980 prefixEnd_6662980 3421311331294446293807519 := by
  unfold tailWord_6662980
  simp only [CollatzResearch.WordTrace]
  refine ⟨121509422700584440616285197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 162012563600779254155046929 121509422700584440616285197)
  ·
    refine ⟨45566033512719165231106949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 121509422700584440616285197 45566033512719165231106949)
    ·
      refine ⟨8543631283634843480832553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45566033512719165231106949 8543631283634843480832553)
      ·
        refine ⟨6407723462726132610624415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8543631283634843480832553 6407723462726132610624415)
        ·
          refine ⟨9611585194089198915936623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6407723462726132610624415 9611585194089198915936623)
          ·
            refine ⟨14417377791133798373904935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9611585194089198915936623 14417377791133798373904935)
            ·
              refine ⟨21626066686700697560857403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14417377791133798373904935 21626066686700697560857403)
              ·
                refine ⟨32439100030051046341286105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21626066686700697560857403 32439100030051046341286105)
                ·
                  refine ⟨24329325022538284755964579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32439100030051046341286105 24329325022538284755964579)
                  ·
                    refine ⟨36493987533807427133946869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24329325022538284755964579 36493987533807427133946869)
                    ·
                      refine ⟨3421311331294446293807519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36493987533807427133946869 3421311331294446293807519)
                      ·
                        rfl

theorem cell23_6662980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_6662980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6662980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6662980 prefixEnd_6662980 := by exact prefixLift 6662980
  have htrace : WordTrace (prefixWord ++ tailWord_6662980) baseStart_6662980 baseEnd_6662980 := by
    simpa [prefixWord, tailWord_6662980, baseEnd_6662980] using wordTrace_append hprefix tailTrace_6662980
  have hstable : (prefixWord ++ tailWord_6662980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6662980).length < 2 ^ (prefixWord ++ tailWord_6662980).sum := by decide
  have hdescent : baseEnd_6662980 < baseStart_6662980 := by decide
  rcases family_descends (prefixWord ++ tailWord_6662980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6663009 : List Nat := [1, 2, 3, 1, 1, 1, 2, 2, 2, 8]
def baseStart_6663009 : Nat := 118140960795 + 6663009 * 2 ^ 59
def prefixEnd_6663009 : Nat := 4983230072969 + 3 ^ 40 * 6663009 * 2
def baseEnd_6663009 : Nat := 1140442074077808893448295

theorem tailTrace_6663009 : CollatzResearch.WordTrace tailWord_6663009 prefixEnd_6663009 1140442074077808893448295 := by
  unfold tailWord_6663009
  simp only [CollatzResearch.WordTrace]
  refine ⟨243019903118063819185376081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 162013268745375879456917387 243019903118063819185376081)
  ·
    refine ⟨182264927338547864389032061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 243019903118063819185376081 182264927338547864389032061)
    ·
      refine ⟨68349347751955449145887023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 182264927338547864389032061 68349347751955449145887023)
      ·
        refine ⟨102524021627933173718830535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68349347751955449145887023 102524021627933173718830535)
        ·
          refine ⟨153786032441899760578245803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102524021627933173718830535 153786032441899760578245803)
          ·
            refine ⟨230679048662849640867368705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153786032441899760578245803 230679048662849640867368705)
            ·
              refine ⟨173009286497137230650526529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 230679048662849640867368705 173009286497137230650526529)
              ·
                refine ⟨129756964872852922987894897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 173009286497137230650526529 129756964872852922987894897)
                ·
                  refine ⟨97317723654639692240921173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 129756964872852922987894897 97317723654639692240921173)
                  ·
                    refine ⟨1140442074077808893448295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 97317723654639692240921173 1140442074077808893448295)
                    ·
                      rfl

theorem cell23_6663009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 2, 2, 8].length) (baseStart_6663009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6663009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6663009 prefixEnd_6663009 := by exact prefixLift 6663009
  have htrace : WordTrace (prefixWord ++ tailWord_6663009) baseStart_6663009 baseEnd_6663009 := by
    simpa [prefixWord, tailWord_6663009, baseEnd_6663009] using wordTrace_append hprefix tailTrace_6663009
  have hstable : (prefixWord ++ tailWord_6663009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6663009).length < 2 ^ (prefixWord ++ tailWord_6663009).sum := by decide
  have hdescent : baseEnd_6663009 < baseStart_6663009 := by decide
  rcases family_descends (prefixWord ++ tailWord_6663009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
