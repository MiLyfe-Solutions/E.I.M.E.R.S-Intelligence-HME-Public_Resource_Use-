import V185TrunkScan23Chunk0031

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_189744 : List Nat := [2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 5]
def baseStart_189744 : Nat := 118140960795 + 189744 * 2 ^ 59
def prefixEnd_189744 : Nat := 4983230072969 + 3 ^ 40 * 189744 * 2
def baseEnd_189744 : Nat := 97429873306810859427389

theorem tailTrace_189744 : CollatzResearch.WordTrace tailWord_189744 prefixEnd_189744 97429873306810859427389 := by
  unfold tailWord_189744
  simp only [CollatzResearch.WordTrace]
  refine ⟨3460266112298684270180143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4613688149731579026906857 3460266112298684270180143)
  ·
    refine ⟨5190399168448026405270215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3460266112298684270180143 5190399168448026405270215)
    ·
      refine ⟨7785598752672039607905323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5190399168448026405270215 7785598752672039607905323)
      ·
        refine ⟨11678398129008059411857985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7785598752672039607905323 11678398129008059411857985)
        ·
          refine ⟨8758798596756044558893489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11678398129008059411857985 8758798596756044558893489)
          ·
            refine ⟨6569098947567033419170117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8758798596756044558893489 6569098947567033419170117)
            ·
              refine ⟨1231706052668818766094397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6569098947567033419170117 1231706052668818766094397)
              ·
                refine ⟨461889769750807037285399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1231706052668818766094397 461889769750807037285399)
                ·
                  refine ⟨692834654626210555928099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 461889769750807037285399 692834654626210555928099)
                  ·
                    refine ⟨1039251981939315833892149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 692834654626210555928099 1039251981939315833892149)
                    ·
                      refine ⟨97429873306810859427389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1039251981939315833892149 97429873306810859427389)
                      ·
                        rfl

theorem cell23_189744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 5].length) (baseStart_189744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_189744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_189744 prefixEnd_189744 := by exact prefixLift 189744
  have htrace : WordTrace (prefixWord ++ tailWord_189744) baseStart_189744 baseEnd_189744 := by
    simpa [prefixWord, tailWord_189744, baseEnd_189744] using wordTrace_append hprefix tailTrace_189744
  have hstable : (prefixWord ++ tailWord_189744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189744).length < 2 ^ (prefixWord ++ tailWord_189744).sum := by decide
  have hdescent : baseEnd_189744 < baseStart_189744 := by decide
  rcases family_descends (prefixWord ++ tailWord_189744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189754 : List Nat := [3, 1, 1, 1, 4, 1, 2, 2, 1, 1, 6]
def baseStart_189754 : Nat := 118140960795 + 189754 * 2 ^ 59
def prefixEnd_189754 : Nat := 4983230072969 + 3 ^ 40 * 189754 * 2
def baseEnd_189754 : Nat := 97435008113355820302343

theorem tailTrace_189754 : CollatzResearch.WordTrace tailWord_189754 prefixEnd_189754 97435008113355820302343 := by
  unfold tailWord_189754
  simp only [CollatzResearch.WordTrace]
  refine ⟨1730224238640285062056079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4613931303040760165482877 1730224238640285062056079)
  ·
    refine ⟨2595336357960427593084119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1730224238640285062056079 2595336357960427593084119)
    ·
      refine ⟨3893004536940641389626179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2595336357960427593084119 3893004536940641389626179)
      ·
        refine ⟨5839506805410962084439269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3893004536940641389626179 5839506805410962084439269)
        ·
          refine ⟨1094907526014555390832363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5839506805410962084439269 1094907526014555390832363)
          ·
            refine ⟨1642361289021833086248545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1094907526014555390832363 1642361289021833086248545)
            ·
              refine ⟨1231770966766374814686409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1642361289021833086248545 1231770966766374814686409)
              ·
                refine ⟨923828225074781111014807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1231770966766374814686409 923828225074781111014807)
                ·
                  refine ⟨1385742337612171666522211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 923828225074781111014807 1385742337612171666522211)
                  ·
                    refine ⟨2078613506418257499783317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1385742337612171666522211 2078613506418257499783317)
                    ·
                      refine ⟨97435008113355820302343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2078613506418257499783317 97435008113355820302343)
                      ·
                        rfl

theorem cell23_189754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 2, 1, 1, 6].length) (baseStart_189754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_189754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_189754 prefixEnd_189754 := by exact prefixLift 189754
  have htrace : WordTrace (prefixWord ++ tailWord_189754) baseStart_189754 baseEnd_189754 := by
    simpa [prefixWord, tailWord_189754, baseEnd_189754] using wordTrace_append hprefix tailTrace_189754
  have hstable : (prefixWord ++ tailWord_189754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189754).length < 2 ^ (prefixWord ++ tailWord_189754).sum := by decide
  have hdescent : baseEnd_189754 < baseStart_189754 := by decide
  rcases family_descends (prefixWord ++ tailWord_189754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189761 : List Nat := [1, 2, 5, 2, 1, 1, 1, 1, 3, 1, 5]
def baseStart_189761 : Nat := 118140960795 + 189761 * 2 ^ 59
def prefixEnd_189761 : Nat := 4983230072969 + 3 ^ 40 * 189761 * 2
def baseEnd_189761 : Nat := 97438602477937292914811

theorem tailTrace_189761 : CollatzResearch.WordTrace tailWord_189761 prefixEnd_189761 97438602477937292914811 := by
  unfold tailWord_189761
  simp only [CollatzResearch.WordTrace]
  refine ⟨6921152265535780443729137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4614101510357186962486091 6921152265535780443729137)
  ·
    refine ⟨5190864199151835332796853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6921152265535780443729137 5190864199151835332796853)
    ·
      refine ⟨486643518670484562449705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5190864199151835332796853 486643518670484562449705)
      ·
        refine ⟨364982639002863421837279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 486643518670484562449705 364982639002863421837279)
        ·
          refine ⟨547473958504295132755919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 364982639002863421837279 547473958504295132755919)
          ·
            refine ⟨821210937756442699133879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 547473958504295132755919 821210937756442699133879)
            ·
              refine ⟨1231816406634664048700819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 821210937756442699133879 1231816406634664048700819)
              ·
                refine ⟨1847724609951996073051229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1231816406634664048700819 1847724609951996073051229)
                ·
                  refine ⟨692896728731998527394211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1847724609951996073051229 692896728731998527394211)
                  ·
                    refine ⟨1039345093097997791091317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 692896728731998527394211 1039345093097997791091317)
                    ·
                      refine ⟨97438602477937292914811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1039345093097997791091317 97438602477937292914811)
                      ·
                        rfl

theorem cell23_189761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_189761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_189761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_189761 prefixEnd_189761 := by exact prefixLift 189761
  have htrace : WordTrace (prefixWord ++ tailWord_189761) baseStart_189761 baseEnd_189761 := by
    simpa [prefixWord, tailWord_189761, baseEnd_189761] using wordTrace_append hprefix tailTrace_189761
  have hstable : (prefixWord ++ tailWord_189761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189761).length < 2 ^ (prefixWord ++ tailWord_189761).sum := by decide
  have hdescent : baseEnd_189761 < baseStart_189761 := by decide
  rcases family_descends (prefixWord ++ tailWord_189761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189781 : List Nat := [1, 3, 2, 2, 3, 1, 4, 7]
def baseStart_189781 : Nat := 118140960795 + 189781 * 2 ^ 59
def prefixEnd_189781 : Nat := 4983230072969 + 3 ^ 40 * 189781 * 2
def baseEnd_189781 : Nat := 3609217484852859802397

theorem tailTrace_189781 : CollatzResearch.WordTrace tailWord_189781 prefixEnd_189781 3609217484852859802397 := by
  unfold tailWord_189781
  simp only [CollatzResearch.WordTrace]
  refine ⟨6921881725463323859457197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4614587816975549239638131 6921881725463323859457197)
  ·
    refine ⟨2595705647048746447296449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6921881725463323859457197 2595705647048746447296449)
    ·
      refine ⟨1946779235286559835472337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2595705647048746447296449 1946779235286559835472337)
      ·
        refine ⟨1460084426464919876604253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1946779235286559835472337 1460084426464919876604253)
        ·
          refine ⟨547531659924344953726595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1460084426464919876604253 547531659924344953726595)
          ·
            refine ⟨821297489886517430589893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 547531659924344953726595 821297489886517430589893)
            ·
              refine ⟨153993279353722018235605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 821297489886517430589893 153993279353722018235605)
              ·
                refine ⟨3609217484852859802397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 153993279353722018235605 3609217484852859802397)
                ·
                  rfl

theorem cell23_189781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 4, 7].length) (baseStart_189781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_189781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_189781 prefixEnd_189781 := by exact prefixLift 189781
  have htrace : WordTrace (prefixWord ++ tailWord_189781) baseStart_189781 baseEnd_189781 := by
    simpa [prefixWord, tailWord_189781, baseEnd_189781] using wordTrace_append hprefix tailTrace_189781
  have hstable : (prefixWord ++ tailWord_189781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189781).length < 2 ^ (prefixWord ++ tailWord_189781).sum := by decide
  have hdescent : baseEnd_189781 < baseStart_189781 := by decide
  rcases family_descends (prefixWord ++ tailWord_189781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189792 : List Nat := [2, 1, 1, 3, 4, 1, 3, 3, 1, 2, 2]
def baseStart_189792 : Nat := 118140960795 + 189792 * 2 ^ 59
def prefixEnd_189792 : Nat := 4983230072969 + 3 ^ 40 * 189792 * 2
def baseEnd_189792 : Nat := 97454520378226671627169

theorem tailTrace_189792 : CollatzResearch.WordTrace tailWord_189792 prefixEnd_189792 97454520378226671627169 := by
  unfold tailWord_189792
  simp only [CollatzResearch.WordTrace]
  refine ⟨3461141464211736369053815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4614855285615648492071753 3461141464211736369053815)
  ·
    refine ⟨5191712196317604553580723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3461141464211736369053815 5191712196317604553580723)
    ·
      refine ⟨7787568294476406830371085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5191712196317604553580723 7787568294476406830371085)
      ·
        refine ⟨2920338110428652561389157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7787568294476406830371085 2920338110428652561389157)
        ·
          refine ⟨547563395705372355260467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2920338110428652561389157 547563395705372355260467)
          ·
            refine ⟨821345093558058532890701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 547563395705372355260467 821345093558058532890701)
            ·
              refine ⟨308004410084271949834013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 821345093558058532890701 308004410084271949834013)
              ·
                refine ⟨115501653781601981187755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 308004410084271949834013 115501653781601981187755)
                ·
                  refine ⟨173252480672402971781633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 115501653781601981187755 173252480672402971781633)
                  ·
                    refine ⟨129939360504302228836225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 173252480672402971781633 129939360504302228836225)
                    ·
                      refine ⟨97454520378226671627169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 129939360504302228836225 97454520378226671627169)
                      ·
                        rfl

theorem cell23_189792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 3, 3, 1, 2, 2].length) (baseStart_189792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_189792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_189792 prefixEnd_189792 := by exact prefixLift 189792
  have htrace : WordTrace (prefixWord ++ tailWord_189792) baseStart_189792 baseEnd_189792 := by
    simpa [prefixWord, tailWord_189792, baseEnd_189792] using wordTrace_append hprefix tailTrace_189792
  have hstable : (prefixWord ++ tailWord_189792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189792).length < 2 ^ (prefixWord ++ tailWord_189792).sum := by decide
  have hdescent : baseEnd_189792 < baseStart_189792 := by decide
  rcases family_descends (prefixWord ++ tailWord_189792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189808 : List Nat := [2, 1, 1, 1, 4, 2, 2, 4, 2, 1, 3]
def baseStart_189808 : Nat := 118140960795 + 189808 * 2 ^ 59
def prefixEnd_189808 : Nat := 4983230072969 + 3 ^ 40 * 189808 * 2
def baseEnd_189808 : Nat := 97462736068698609027095

theorem tailTrace_189808 : CollatzResearch.WordTrace tailWord_189808 prefixEnd_189808 97462736068698609027095 := by
  unfold tailWord_189808
  simp only [CollatzResearch.WordTrace]
  refine ⟨3461433248182753735345039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4615244330910338313793385 3461433248182753735345039)
  ·
    refine ⟨5192149872274130603017559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3461433248182753735345039 5192149872274130603017559)
    ·
      refine ⟨7788224808411195904526339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5192149872274130603017559 7788224808411195904526339)
      ·
        refine ⟨11682337212616793856789509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7788224808411195904526339 11682337212616793856789509)
        ·
          refine ⟨2190438227365648848148033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11682337212616793856789509 2190438227365648848148033)
          ·
            refine ⟨1642828670524236636111025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2190438227365648848148033 1642828670524236636111025)
            ·
              refine ⟨1232121502893177477083269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1642828670524236636111025 1232121502893177477083269)
              ·
                refine ⟨231022781792470776953113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1232121502893177477083269 231022781792470776953113)
                ·
                  refine ⟨173267086344353082714835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 231022781792470776953113 173267086344353082714835)
                  ·
                    refine ⟨259900629516529624072253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 173267086344353082714835 259900629516529624072253)
                    ·
                      refine ⟨97462736068698609027095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 259900629516529624072253 97462736068698609027095)
                      ·
                        rfl

theorem cell23_189808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 4, 2, 1, 3].length) (baseStart_189808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_189808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_189808 prefixEnd_189808 := by exact prefixLift 189808
  have htrace : WordTrace (prefixWord ++ tailWord_189808) baseStart_189808 baseEnd_189808 := by
    simpa [prefixWord, tailWord_189808, baseEnd_189808] using wordTrace_append hprefix tailTrace_189808
  have hstable : (prefixWord ++ tailWord_189808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189808).length < 2 ^ (prefixWord ++ tailWord_189808).sum := by decide
  have hdescent : baseEnd_189808 < baseStart_189808 := by decide
  rcases family_descends (prefixWord ++ tailWord_189808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189824 : List Nat := [2, 1, 1, 2, 1, 2, 1, 5, 2, 6]
def baseStart_189824 : Nat := 118140960795 + 189824 * 2 ^ 59
def prefixEnd_189824 : Nat := 4983230072969 + 3 ^ 40 * 189824 * 2
def baseEnd_189824 : Nat := 32490317253056848809007

theorem tailTrace_189824 : CollatzResearch.WordTrace tailWord_189824 prefixEnd_189824 32490317253056848809007 := by
  unfold tailWord_189824
  simp only [CollatzResearch.WordTrace]
  refine ⟨3461725032153771101636263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4615633376205028135515017 3461725032153771101636263)
  ·
    refine ⟨5192587548230656652454395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3461725032153771101636263 5192587548230656652454395)
    ·
      refine ⟨7788881322345984978681593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5192587548230656652454395 7788881322345984978681593)
      ·
        refine ⟨5841660991759488734011195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7788881322345984978681593 5841660991759488734011195)
        ·
          refine ⟨8762491487639233101016793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5841660991759488734011195 8762491487639233101016793)
          ·
            refine ⟨6571868615729424825762595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8762491487639233101016793 6571868615729424825762595)
            ·
              refine ⟨9857802923594137238643893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6571868615729424825762595 9857802923594137238643893)
              ·
                refine ⟨924169024086950366122865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9857802923594137238643893 924169024086950366122865)
                ·
                  refine ⟨693126768065212774592149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 924169024086950366122865 693126768065212774592149)
                  ·
                    refine ⟨32490317253056848809007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 693126768065212774592149 32490317253056848809007)
                    ·
                      rfl

theorem cell23_189824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 5, 2, 6].length) (baseStart_189824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_189824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_189824 prefixEnd_189824 := by exact prefixLift 189824
  have htrace : WordTrace (prefixWord ++ tailWord_189824) baseStart_189824 baseEnd_189824 := by
    simpa [prefixWord, tailWord_189824, baseEnd_189824] using wordTrace_append hprefix tailTrace_189824
  have hstable : (prefixWord ++ tailWord_189824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189824).length < 2 ^ (prefixWord ++ tailWord_189824).sum := by decide
  have hdescent : baseEnd_189824 < baseStart_189824 := by decide
  rcases family_descends (prefixWord ++ tailWord_189824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189938 : List Nat := [3, 2, 1, 4, 1, 1, 1, 2, 1, 3, 4]
def baseStart_189938 : Nat := 118140960795 + 189938 * 2 ^ 59
def prefixEnd_189938 : Nat := 4983230072969 + 3 ^ 40 * 189938 * 2
def baseEnd_189938 : Nat := 97529488553783100401497

theorem tailTrace_189938 : CollatzResearch.WordTrace tailWord_189938 prefixEnd_189938 97529488553783100401497 := by
  unfold tailWord_189938
  simp only [CollatzResearch.WordTrace]
  refine ⟨1731901996473634918230617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4618405323929693115281645 1731901996473634918230617)
  ·
    refine ⟨1298926497355226188672963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1731901996473634918230617 1298926497355226188672963)
    ·
      refine ⟨1948389746032839283009445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1298926497355226188672963 1948389746032839283009445)
      ·
        refine ⟨365323077381157365564271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1948389746032839283009445 365323077381157365564271)
        ·
          refine ⟨547984616071736048346407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 365323077381157365564271 547984616071736048346407)
          ·
            refine ⟨821976924107604072519611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 547984616071736048346407 821976924107604072519611)
            ·
              refine ⟨1232965386161406108779417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 821976924107604072519611 1232965386161406108779417)
              ·
                refine ⟨924724039621054581584563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1232965386161406108779417 924724039621054581584563)
                ·
                  refine ⟨1387086059431581872376845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 924724039621054581584563 1387086059431581872376845)
                  ·
                    refine ⟨520157272286843202141317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1387086059431581872376845 520157272286843202141317)
                    ·
                      refine ⟨97529488553783100401497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 520157272286843202141317 97529488553783100401497)
                      ·
                        rfl

theorem cell23_189938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_189938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_189938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_189938 prefixEnd_189938 := by exact prefixLift 189938
  have htrace : WordTrace (prefixWord ++ tailWord_189938) baseStart_189938 baseEnd_189938 := by
    simpa [prefixWord, tailWord_189938, baseEnd_189938] using wordTrace_append hprefix tailTrace_189938
  have hstable : (prefixWord ++ tailWord_189938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189938).length < 2 ^ (prefixWord ++ tailWord_189938).sum := by decide
  have hdescent : baseEnd_189938 < baseStart_189938 := by decide
  rcases family_descends (prefixWord ++ tailWord_189938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189948 : List Nat := [2, 2, 2, 1, 2, 1, 4, 2, 3, 4]
def baseStart_189948 : Nat := 118140960795 + 189948 * 2 ^ 59
def prefixEnd_189948 : Nat := 4983230072969 + 3 ^ 40 * 189948 * 2
def baseEnd_189948 : Nat := 32511541120109353758817

theorem tailTrace_189948 : CollatzResearch.WordTrace tailWord_189948 prefixEnd_189948 32511541120109353758817 := by
  unfold tailWord_189948
  simp only [CollatzResearch.WordTrace]
  refine ⟨3463986357929155690393249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4618648477238874253857665 3463986357929155690393249)
  ·
    refine ⟨2597989768446866767794937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3463986357929155690393249 2597989768446866767794937)
    ·
      refine ⟨1948492326335150075846203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2597989768446866767794937 1948492326335150075846203)
      ·
        refine ⟨2922738489502725113769305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1948492326335150075846203 2922738489502725113769305)
        ·
          refine ⟨2192053867127043835326979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2922738489502725113769305 2192053867127043835326979)
          ·
            refine ⟨3288080800690565752990469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2192053867127043835326979 3288080800690565752990469)
            ·
              refine ⟨616515150129481078685713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3288080800690565752990469 616515150129481078685713)
              ·
                refine ⟨462386362597110809014285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 616515150129481078685713 462386362597110809014285)
                ·
                  refine ⟨173394885973916553380357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 462386362597110809014285 173394885973916553380357)
                  ·
                    refine ⟨32511541120109353758817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 173394885973916553380357 32511541120109353758817)
                    ·
                      rfl

theorem cell23_189948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 2, 3, 4].length) (baseStart_189948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_189948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_189948 prefixEnd_189948 := by exact prefixLift 189948
  have htrace : WordTrace (prefixWord ++ tailWord_189948) baseStart_189948 baseEnd_189948 := by
    simpa [prefixWord, tailWord_189948, baseEnd_189948] using wordTrace_append hprefix tailTrace_189948
  have hstable : (prefixWord ++ tailWord_189948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189948).length < 2 ^ (prefixWord ++ tailWord_189948).sum := by decide
  have hdescent : baseEnd_189948 < baseStart_189948 := by decide
  rcases family_descends (prefixWord ++ tailWord_189948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_189972 : List Nat := [2, 4, 3, 1, 2, 1, 1, 2, 2, 1, 4]
def baseStart_189972 : Nat := 118140960795 + 189972 * 2 ^ 59
def prefixEnd_189972 : Nat := 4983230072969 + 3 ^ 40 * 189972 * 2
def baseEnd_189972 : Nat := 97546946896035967376341

theorem tailTrace_189972 : CollatzResearch.WordTrace tailWord_189972 prefixEnd_189972 97546946896035967376341 := by
  unfold tailWord_189972
  simp only [CollatzResearch.WordTrace]
  refine ⟨3464424033885681739830085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4619232045180908986440113 3464424033885681739830085)
  ·
    refine ⟨649579506353565326218141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3464424033885681739830085 649579506353565326218141)
    ·
      refine ⟨243592314882586997331803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 649579506353565326218141 243592314882586997331803)
      ·
        refine ⟨365388472323880495997705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243592314882586997331803 365388472323880495997705)
        ·
          refine ⟨274041354242910371998279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 365388472323880495997705 274041354242910371998279)
          ·
            refine ⟨411062031364365557997419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 274041354242910371998279 411062031364365557997419)
            ·
              refine ⟨616593047046548336996129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 411062031364365557997419 616593047046548336996129)
              ·
                refine ⟨462444785284911252747097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 616593047046548336996129 462444785284911252747097)
                ·
                  refine ⟨346833588963683439560323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 462444785284911252747097 346833588963683439560323)
                  ·
                    refine ⟨520250383445525159340485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 346833588963683439560323 520250383445525159340485)
                    ·
                      refine ⟨97546946896035967376341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 520250383445525159340485 97546946896035967376341)
                      ·
                        rfl

theorem cell23_189972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_189972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_189972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_189972 prefixEnd_189972 := by exact prefixLift 189972
  have htrace : WordTrace (prefixWord ++ tailWord_189972) baseStart_189972 baseEnd_189972 := by
    simpa [prefixWord, tailWord_189972, baseEnd_189972] using wordTrace_append hprefix tailTrace_189972
  have hstable : (prefixWord ++ tailWord_189972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_189972).length < 2 ^ (prefixWord ++ tailWord_189972).sum := by decide
  have hdescent : baseEnd_189972 < baseStart_189972 := by decide
  rcases family_descends (prefixWord ++ tailWord_189972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190008 : List Nat := [2, 1, 2, 1, 4, 3, 1, 1, 3, 5]
def baseStart_190008 : Nat := 118140960795 + 190008 * 2 ^ 59
def prefixEnd_190008 : Nat := 4983230072969 + 3 ^ 40 * 190008 * 2
def baseEnd_190008 : Nat := 32521810733199275508725

theorem tailTrace_190008 : CollatzResearch.WordTrace tailWord_190008 prefixEnd_190008 32521810733199275508725 := by
  unfold tailWord_190008
  simp only [CollatzResearch.WordTrace]
  refine ⟨3465080547820470813985339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4620107397093961085313785 3465080547820470813985339)
  ·
    refine ⟨5197620821730706220978009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3465080547820470813985339 5197620821730706220978009)
    ·
      refine ⟨3898215616298029665733507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5197620821730706220978009 3898215616298029665733507)
      ·
        refine ⟨5847323424447044498600261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3898215616298029665733507 5847323424447044498600261)
        ·
          refine ⟨1096373142083820843487549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5847323424447044498600261 1096373142083820843487549)
          ·
            refine ⟨411139928281432816307831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1096373142083820843487549 411139928281432816307831)
            ·
              refine ⟨616709892422149224461747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 411139928281432816307831 616709892422149224461747)
              ·
                refine ⟨925064838633223836692621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 616709892422149224461747 925064838633223836692621)
                ·
                  refine ⟨346899314487458938759733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 925064838633223836692621 346899314487458938759733)
                  ·
                    refine ⟨32521810733199275508725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 346899314487458938759733 32521810733199275508725)
                    ·
                      rfl

theorem cell23_190008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 1, 3, 5].length) (baseStart_190008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_190008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_190008 prefixEnd_190008 := by exact prefixLift 190008
  have htrace : WordTrace (prefixWord ++ tailWord_190008) baseStart_190008 baseEnd_190008 := by
    simpa [prefixWord, tailWord_190008, baseEnd_190008] using wordTrace_append hprefix tailTrace_190008
  have hstable : (prefixWord ++ tailWord_190008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190008).length < 2 ^ (prefixWord ++ tailWord_190008).sum := by decide
  have hdescent : baseEnd_190008 < baseStart_190008 := by decide
  rcases family_descends (prefixWord ++ tailWord_190008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190015 : List Nat := [1, 1, 2, 2, 3, 3, 1, 3, 2, 3, 2]
def baseStart_190015 : Nat := 118140960795 + 190015 * 2 ^ 59
def prefixEnd_190015 : Nat := 4983230072969 + 3 ^ 40 * 190015 * 2
def baseEnd_190015 : Nat := 97569026564179299138643

theorem tailTrace_190015 : CollatzResearch.WordTrace tailWord_190015 prefixEnd_190015 97569026564179299138643 := by
  unfold tailWord_190015
  simp only [CollatzResearch.WordTrace]
  refine ⟨6930416406615581823475499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4620277604410387882316999 6930416406615581823475499)
  ·
    refine ⟨10395624609923372735213249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6930416406615581823475499 10395624609923372735213249)
    ·
      refine ⟨7796718457442529551409937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10395624609923372735213249 7796718457442529551409937)
      ·
        refine ⟨5847538843081897163557453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7796718457442529551409937 5847538843081897163557453)
        ·
          refine ⟨2192827066155711436334045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5847538843081897163557453 2192827066155711436334045)
          ·
            refine ⟨822310149808391788625267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2192827066155711436334045 822310149808391788625267)
            ·
              refine ⟨1233465224712587682937901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 822310149808391788625267 1233465224712587682937901)
              ·
                refine ⟨462549459267220381101713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1233465224712587682937901 462549459267220381101713)
                ·
                  refine ⟨346912094450415285826285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 462549459267220381101713 346912094450415285826285)
                  ·
                    refine ⟨130092035418905732184857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 346912094450415285826285 130092035418905732184857)
                    ·
                      refine ⟨97569026564179299138643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 130092035418905732184857 97569026564179299138643)
                      ·
                        rfl

theorem cell23_190015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 3, 2, 3, 2].length) (baseStart_190015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_190015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_190015 prefixEnd_190015 := by exact prefixLift 190015
  have htrace : WordTrace (prefixWord ++ tailWord_190015) baseStart_190015 baseEnd_190015 := by
    simpa [prefixWord, tailWord_190015, baseEnd_190015] using wordTrace_append hprefix tailTrace_190015
  have hstable : (prefixWord ++ tailWord_190015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190015).length < 2 ^ (prefixWord ++ tailWord_190015).sum := by decide
  have hdescent : baseEnd_190015 < baseStart_190015 := by decide
  rcases family_descends (prefixWord ++ tailWord_190015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190039 : List Nat := [1, 1, 3, 2, 2, 3, 4, 2, 1, 1, 3]
def baseStart_190039 : Nat := 118140960795 + 190039 * 2 ^ 59
def prefixEnd_190039 : Nat := 4983230072969 + 3 ^ 40 * 190039 * 2
def baseEnd_190039 : Nat := 97581350099887205238533

theorem tailTrace_190039 : CollatzResearch.WordTrace tailWord_190039 prefixEnd_190039 97581350099887205238533 := by
  unfold tailWord_190039
  simp only [CollatzResearch.WordTrace]
  refine ⟨6931291758528633922349171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4620861172352422614899447 6931291758528633922349171)
  ·
    refine ⟨10396937637792950883523757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6931291758528633922349171 10396937637792950883523757)
    ·
      refine ⟨3898851614172356581321409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10396937637792950883523757 3898851614172356581321409)
      ·
        refine ⟨2924138710629267435991057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3898851614172356581321409 2924138710629267435991057)
        ·
          refine ⟨2193104032971950576993293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2924138710629267435991057 2193104032971950576993293)
          ·
            refine ⟨822414012364481466372485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2193104032971950576993293 822414012364481466372485)
            ·
              refine ⟨154202627318340274944841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 822414012364481466372485 154202627318340274944841)
              ·
                refine ⟨115651970488755206208631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 154202627318340274944841 115651970488755206208631)
                ·
                  refine ⟨173477955733132809312947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 115651970488755206208631 173477955733132809312947)
                  ·
                    refine ⟨260216933599699213969421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 173477955733132809312947 260216933599699213969421)
                    ·
                      refine ⟨97581350099887205238533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 260216933599699213969421 97581350099887205238533)
                      ·
                        rfl

theorem cell23_190039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 4, 2, 1, 1, 3].length) (baseStart_190039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_190039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_190039 prefixEnd_190039 := by exact prefixLift 190039
  have htrace : WordTrace (prefixWord ++ tailWord_190039) baseStart_190039 baseEnd_190039 := by
    simpa [prefixWord, tailWord_190039, baseEnd_190039] using wordTrace_append hprefix tailTrace_190039
  have hstable : (prefixWord ++ tailWord_190039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190039).length < 2 ^ (prefixWord ++ tailWord_190039).sum := by decide
  have hdescent : baseEnd_190039 < baseStart_190039 := by decide
  rcases family_descends (prefixWord ++ tailWord_190039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190041 : List Nat := [1, 2, 1, 2, 2, 1, 1, 3, 3, 1, 6]
def baseStart_190041 : Nat := 118140960795 + 190041 * 2 ^ 59
def prefixEnd_190041 : Nat := 4983230072969 + 3 ^ 40 * 190041 * 2
def baseEnd_190041 : Nat := 97582377061196197413523

theorem tailTrace_190041 : CollatzResearch.WordTrace tailWord_190041 prefixEnd_190041 97582377061196197413523 := by
  unfold tailWord_190041
  simp only [CollatzResearch.WordTrace]
  refine ⟨6931364704521388263921977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4620909803014258842614651 6931364704521388263921977)
  ·
    refine ⟨5198523528391041197941483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6931364704521388263921977 5198523528391041197941483)
    ·
      refine ⟨7797785292586561796912225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5198523528391041197941483 7797785292586561796912225)
      ·
        refine ⟨5848338969439921347684169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7797785292586561796912225 5848338969439921347684169)
        ·
          refine ⟨4386254227079941010763127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5848338969439921347684169 4386254227079941010763127)
          ·
            refine ⟨6579381340619911516144691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4386254227079941010763127 6579381340619911516144691)
            ·
              refine ⟨9869072010929867274217037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6579381340619911516144691 9869072010929867274217037)
              ·
                refine ⟨3700902004098700227831389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9869072010929867274217037 3700902004098700227831389)
                ·
                  refine ⟨1387838251537012585436771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3700902004098700227831389 1387838251537012585436771)
                  ·
                    refine ⟨2081757377305518878155157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1387838251537012585436771 2081757377305518878155157)
                    ·
                      refine ⟨97582377061196197413523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2081757377305518878155157 97582377061196197413523)
                      ·
                        rfl

theorem cell23_190041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 3, 3, 1, 6].length) (baseStart_190041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_190041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_190041 prefixEnd_190041 := by exact prefixLift 190041
  have htrace : WordTrace (prefixWord ++ tailWord_190041) baseStart_190041 baseEnd_190041 := by
    simpa [prefixWord, tailWord_190041, baseEnd_190041] using wordTrace_append hprefix tailTrace_190041
  have hstable : (prefixWord ++ tailWord_190041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190041).length < 2 ^ (prefixWord ++ tailWord_190041).sum := by decide
  have hdescent : baseEnd_190041 < baseStart_190041 := by decide
  rcases family_descends (prefixWord ++ tailWord_190041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190055 : List Nat := [1, 1, 5, 1, 1, 1, 4, 3, 2, 4]
def baseStart_190055 : Nat := 118140960795 + 190055 * 2 ^ 59
def prefixEnd_190055 : Nat := 4983230072969 + 3 ^ 40 * 190055 * 2
def baseEnd_190055 : Nat := 32529855263453047546153

theorem tailTrace_190055 : CollatzResearch.WordTrace tailWord_190055 prefixEnd_190055 32529855263453047546153 := by
  unfold tailWord_190055
  simp only [CollatzResearch.WordTrace]
  refine ⟨6931875326470668654931619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4621250217647112436621079 6931875326470668654931619)
  ·
    refine ⟨10397812989706002982397429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6931875326470668654931619 10397812989706002982397429)
    ·
      refine ⟨974794967784937779599759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10397812989706002982397429 974794967784937779599759)
      ·
        refine ⟨1462192451677406669399639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 974794967784937779599759 1462192451677406669399639)
        ·
          refine ⟨2193288677516110004099459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1462192451677406669399639 2193288677516110004099459)
          ·
            refine ⟨3289933016274165006149189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2193288677516110004099459 3289933016274165006149189)
            ·
              refine ⟨616862440551405938652973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3289933016274165006149189 616862440551405938652973)
              ·
                refine ⟨231323415206777226994865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 616862440551405938652973 231323415206777226994865)
                ·
                  refine ⟨173492561405082920246149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 231323415206777226994865 173492561405082920246149)
                  ·
                    refine ⟨32529855263453047546153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 173492561405082920246149 32529855263453047546153)
                    ·
                      rfl

theorem cell23_190055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 3, 2, 4].length) (baseStart_190055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_190055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_190055 prefixEnd_190055 := by exact prefixLift 190055
  have htrace : WordTrace (prefixWord ++ tailWord_190055) baseStart_190055 baseEnd_190055 := by
    simpa [prefixWord, tailWord_190055, baseEnd_190055] using wordTrace_append hprefix tailTrace_190055
  have hstable : (prefixWord ++ tailWord_190055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190055).length < 2 ^ (prefixWord ++ tailWord_190055).sum := by decide
  have hdescent : baseEnd_190055 < baseStart_190055 := by decide
  rcases family_descends (prefixWord ++ tailWord_190055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190105 : List Nat := [1, 2, 1, 2, 1, 2, 2, 4, 3, 3, 2]
def baseStart_190105 : Nat := 118140960795 + 190105 * 2 ^ 59
def prefixEnd_190105 : Nat := 4983230072969 + 3 ^ 40 * 190105 * 2
def baseEnd_190105 : Nat := 97615239823083947013229

theorem tailTrace_190105 : CollatzResearch.WordTrace tailWord_190105 prefixEnd_190105 97615239823083947013229 := by
  unfold tailWord_190105
  simp only [CollatzResearch.WordTrace]
  refine ⟨6933698976289527194251769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4622465984193018129501179 6933698976289527194251769)
  ·
    refine ⟨5200274232217145395688827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6933698976289527194251769 5200274232217145395688827)
    ·
      refine ⟨7800411348325718093533241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5200274232217145395688827 7800411348325718093533241)
      ·
        refine ⟨5850308511244288570149931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7800411348325718093533241 5850308511244288570149931)
        ·
          refine ⟨8775462766866432855224897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5850308511244288570149931 8775462766866432855224897)
          ·
            refine ⟨6581597075149824641418673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8775462766866432855224897 6581597075149824641418673)
            ·
              refine ⟨4936197806362368481064005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6581597075149824641418673 4936197806362368481064005)
              ·
                refine ⟨925537088692944090199501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4936197806362368481064005 925537088692944090199501)
                ·
                  refine ⟨347076408259854033824813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 925537088692944090199501 347076408259854033824813)
                  ·
                    refine ⟨130153653097445262684305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 347076408259854033824813 130153653097445262684305)
                    ·
                      refine ⟨97615239823083947013229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 130153653097445262684305 97615239823083947013229)
                      ·
                        rfl

theorem cell23_190105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 4, 3, 3, 2].length) (baseStart_190105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_190105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_190105 prefixEnd_190105 := by exact prefixLift 190105
  have htrace : WordTrace (prefixWord ++ tailWord_190105) baseStart_190105 baseEnd_190105 := by
    simpa [prefixWord, tailWord_190105, baseEnd_190105] using wordTrace_append hprefix tailTrace_190105
  have hstable : (prefixWord ++ tailWord_190105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190105).length < 2 ^ (prefixWord ++ tailWord_190105).sum := by decide
  have hdescent : baseEnd_190105 < baseStart_190105 := by decide
  rcases family_descends (prefixWord ++ tailWord_190105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190112 : List Nat := [2, 1, 1, 4, 3, 3, 1, 1, 1, 3, 3]
def baseStart_190112 : Nat := 118140960795 + 190112 * 2 ^ 59
def prefixEnd_190112 : Nat := 4983230072969 + 3 ^ 40 * 190112 * 2
def baseEnd_190112 : Nat := 97618834187665419625697

theorem tailTrace_190112 : CollatzResearch.WordTrace tailWord_190112 prefixEnd_190112 97618834187665419625697 := by
  unfold tailWord_190112
  simp only [CollatzResearch.WordTrace]
  refine ⟨3466977143632083694878295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4622636191509444926504393 3466977143632083694878295)
  ·
    refine ⟨5200465715448125542317443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3466977143632083694878295 5200465715448125542317443)
    ·
      refine ⟨7800698573172188313476165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5200465715448125542317443 7800698573172188313476165)
      ·
        refine ⟨1462630982469785308776781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7800698573172188313476165 1462630982469785308776781)
        ·
          refine ⟨548486618426169490791293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1462630982469785308776781 548486618426169490791293)
          ·
            refine ⟨205682481909813559046735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 548486618426169490791293 205682481909813559046735)
            ·
              refine ⟨308523722864720338570103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 205682481909813559046735 308523722864720338570103)
              ·
                refine ⟨462785584297080507855155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 308523722864720338570103 462785584297080507855155)
                ·
                  refine ⟨694178376445620761782733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 462785584297080507855155 694178376445620761782733)
                  ·
                    refine ⟨260316891167107785668525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 694178376445620761782733 260316891167107785668525)
                    ·
                      refine ⟨97618834187665419625697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 260316891167107785668525 97618834187665419625697)
                      ·
                        rfl

theorem cell23_190112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 1, 1, 1, 3, 3].length) (baseStart_190112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_190112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_190112 prefixEnd_190112 := by exact prefixLift 190112
  have htrace : WordTrace (prefixWord ++ tailWord_190112) baseStart_190112 baseEnd_190112 := by
    simpa [prefixWord, tailWord_190112, baseEnd_190112] using wordTrace_append hprefix tailTrace_190112
  have hstable : (prefixWord ++ tailWord_190112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190112).length < 2 ^ (prefixWord ++ tailWord_190112).sum := by decide
  have hdescent : baseEnd_190112 < baseStart_190112 := by decide
  rcases family_descends (prefixWord ++ tailWord_190112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190138 : List Nat := [3, 1, 1, 1, 2, 4, 1, 1, 1, 3, 5]
def baseStart_190138 : Nat := 118140960795 + 190138 * 2 ^ 59
def prefixEnd_190138 : Nat := 4983230072969 + 3 ^ 40 * 190138 * 2
def baseEnd_190138 : Nat := 97632184684682317900577

theorem tailTrace_190138 : CollatzResearch.WordTrace tailWord_190138 prefixEnd_190138 97632184684682317900577 := by
  unfold tailWord_190138
  simp only [CollatzResearch.WordTrace]
  refine ⟨1733725646292493457550767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4623268390113315886802045 1733725646292493457550767)
  ·
    refine ⟨2600588469438740186326151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1733725646292493457550767 2600588469438740186326151)
    ·
      refine ⟨3900882704158110279489227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2600588469438740186326151 3900882704158110279489227)
      ·
        refine ⟨5851324056237165419233841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3900882704158110279489227 5851324056237165419233841)
        ·
          refine ⟨4388493042177874064425381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5851324056237165419233841 4388493042177874064425381)
          ·
            refine ⟨822842445408351387079759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4388493042177874064425381 822842445408351387079759)
            ·
              refine ⟨1234263668112527080619639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 822842445408351387079759 1234263668112527080619639)
              ·
                refine ⟨1851395502168790620929459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1234263668112527080619639 1851395502168790620929459)
                ·
                  refine ⟨2777093253253185931394189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1851395502168790620929459 2777093253253185931394189)
                  ·
                    refine ⟨1041409969969944724272821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2777093253253185931394189 1041409969969944724272821)
                    ·
                      refine ⟨97632184684682317900577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1041409969969944724272821 97632184684682317900577)
                      ·
                        rfl

theorem cell23_190138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 1, 1, 3, 5].length) (baseStart_190138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_190138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_190138 prefixEnd_190138 := by exact prefixLift 190138
  have htrace : WordTrace (prefixWord ++ tailWord_190138) baseStart_190138 baseEnd_190138 := by
    simpa [prefixWord, tailWord_190138, baseEnd_190138] using wordTrace_append hprefix tailTrace_190138
  have hstable : (prefixWord ++ tailWord_190138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190138).length < 2 ^ (prefixWord ++ tailWord_190138).sum := by decide
  have hdescent : baseEnd_190138 < baseStart_190138 := by decide
  rcases family_descends (prefixWord ++ tailWord_190138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190152 : List Nat := [2, 1, 3, 1, 2, 2, 1, 3, 4, 2, 2]
def baseStart_190152 : Nat := 118140960795 + 190152 * 2 ^ 59
def prefixEnd_190152 : Nat := 4983230072969 + 3 ^ 40 * 190152 * 2
def baseEnd_190152 : Nat := 97639373413845263125513

theorem tailTrace_190152 : CollatzResearch.WordTrace tailWord_190152 prefixEnd_190152 97639373413845263125513 := by
  unfold tailWord_190152
  simp only [CollatzResearch.WordTrace]
  refine ⟨3467706603559627110606355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4623608804746169480808473 3467706603559627110606355)
  ·
    refine ⟨5201559905339440665909533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3467706603559627110606355 5201559905339440665909533)
    ·
      refine ⟨1950584964502290249716075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5201559905339440665909533 1950584964502290249716075)
      ·
        refine ⟨2925877446753435374574113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1950584964502290249716075 2925877446753435374574113)
        ·
          refine ⟨2194408085065076530930585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2925877446753435374574113 2194408085065076530930585)
          ·
            refine ⟨1645806063798807398197939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2194408085065076530930585 1645806063798807398197939)
            ·
              refine ⟨2468709095698211097296909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1645806063798807398197939 2468709095698211097296909)
              ·
                refine ⟨925765910886829161486341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2468709095698211097296909 925765910886829161486341)
                ·
                  refine ⟨173581108291280467778689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 925765910886829161486341 173581108291280467778689)
                  ·
                    refine ⟨130185831218460350834017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 173581108291280467778689 130185831218460350834017)
                    ·
                      refine ⟨97639373413845263125513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 130185831218460350834017 97639373413845263125513)
                      ·
                        rfl

theorem cell23_190152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 3, 4, 2, 2].length) (baseStart_190152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_190152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_190152 prefixEnd_190152 := by exact prefixLift 190152
  have htrace : WordTrace (prefixWord ++ tailWord_190152) baseStart_190152 baseEnd_190152 := by
    simpa [prefixWord, tailWord_190152, baseEnd_190152] using wordTrace_append hprefix tailTrace_190152
  have hstable : (prefixWord ++ tailWord_190152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190152).length < 2 ^ (prefixWord ++ tailWord_190152).sum := by decide
  have hdescent : baseEnd_190152 < baseStart_190152 := by decide
  rcases family_descends (prefixWord ++ tailWord_190152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190169 : List Nat := [1, 2, 1, 2, 3, 4, 1, 3, 2, 2, 2]
def baseStart_190169 : Nat := 118140960795 + 190169 * 2 ^ 59
def prefixEnd_190169 : Nat := 4983230072969 + 3 ^ 40 * 190169 * 2
def baseEnd_190169 : Nat := 97648102584971696612935

theorem tailTrace_190169 : CollatzResearch.WordTrace tailWord_190169 prefixEnd_190169 97648102584971696612935 := by
  unfold tailWord_190169
  simp only [CollatzResearch.WordTrace]
  refine ⟨6936033248057666124581561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4624022165371777416387707 6936033248057666124581561)
  ·
    refine ⟨5202024936043249593436171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6936033248057666124581561 5202024936043249593436171)
    ·
      refine ⟨7803037404064874390154257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5202024936043249593436171 7803037404064874390154257)
      ·
        refine ⟨5852278053048655792615693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7803037404064874390154257 5852278053048655792615693)
        ·
          refine ⟨2194604269893245922230885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5852278053048655792615693 2194604269893245922230885)
          ·
            refine ⟨411488300604983610418291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2194604269893245922230885 411488300604983610418291)
            ·
              refine ⟨617232450907475415627437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 411488300604983610418291 617232450907475415627437)
              ·
                refine ⟨231462169090303280860289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 617232450907475415627437 231462169090303280860289)
                ·
                  refine ⟨173596626817727460645217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 231462169090303280860289 173596626817727460645217)
                  ·
                    refine ⟨130197470113295595483913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 173596626817727460645217 130197470113295595483913)
                    ·
                      refine ⟨97648102584971696612935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 130197470113295595483913 97648102584971696612935)
                      ·
                        rfl

theorem cell23_190169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 3, 2, 2, 2].length) (baseStart_190169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_190169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_190169 prefixEnd_190169 := by exact prefixLift 190169
  have htrace : WordTrace (prefixWord ++ tailWord_190169) baseStart_190169 baseEnd_190169 := by
    simpa [prefixWord, tailWord_190169, baseEnd_190169] using wordTrace_append hprefix tailTrace_190169
  have hstable : (prefixWord ++ tailWord_190169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190169).length < 2 ^ (prefixWord ++ tailWord_190169).sum := by decide
  have hdescent : baseEnd_190169 < baseStart_190169 := by decide
  rcases family_descends (prefixWord ++ tailWord_190169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190173 : List Nat := [1, 4, 3, 3, 1, 2, 1, 2, 1, 3, 2]
def baseStart_190173 : Nat := 118140960795 + 190173 * 2 ^ 59
def prefixEnd_190173 : Nat := 4983230072969 + 3 ^ 40 * 190173 * 2
def baseEnd_190173 : Nat := 97650156507589680962917

theorem tailTrace_190173 : CollatzResearch.WordTrace tailWord_190173 prefixEnd_190173 97650156507589680962917 := by
  unfold tailWord_190173
  simp only [CollatzResearch.WordTrace]
  refine ⟨6936179140043174807727173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4624119426695449871818115 6936179140043174807727173)
  ·
    refine ⟨1300533588758095276448845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6936179140043174807727173 1300533588758095276448845)
    ·
      refine ⟨487700095784285728668317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1300533588758095276448845 487700095784285728668317)
      ·
        refine ⟨182887535919107148250619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 487700095784285728668317 182887535919107148250619)
        ·
          refine ⟨274331303878660722375929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182887535919107148250619 274331303878660722375929)
          ·
            refine ⟨205748477908995541781947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 274331303878660722375929 205748477908995541781947)
            ·
              refine ⟨308622716863493312672921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 205748477908995541781947 308622716863493312672921)
              ·
                refine ⟨231467037647619984504691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 308622716863493312672921 231467037647619984504691)
                ·
                  refine ⟨347200556471429976757037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 231467037647619984504691 347200556471429976757037)
                  ·
                    refine ⟨130200208676786241283889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 347200556471429976757037 130200208676786241283889)
                    ·
                      refine ⟨97650156507589680962917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 130200208676786241283889 97650156507589680962917)
                      ·
                        rfl

theorem cell23_190173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_190173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_190173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_190173 prefixEnd_190173 := by exact prefixLift 190173
  have htrace : WordTrace (prefixWord ++ tailWord_190173) baseStart_190173 baseEnd_190173 := by
    simpa [prefixWord, tailWord_190173, baseEnd_190173] using wordTrace_append hprefix tailTrace_190173
  have hstable : (prefixWord ++ tailWord_190173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190173).length < 2 ^ (prefixWord ++ tailWord_190173).sum := by decide
  have hdescent : baseEnd_190173 < baseStart_190173 := by decide
  rcases family_descends (prefixWord ++ tailWord_190173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190188 : List Nat := [2, 2, 1, 1, 2, 2, 2, 3, 1, 7]
def baseStart_190188 : Nat := 118140960795 + 190188 * 2 ^ 59
def prefixEnd_190188 : Nat := 4983230072969 + 3 ^ 40 * 190188 * 2
def baseEnd_190188 : Nat := 32552619572469040758449

theorem tailTrace_190188 : CollatzResearch.WordTrace tailWord_190188 prefixEnd_190188 32552619572469040758449 := by
  unfold tailWord_190188
  simp only [CollatzResearch.WordTrace]
  refine ⟨3468363117494416184761609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4624484156659221579682145 3468363117494416184761609)
  ·
    refine ⟨2601272338120812138571207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3468363117494416184761609 2601272338120812138571207)
    ·
      refine ⟨3901908507181218207856811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2601272338120812138571207 3901908507181218207856811)
      ·
        refine ⟨5852862760771827311785217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3901908507181218207856811 5852862760771827311785217)
        ·
          refine ⟨4389647070578870483838913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5852862760771827311785217 4389647070578870483838913)
          ·
            refine ⟨3292235302934152862879185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4389647070578870483838913 3292235302934152862879185)
            ·
              refine ⟨2469176477200614647159389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3292235302934152862879185 2469176477200614647159389)
              ·
                refine ⟨925941178950230492684771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2469176477200614647159389 925941178950230492684771)
                ·
                  refine ⟨1388911768425345739027157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 925941178950230492684771 1388911768425345739027157)
                  ·
                    refine ⟨32552619572469040758449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1388911768425345739027157 32552619572469040758449)
                    ·
                      rfl

theorem cell23_190188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 7].length) (baseStart_190188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_190188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_190188 prefixEnd_190188 := by exact prefixLift 190188
  have htrace : WordTrace (prefixWord ++ tailWord_190188) baseStart_190188 baseEnd_190188 := by
    simpa [prefixWord, tailWord_190188, baseEnd_190188] using wordTrace_append hprefix tailTrace_190188
  have hstable : (prefixWord ++ tailWord_190188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190188).length < 2 ^ (prefixWord ++ tailWord_190188).sum := by decide
  have hdescent : baseEnd_190188 < baseStart_190188 := by decide
  rcases family_descends (prefixWord ++ tailWord_190188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190212 : List Nat := [2, 3, 2, 2, 1, 2, 1, 1, 2, 5, 2]
def baseStart_190212 : Nat := 118140960795 + 190212 * 2 ^ 59
def prefixEnd_190212 : Nat := 4983230072969 + 3 ^ 40 * 190212 * 2
def baseEnd_190212 : Nat := 97670182253115028375237

theorem tailTrace_190212 : CollatzResearch.WordTrace tailWord_190212 prefixEnd_190212 97670182253115028375237 := by
  unfold tailWord_190212
  simp only [CollatzResearch.WordTrace]
  refine ⟨3468800793450942234198445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4625067724601256312264593 3468800793450942234198445)
  ·
    refine ⟨1300800297544103337824417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3468800793450942234198445 1300800297544103337824417)
    ·
      refine ⟨975600223158077503368313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1300800297544103337824417 975600223158077503368313)
      ·
        refine ⟨731700167368558127526235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 975600223158077503368313 731700167368558127526235)
        ·
          refine ⟨1097550251052837191289353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 731700167368558127526235 1097550251052837191289353)
          ·
            refine ⟨823162688289627893467015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1097550251052837191289353 823162688289627893467015)
            ·
              refine ⟨1234744032434441840200523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 823162688289627893467015 1234744032434441840200523)
              ·
                refine ⟨1852116048651662760300785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1234744032434441840200523 1852116048651662760300785)
                ·
                  refine ⟨1389087036488747070225589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1852116048651662760300785 1389087036488747070225589)
                  ·
                    refine ⟨130226909670820037833649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1389087036488747070225589 130226909670820037833649)
                    ·
                      refine ⟨97670182253115028375237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 130226909670820037833649 97670182253115028375237)
                      ·
                        rfl

theorem cell23_190212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 1, 2, 5, 2].length) (baseStart_190212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_190212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_190212 prefixEnd_190212 := by exact prefixLift 190212
  have htrace : WordTrace (prefixWord ++ tailWord_190212) baseStart_190212 baseEnd_190212 := by
    simpa [prefixWord, tailWord_190212, baseEnd_190212] using wordTrace_append hprefix tailTrace_190212
  have hstable : (prefixWord ++ tailWord_190212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190212).length < 2 ^ (prefixWord ++ tailWord_190212).sum := by decide
  have hdescent : baseEnd_190212 < baseStart_190212 := by decide
  rcases family_descends (prefixWord ++ tailWord_190212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190235 : List Nat := [1, 1, 1, 1, 1, 1, 4, 6, 3, 4]
def baseStart_190235 : Nat := 118140960795 + 190235 * 2 ^ 59
def prefixEnd_190235 : Nat := 4983230072969 + 3 ^ 40 * 190235 * 2
def baseEnd_190235 : Nat := 32560664102722812795877

theorem tailTrace_190235 : CollatzResearch.WordTrace tailWord_190235 prefixEnd_190235 32560664102722812795877 := by
  unfold tailWord_190235
  simp only [CollatzResearch.WordTrace]
  refine ⟨6938440465818559396484159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4625626977212372930989439 6938440465818559396484159)
  ·
    refine ⟨10407660698727839094726239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6938440465818559396484159 10407660698727839094726239)
    ·
      refine ⟨15611491048091758642089359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10407660698727839094726239 15611491048091758642089359)
      ·
        refine ⟨23417236572137637963134039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15611491048091758642089359 23417236572137637963134039)
        ·
          refine ⟨35125854858206456944701059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23417236572137637963134039 35125854858206456944701059)
          ·
            refine ⟨52688782287309685417051589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35125854858206456944701059 52688782287309685417051589)
            ·
              refine ⟨9879146678870566015697173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52688782287309685417051589 9879146678870566015697173)
              ·
                refine ⟨463085000572057781985805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9879146678870566015697173 463085000572057781985805)
                ·
                  refine ⟨173656875214521668244677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 463085000572057781985805 173656875214521668244677)
                  ·
                    refine ⟨32560664102722812795877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 173656875214521668244677 32560664102722812795877)
                    ·
                      rfl

theorem cell23_190235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 6, 3, 4].length) (baseStart_190235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_190235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_190235 prefixEnd_190235 := by exact prefixLift 190235
  have htrace : WordTrace (prefixWord ++ tailWord_190235) baseStart_190235 baseEnd_190235 := by
    simpa [prefixWord, tailWord_190235, baseEnd_190235] using wordTrace_append hprefix tailTrace_190235
  have hstable : (prefixWord ++ tailWord_190235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190235).length < 2 ^ (prefixWord ++ tailWord_190235).sum := by decide
  have hdescent : baseEnd_190235 < baseStart_190235 := by decide
  rcases family_descends (prefixWord ++ tailWord_190235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190242 : List Nat := [3, 3, 1, 1, 2, 1, 1, 2, 1, 6, 2]
def baseStart_190242 : Nat := 118140960795 + 190242 * 2 ^ 59
def prefixEnd_190242 : Nat := 4983230072969 + 3 ^ 40 * 190242 * 2
def baseEnd_190242 : Nat := 97685586672749911000099

theorem tailTrace_190242 : CollatzResearch.WordTrace tailWord_190242 prefixEnd_190242 97685586672749911000099 := by
  unfold tailWord_190242
  simp only [CollatzResearch.WordTrace]
  refine ⟨1734673944198299897997245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4625797184528799727992653 1734673944198299897997245)
  ·
    refine ⟨650502729074362461748967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1734673944198299897997245 650502729074362461748967)
    ·
      refine ⟨975754093611543692623451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 650502729074362461748967 975754093611543692623451)
      ·
        refine ⟨1463631140417315538935177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 975754093611543692623451 1463631140417315538935177)
        ·
          refine ⟨1097723355312986654201383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1463631140417315538935177 1097723355312986654201383)
          ·
            refine ⟨1646585032969479981302075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1097723355312986654201383 1646585032969479981302075)
            ·
              refine ⟨2469877549454219971953113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1646585032969479981302075 2469877549454219971953113)
              ·
                refine ⟨1852408162090664978964835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2469877549454219971953113 1852408162090664978964835)
                ·
                  refine ⟨2778612243135997468447253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1852408162090664978964835 2778612243135997468447253)
                  ·
                    refine ⟨130247448896999881333465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2778612243135997468447253 130247448896999881333465)
                    ·
                      refine ⟨97685586672749911000099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 130247448896999881333465 97685586672749911000099)
                      ·
                        rfl

theorem cell23_190242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 2, 1, 6, 2].length) (baseStart_190242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_190242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_190242 prefixEnd_190242 := by exact prefixLift 190242
  have htrace : WordTrace (prefixWord ++ tailWord_190242) baseStart_190242 baseEnd_190242 := by
    simpa [prefixWord, tailWord_190242, baseEnd_190242] using wordTrace_append hprefix tailTrace_190242
  have hstable : (prefixWord ++ tailWord_190242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190242).length < 2 ^ (prefixWord ++ tailWord_190242).sum := by decide
  have hdescent : baseEnd_190242 < baseStart_190242 := by decide
  rcases family_descends (prefixWord ++ tailWord_190242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190269 : List Nat := [1, 4, 1, 4, 1, 2, 2, 1, 3, 4]
def baseStart_190269 : Nat := 118140960795 + 190269 * 2 ^ 59
def prefixEnd_190269 : Nat := 4983230072969 + 3 ^ 40 * 190269 * 2
def baseEnd_190269 : Nat := 32566483550140435120825

theorem tailTrace_190269 : CollatzResearch.WordTrace tailWord_190269 prefixEnd_190269 32566483550140435120825 := by
  unfold tailWord_190269
  simp only [CollatzResearch.WordTrace]
  refine ⟨6939680547695383203221861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4626453698463588802147907 6939680547695383203221861)
  ·
    refine ⟨1301190102692884350604099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6939680547695383203221861 1301190102692884350604099)
    ·
      refine ⟨1951785154039326525906149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1301190102692884350604099 1951785154039326525906149)
      ·
        refine ⟨365959716382373723607403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1951785154039326525906149 365959716382373723607403)
        ·
          refine ⟨548939574573560585411105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 365959716382373723607403 548939574573560585411105)
          ·
            refine ⟨411704680930170439058329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 548939574573560585411105 411704680930170439058329)
            ·
              refine ⟨308778510697627829293747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 411704680930170439058329 308778510697627829293747)
              ·
                refine ⟨463167766046441743940621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 308778510697627829293747 463167766046441743940621)
                ·
                  refine ⟨173687912267415653977733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 463167766046441743940621 173687912267415653977733)
                  ·
                    refine ⟨32566483550140435120825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 173687912267415653977733 32566483550140435120825)
                    ·
                      rfl

theorem cell23_190269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 2, 1, 3, 4].length) (baseStart_190269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_190269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_190269 prefixEnd_190269 := by exact prefixLift 190269
  have htrace : WordTrace (prefixWord ++ tailWord_190269) baseStart_190269 baseEnd_190269 := by
    simpa [prefixWord, tailWord_190269, baseEnd_190269] using wordTrace_append hprefix tailTrace_190269
  have hstable : (prefixWord ++ tailWord_190269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190269).length < 2 ^ (prefixWord ++ tailWord_190269).sum := by decide
  have hdescent : baseEnd_190269 < baseStart_190269 := by decide
  rcases family_descends (prefixWord ++ tailWord_190269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190282 : List Nat := [3, 1, 2, 1, 1, 1, 7, 1, 6]
def baseStart_190282 : Nat := 118140960795 + 190282 * 2 ^ 59
def prefixEnd_190282 : Nat := 4983230072969 + 3 ^ 40 * 190282 * 2
def baseEnd_190282 : Nat := 10856236210992194944435

theorem tailTrace_190282 : CollatzResearch.WordTrace tailWord_190282 prefixEnd_190282 10856236210992194944435 := by
  unfold tailWord_190282
  simp only [CollatzResearch.WordTrace]
  refine ⟨1735038674162071605861275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4626769797765524282296733 1735038674162071605861275)
  ·
    refine ⟨2602558011243107408791913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1735038674162071605861275 2602558011243107408791913)
    ·
      refine ⟨1951918508432330556593935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2602558011243107408791913 1951918508432330556593935)
      ·
        refine ⟨2927877762648495834890903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1951918508432330556593935 2927877762648495834890903)
        ·
          refine ⟨4391816643972743752336355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2927877762648495834890903 4391816643972743752336355)
          ·
            refine ⟨6587724965959115628504533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4391816643972743752336355 6587724965959115628504533)
            ·
              refine ⟨154399803889666772543075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 6587724965959115628504533 154399803889666772543075)
              ·
                refine ⟨231599705834500158814613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 154399803889666772543075 231599705834500158814613)
                ·
                  refine ⟨10856236210992194944435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 231599705834500158814613 10856236210992194944435)
                  ·
                    rfl

theorem cell23_190282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 7, 1, 6].length) (baseStart_190282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_190282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_190282 prefixEnd_190282 := by exact prefixLift 190282
  have htrace : WordTrace (prefixWord ++ tailWord_190282) baseStart_190282 baseEnd_190282 := by
    simpa [prefixWord, tailWord_190282, baseEnd_190282] using wordTrace_append hprefix tailTrace_190282
  have hstable : (prefixWord ++ tailWord_190282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190282).length < 2 ^ (prefixWord ++ tailWord_190282).sum := by decide
  have hdescent : baseEnd_190282 < baseStart_190282 := by decide
  rcases family_descends (prefixWord ++ tailWord_190282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190312 : List Nat := [2, 1, 4, 2, 1, 1, 1, 5, 1, 5]
def baseStart_190312 : Nat := 118140960795 + 190312 * 2 ^ 59
def prefixEnd_190312 : Nat := 4983230072969 + 3 ^ 40 * 190312 * 2
def baseEnd_190312 : Nat := 32573843439521545708259

theorem tailTrace_190312 : CollatzResearch.WordTrace tailWord_190312 prefixEnd_190312 32573843439521545708259 := by
  unfold tailWord_190312
  simp only [CollatzResearch.WordTrace]
  refine ⟨3470624443269800773518595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4627499257693067698024793 3470624443269800773518595)
  ·
    refine ⟨5205936664904701160277893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3470624443269800773518595 5205936664904701160277893)
    ·
      refine ⟨976113124669631467552105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5205936664904701160277893 976113124669631467552105)
      ·
        refine ⟨732084843502223600664079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 976113124669631467552105 732084843502223600664079)
        ·
          refine ⟨1098127265253335400996119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 732084843502223600664079 1098127265253335400996119)
          ·
            refine ⟨1647190897880003101494179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1098127265253335400996119 1647190897880003101494179)
            ·
              refine ⟨2470786346820004652241269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1647190897880003101494179 2470786346820004652241269)
              ·
                refine ⟨231636220014375436147619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2470786346820004652241269 231636220014375436147619)
                ·
                  refine ⟨347454330021563154221429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 231636220014375436147619 347454330021563154221429)
                  ·
                    refine ⟨32573843439521545708259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 347454330021563154221429 32573843439521545708259)
                    ·
                      rfl

theorem cell23_190312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 5, 1, 5].length) (baseStart_190312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_190312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_190312 prefixEnd_190312 := by exact prefixLift 190312
  have htrace : WordTrace (prefixWord ++ tailWord_190312) baseStart_190312 baseEnd_190312 := by
    simpa [prefixWord, tailWord_190312, baseEnd_190312] using wordTrace_append hprefix tailTrace_190312
  have hstable : (prefixWord ++ tailWord_190312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190312).length < 2 ^ (prefixWord ++ tailWord_190312).sum := by decide
  have hdescent : baseEnd_190312 < baseStart_190312 := by decide
  rcases family_descends (prefixWord ++ tailWord_190312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190315 : List Nat := [1, 1, 1, 1, 2, 2, 3, 2, 5, 1, 4]
def baseStart_190315 : Nat := 118140960795 + 190315 * 2 ^ 59
def prefixEnd_190315 : Nat := 4983230072969 + 3 ^ 40 * 190315 * 2
def baseEnd_190315 : Nat := 97723070760528125387263

theorem tailTrace_190315 : CollatzResearch.WordTrace tailWord_190315 prefixEnd_190315 97723070760528125387263 := by
  unfold tailWord_190315
  simp only [CollatzResearch.WordTrace]
  refine ⟨6941358305528733059396399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4627572203685822039597599 6941358305528733059396399)
  ·
    refine ⟨10412037458293099589094599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6941358305528733059396399 10412037458293099589094599)
    ·
      refine ⟨15618056187439649383641899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10412037458293099589094599 15618056187439649383641899)
      ·
        refine ⟨23427084281159474075462849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15618056187439649383641899 23427084281159474075462849)
        ·
          refine ⟨17570313210869605556597137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23427084281159474075462849 17570313210869605556597137)
          ·
            refine ⟨13177734908152204167447853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17570313210869605556597137 13177734908152204167447853)
            ·
              refine ⟨4941650590557076562792945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13177734908152204167447853 4941650590557076562792945)
              ·
                refine ⟨3706237942917807422094709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4941650590557076562792945 3706237942917807422094709)
                ·
                  refine ⟨347459807148544445821379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3706237942917807422094709 347459807148544445821379)
                  ·
                    refine ⟨521189710722816668732069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 347459807148544445821379 521189710722816668732069)
                    ·
                      refine ⟨97723070760528125387263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 521189710722816668732069 97723070760528125387263)
                      ·
                        rfl

theorem cell23_190315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 2, 5, 1, 4].length) (baseStart_190315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_190315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_190315 prefixEnd_190315 := by exact prefixLift 190315
  have htrace : WordTrace (prefixWord ++ tailWord_190315) baseStart_190315 baseEnd_190315 := by
    simpa [prefixWord, tailWord_190315, baseEnd_190315] using wordTrace_append hprefix tailTrace_190315
  have hstable : (prefixWord ++ tailWord_190315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190315).length < 2 ^ (prefixWord ++ tailWord_190315).sum := by decide
  have hdescent : baseEnd_190315 < baseStart_190315 := by decide
  rcases family_descends (prefixWord ++ tailWord_190315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190335 : List Nat := [1, 1, 2, 2, 1, 1, 3, 1, 2, 6, 3]
def baseStart_190335 : Nat := 118140960795 + 190335 * 2 ^ 59
def prefixEnd_190335 : Nat := 4983230072969 + 3 ^ 40 * 190335 * 2
def baseEnd_190335 : Nat := 97733340373618047137171

theorem tailTrace_190335 : CollatzResearch.WordTrace tailWord_190335 prefixEnd_190335 97733340373618047137171 := by
  unfold tailWord_190335
  simp only [CollatzResearch.WordTrace]
  refine ⟨6942087765456276475124459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4628058510304184316749639 6942087765456276475124459)
  ·
    refine ⟨10413131648184414712686689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6942087765456276475124459 10413131648184414712686689)
    ·
      refine ⟨7809848736138311034515017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10413131648184414712686689 7809848736138311034515017)
      ·
        refine ⟨5857386552103733275886263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7809848736138311034515017 5857386552103733275886263)
        ·
          refine ⟨8786079828155599913829395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5857386552103733275886263 8786079828155599913829395)
          ·
            refine ⟨13179119742233399870744093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8786079828155599913829395 13179119742233399870744093)
            ·
              refine ⟨4942169903337524951529035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13179119742233399870744093 4942169903337524951529035)
              ·
                refine ⟨7413254855006287427293553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4942169903337524951529035 7413254855006287427293553)
                ·
                  refine ⟨5559941141254715570470165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7413254855006287427293553 5559941141254715570470165)
                  ·
                    refine ⟨260622240996314792365789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5559941141254715570470165 260622240996314792365789)
                    ·
                      refine ⟨97733340373618047137171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 260622240996314792365789 97733340373618047137171)
                      ·
                        rfl

theorem cell23_190335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 2, 6, 3].length) (baseStart_190335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_190335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_190335 prefixEnd_190335 := by exact prefixLift 190335
  have htrace : WordTrace (prefixWord ++ tailWord_190335) baseStart_190335 baseEnd_190335 := by
    simpa [prefixWord, tailWord_190335, baseEnd_190335] using wordTrace_append hprefix tailTrace_190335
  have hstable : (prefixWord ++ tailWord_190335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190335).length < 2 ^ (prefixWord ++ tailWord_190335).sum := by decide
  have hdescent : baseEnd_190335 < baseStart_190335 := by decide
  rcases family_descends (prefixWord ++ tailWord_190335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190345 : List Nat := [1, 2, 1, 1, 5, 1, 1, 3, 1, 1, 6]
def baseStart_190345 : Nat := 118140960795 + 190345 * 2 ^ 59
def prefixEnd_190345 : Nat := 4983230072969 + 3 ^ 40 * 190345 * 2
def baseEnd_190345 : Nat := 97738475180163008012125

theorem tailTrace_190345 : CollatzResearch.WordTrace tailWord_190345 prefixEnd_190345 97738475180163008012125 := by
  unfold tailWord_190345
  simp only [CollatzResearch.WordTrace]
  refine ⟨6942452495420048182988489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4628301663613365455325659 6942452495420048182988489)
  ·
    refine ⟨5206839371565036137241367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6942452495420048182988489 5206839371565036137241367)
    ·
      refine ⟨7810259057347554205862051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5206839371565036137241367 7810259057347554205862051)
      ·
        refine ⟨11715388586021331308793077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7810259057347554205862051 11715388586021331308793077)
        ·
          refine ⟨1098317679939499810199351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11715388586021331308793077 1098317679939499810199351)
          ·
            refine ⟨1647476519909249715299027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1098317679939499810199351 1647476519909249715299027)
            ·
              refine ⟨2471214779863874572948541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1647476519909249715299027 2471214779863874572948541)
              ·
                refine ⟨926705542448952964855703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2471214779863874572948541 926705542448952964855703)
                ·
                  refine ⟨1390058313673429447283555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 926705542448952964855703 1390058313673429447283555)
                  ·
                    refine ⟨2085087470510144170925333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1390058313673429447283555 2085087470510144170925333)
                    ·
                      refine ⟨97738475180163008012125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2085087470510144170925333 97738475180163008012125)
                      ·
                        rfl

theorem cell23_190345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 3, 1, 1, 6].length) (baseStart_190345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_190345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_190345 prefixEnd_190345 := by exact prefixLift 190345
  have htrace : WordTrace (prefixWord ++ tailWord_190345) baseStart_190345 baseEnd_190345 := by
    simpa [prefixWord, tailWord_190345, baseEnd_190345] using wordTrace_append hprefix tailTrace_190345
  have hstable : (prefixWord ++ tailWord_190345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190345).length < 2 ^ (prefixWord ++ tailWord_190345).sum := by decide
  have hdescent : baseEnd_190345 < baseStart_190345 := by decide
  rcases family_descends (prefixWord ++ tailWord_190345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190346 : List Nat := [3, 1, 2, 4, 2, 2, 1, 2, 1, 5]
def baseStart_190346 : Nat := 118140960795 + 190346 * 2 ^ 59
def prefixEnd_190346 : Nat := 4983230072969 + 3 ^ 40 * 190346 * 2
def baseEnd_190346 : Nat := 32579662886939168033207

theorem tailTrace_190346 : CollatzResearch.WordTrace tailWord_190346 prefixEnd_190346 32579662886939168033207 := by
  unfold tailWord_190346
  simp only [CollatzResearch.WordTrace]
  refine ⟨1735622242104106338443723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4628325978944283569183261 1735622242104106338443723)
  ·
    refine ⟨2603433363156159507665585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1735622242104106338443723 2603433363156159507665585)
    ·
      refine ⟨1952575022367119630749189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2603433363156159507665585 1952575022367119630749189)
      ·
        refine ⟨366107816693834930765473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1952575022367119630749189 366107816693834930765473)
        ·
          refine ⟨274580862520376198074105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 366107816693834930765473 274580862520376198074105)
          ·
            refine ⟨205935646890282148555579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 274580862520376198074105 205935646890282148555579)
            ·
              refine ⟨308903470335423222833369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 205935646890282148555579 308903470335423222833369)
              ·
                refine ⟨231677602751567417125027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 308903470335423222833369 231677602751567417125027)
                ·
                  refine ⟨347516404127351125687541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 231677602751567417125027 347516404127351125687541)
                  ·
                    refine ⟨32579662886939168033207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 347516404127351125687541 32579662886939168033207)
                    ·
                      rfl

theorem cell23_190346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 1, 2, 1, 5].length) (baseStart_190346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_190346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_190346 prefixEnd_190346 := by exact prefixLift 190346
  have htrace : WordTrace (prefixWord ++ tailWord_190346) baseStart_190346 baseEnd_190346 := by
    simpa [prefixWord, tailWord_190346, baseEnd_190346] using wordTrace_append hprefix tailTrace_190346
  have hstable : (prefixWord ++ tailWord_190346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190346).length < 2 ^ (prefixWord ++ tailWord_190346).sum := by decide
  have hdescent : baseEnd_190346 < baseStart_190346 := by decide
  rcases family_descends (prefixWord ++ tailWord_190346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190362 : List Nat := [3, 1, 1, 4, 2, 1, 1, 1, 3, 2, 4]
def baseStart_190362 : Nat := 118140960795 + 190362 * 2 ^ 59
def prefixEnd_190362 : Nat := 4983230072969 + 3 ^ 40 * 190362 * 2
def baseEnd_190362 : Nat := 97747204351289441499547

theorem tailTrace_190362 : CollatzResearch.WordTrace tailWord_190362 prefixEnd_190362 97747204351289441499547 := by
  unfold tailWord_190362
  simp only [CollatzResearch.WordTrace]
  refine ⟨1735768134089615021589335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4628715024238973390904893 1735768134089615021589335)
  ·
    refine ⟨2603652201134422532384003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1735768134089615021589335 2603652201134422532384003)
    ·
      refine ⟨3905478301701633798576005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2603652201134422532384003 3905478301701633798576005)
      ·
        refine ⟨732277181569056337233001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3905478301701633798576005 732277181569056337233001)
        ·
          refine ⟨549207886176792252924751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 732277181569056337233001 549207886176792252924751)
          ·
            refine ⟨823811829265188379387127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 549207886176792252924751 823811829265188379387127)
            ·
              refine ⟨1235717743897782569080691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 823811829265188379387127 1235717743897782569080691)
              ·
                refine ⟨1853576615846673853621037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1235717743897782569080691 1853576615846673853621037)
                ·
                  refine ⟨695091230942502695107889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1853576615846673853621037 695091230942502695107889)
                  ·
                    refine ⟨521318423206877021330917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 695091230942502695107889 521318423206877021330917)
                    ·
                      refine ⟨97747204351289441499547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 521318423206877021330917 97747204351289441499547)
                      ·
                        rfl

theorem cell23_190362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_190362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_190362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_190362 prefixEnd_190362 := by exact prefixLift 190362
  have htrace : WordTrace (prefixWord ++ tailWord_190362) baseStart_190362 baseEnd_190362 := by
    simpa [prefixWord, tailWord_190362, baseEnd_190362] using wordTrace_append hprefix tailTrace_190362
  have hstable : (prefixWord ++ tailWord_190362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190362).length < 2 ^ (prefixWord ++ tailWord_190362).sum := by decide
  have hdescent : baseEnd_190362 < baseStart_190362 := by decide
  rcases family_descends (prefixWord ++ tailWord_190362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190396 : List Nat := [2, 2, 2, 5, 1, 1, 2, 1, 1, 2, 4]
def baseStart_190396 : Nat := 118140960795 + 190396 * 2 ^ 59
def prefixEnd_190396 : Nat := 4983230072969 + 3 ^ 40 * 190396 * 2
def baseEnd_190396 : Nat := 97764662693542308474391

theorem tailTrace_190396 : CollatzResearch.WordTrace tailWord_190396 prefixEnd_190396 97764662693542308474391 := by
  unfold tailWord_190396
  simp only [CollatzResearch.WordTrace]
  refine ⟨3472156309117641946547521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4629541745490189262063361 3472156309117641946547521)
  ·
    refine ⟨2604117231838231459910641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3472156309117641946547521 2604117231838231459910641)
    ·
      refine ⟨1953087923878673594932981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2604117231838231459910641 1953087923878673594932981)
      ·
        refine ⟨183101992863625649524967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1953087923878673594932981 183101992863625649524967)
        ·
          refine ⟨274652989295438474287451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183101992863625649524967 274652989295438474287451)
          ·
            refine ⟨411979483943157711431177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 274652989295438474287451 411979483943157711431177)
            ·
              refine ⟨308984612957368283573383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 411979483943157711431177 308984612957368283573383)
              ·
                refine ⟨463476919436052425360075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 308984612957368283573383 463476919436052425360075)
                ·
                  refine ⟨695215379154078638040113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 463476919436052425360075 695215379154078638040113)
                  ·
                    refine ⟨521411534365558978530085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 695215379154078638040113 521411534365558978530085)
                    ·
                      refine ⟨97764662693542308474391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 521411534365558978530085 97764662693542308474391)
                      ·
                        rfl

theorem cell23_190396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_190396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_190396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_190396 prefixEnd_190396 := by exact prefixLift 190396
  have htrace : WordTrace (prefixWord ++ tailWord_190396) baseStart_190396 baseEnd_190396 := by
    simpa [prefixWord, tailWord_190396, baseEnd_190396] using wordTrace_append hprefix tailTrace_190396
  have hstable : (prefixWord ++ tailWord_190396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190396).length < 2 ^ (prefixWord ++ tailWord_190396).sum := by decide
  have hdescent : baseEnd_190396 < baseStart_190396 := by decide
  rcases family_descends (prefixWord ++ tailWord_190396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190399 : List Nat := [1, 1, 2, 2, 2, 1, 3, 5, 2, 1, 3]
def baseStart_190399 : Nat := 118140960795 + 190399 * 2 ^ 59
def prefixEnd_190399 : Nat := 4983230072969 + 3 ^ 40 * 190399 * 2
def baseEnd_190399 : Nat := 97766203135505796736877

theorem tailTrace_190399 : CollatzResearch.WordTrace tailWord_190399 prefixEnd_190399 97766203135505796736877 := by
  unfold tailWord_190399
  simp only [CollatzResearch.WordTrace]
  refine ⟨6944422037224415405454251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4629614691482943603636167 6944422037224415405454251)
  ·
    refine ⟨10416633055836623108181377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6944422037224415405454251 10416633055836623108181377)
    ·
      refine ⟨7812474791877467331136033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10416633055836623108181377 7812474791877467331136033)
      ·
        refine ⟨5859356093908100498352025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7812474791877467331136033 5859356093908100498352025)
        ·
          refine ⟨4394517070431075373764019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5859356093908100498352025 4394517070431075373764019)
          ·
            refine ⟨6591775605646613060646029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4394517070431075373764019 6591775605646613060646029)
            ·
              refine ⟨2471915852117479897742261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6591775605646613060646029 2471915852117479897742261)
              ·
                refine ⟨231742111136013740413337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2471915852117479897742261 231742111136013740413337)
                ·
                  refine ⟨173806583352010305310003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 231742111136013740413337 173806583352010305310003)
                  ·
                    refine ⟨260709875028015457965005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 173806583352010305310003 260709875028015457965005)
                    ·
                      refine ⟨97766203135505796736877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 260709875028015457965005 97766203135505796736877)
                      ·
                        rfl

theorem cell23_190399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 5, 2, 1, 3].length) (baseStart_190399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_190399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_190399 prefixEnd_190399 := by exact prefixLift 190399
  have htrace : WordTrace (prefixWord ++ tailWord_190399) baseStart_190399 baseEnd_190399 := by
    simpa [prefixWord, tailWord_190399, baseEnd_190399] using wordTrace_append hprefix tailTrace_190399
  have hstable : (prefixWord ++ tailWord_190399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190399).length < 2 ^ (prefixWord ++ tailWord_190399).sum := by decide
  have hdescent : baseEnd_190399 < baseStart_190399 := by decide
  rcases family_descends (prefixWord ++ tailWord_190399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190415 : List Nat := [1, 1, 2, 1, 1, 5, 1, 2, 1, 8]
def baseStart_190415 : Nat := 118140960795 + 190415 * 2 ^ 59
def prefixEnd_190415 : Nat := 4983230072969 + 3 ^ 40 * 190415 * 2
def baseEnd_190415 : Nat := 32591472941992578045601

theorem tailTrace_190415 : CollatzResearch.WordTrace tailWord_190415 prefixEnd_190415 32591472941992578045601 := by
  unfold tailWord_190415
  simp only [CollatzResearch.WordTrace]
  refine ⟨6945005605166450138036699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4630003736777633425357799 6945005605166450138036699)
  ·
    refine ⟨10417508407749675207055049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6945005605166450138036699 10417508407749675207055049)
    ·
      refine ⟨7813131305812256405291287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10417508407749675207055049 7813131305812256405291287)
      ·
        refine ⟨11719696958718384607936931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7813131305812256405291287 11719696958718384607936931)
        ·
          refine ⟨17579545438077576911905397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11719696958718384607936931 17579545438077576911905397)
          ·
            refine ⟨1648082384819772835491131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17579545438077576911905397 1648082384819772835491131)
            ·
              refine ⟨2472123577229659253236697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1648082384819772835491131 2472123577229659253236697)
              ·
                refine ⟨1854092682922244439927523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2472123577229659253236697 1854092682922244439927523)
                ·
                  refine ⟨2781139024383366659891285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1854092682922244439927523 2781139024383366659891285)
                  ·
                    refine ⟨32591472941992578045601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 2781139024383366659891285 32591472941992578045601)
                    ·
                      rfl

theorem cell23_190415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 2, 1, 8].length) (baseStart_190415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_190415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_190415 prefixEnd_190415 := by exact prefixLift 190415
  have htrace : WordTrace (prefixWord ++ tailWord_190415) baseStart_190415 baseEnd_190415 := by
    simpa [prefixWord, tailWord_190415, baseEnd_190415] using wordTrace_append hprefix tailTrace_190415
  have hstable : (prefixWord ++ tailWord_190415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190415).length < 2 ^ (prefixWord ++ tailWord_190415).sum := by decide
  have hdescent : baseEnd_190415 < baseStart_190415 := by decide
  rcases family_descends (prefixWord ++ tailWord_190415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190455 : List Nat := [1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 9]
def baseStart_190455 : Nat := 118140960795 + 190455 * 2 ^ 59
def prefixEnd_190455 : Nat := 4983230072969 + 3 ^ 40 * 190455 * 2
def baseEnd_190455 : Nat := 97794958052157577636619

theorem tailTrace_190455 : CollatzResearch.WordTrace tailWord_190455 prefixEnd_190455 97794958052157577636619 := by
  unfold tailWord_190455
  simp only [CollatzResearch.WordTrace]
  refine ⟨6946464525021536969492819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4630976350014357979661879 6946464525021536969492819)
  ·
    refine ⟨10419696787532305454239229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6946464525021536969492819 10419696787532305454239229)
    ·
      refine ⟨3907386295324614545339711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10419696787532305454239229 3907386295324614545339711)
      ·
        refine ⟨5861079442986921818009567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3907386295324614545339711 5861079442986921818009567)
        ·
          refine ⟨8791619164480382727014351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5861079442986921818009567 8791619164480382727014351)
          ·
            refine ⟨13187428746720574090521527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8791619164480382727014351 13187428746720574090521527)
            ·
              refine ⟨19781143120080861135782291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13187428746720574090521527 19781143120080861135782291)
              ·
                refine ⟨29671714680121291703673437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19781143120080861135782291 29671714680121291703673437)
                ·
                  refine ⟨11126893005045484388877539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29671714680121291703673437 11126893005045484388877539)
                  ·
                    refine ⟨16690339507568226583316309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11126893005045484388877539 16690339507568226583316309)
                    ·
                      refine ⟨97794958052157577636619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 16690339507568226583316309 97794958052157577636619)
                      ·
                        rfl

theorem cell23_190455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 9].length) (baseStart_190455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_190455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_190455 prefixEnd_190455 := by exact prefixLift 190455
  have htrace : WordTrace (prefixWord ++ tailWord_190455) baseStart_190455 baseEnd_190455 := by
    simpa [prefixWord, tailWord_190455, baseEnd_190455] using wordTrace_append hprefix tailTrace_190455
  have hstable : (prefixWord ++ tailWord_190455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190455).length < 2 ^ (prefixWord ++ tailWord_190455).sum := by decide
  have hdescent : baseEnd_190455 < baseStart_190455 := by decide
  rcases family_descends (prefixWord ++ tailWord_190455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190456 : List Nat := [2, 1, 2, 1, 1, 3, 2, 5, 2, 2, 2]
def baseStart_190456 : Nat := 118140960795 + 190456 * 2 ^ 59
def prefixEnd_190456 : Nat := 4983230072969 + 3 ^ 40 * 190456 * 2
def baseEnd_190456 : Nat := 97795471532812073724115

theorem tailTrace_190456 : CollatzResearch.WordTrace tailWord_190456 prefixEnd_190456 97795471532812073724115 := by
  unfold tailWord_190456
  simp only [CollatzResearch.WordTrace]
  refine ⟨3473250499008957070139611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4631000665345276093519481 3473250499008957070139611)
  ·
    refine ⟨5209875748513435605209417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3473250499008957070139611 5209875748513435605209417)
    ·
      refine ⟨3907406811385076703907063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5209875748513435605209417 3907406811385076703907063)
      ·
        refine ⟨5861110217077615055860595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3907406811385076703907063 5861110217077615055860595)
        ·
          refine ⟨8791665325616422583790893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5861110217077615055860595 8791665325616422583790893)
          ·
            refine ⟨3296874497106158468921585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8791665325616422583790893 3296874497106158468921585)
            ·
              refine ⟨2472655872829618851691189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3296874497106158468921585 2472655872829618851691189)
              ·
                refine ⟨231811488077776767346049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2472655872829618851691189 231811488077776767346049)
                ·
                  refine ⟨173858616058332575509537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 231811488077776767346049 173858616058332575509537)
                  ·
                    refine ⟨130393962043749431632153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 173858616058332575509537 130393962043749431632153)
                    ·
                      refine ⟨97795471532812073724115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 130393962043749431632153 97795471532812073724115)
                      ·
                        rfl

theorem cell23_190456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 5, 2, 2, 2].length) (baseStart_190456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_190456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_190456 prefixEnd_190456 := by exact prefixLift 190456
  have htrace : WordTrace (prefixWord ++ tailWord_190456) baseStart_190456 baseEnd_190456 := by
    simpa [prefixWord, tailWord_190456, baseEnd_190456] using wordTrace_append hprefix tailTrace_190456
  have hstable : (prefixWord ++ tailWord_190456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190456).length < 2 ^ (prefixWord ++ tailWord_190456).sum := by decide
  have hdescent : baseEnd_190456 < baseStart_190456 := by decide
  rcases family_descends (prefixWord ++ tailWord_190456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190499 : List Nat := [1, 1, 1, 4, 3, 1, 2, 1, 2, 5, 2]
def baseStart_190499 : Nat := 118140960795 + 190499 * 2 ^ 59
def prefixEnd_190499 : Nat := 4983230072969 + 3 ^ 40 * 190499 * 2
def baseEnd_190499 : Nat := 97817551200955405486417

theorem tailTrace_190499 : CollatzResearch.WordTrace tailWord_190499 prefixEnd_190499 97817551200955405486417 := by
  unfold tailWord_190499
  simp only [CollatzResearch.WordTrace]
  refine ⟨6948069336862132484094551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4632046224574754989396367 6948069336862132484094551)
  ·
    refine ⟨10422104005293198726141827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6948069336862132484094551 10422104005293198726141827)
    ·
      refine ⟨15633156007939798089212741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10422104005293198726141827 15633156007939798089212741)
      ·
        refine ⟨2931216751488712141727389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15633156007939798089212741 2931216751488712141727389)
        ·
          refine ⟨1099206281808267053147771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2931216751488712141727389 1099206281808267053147771)
          ·
            refine ⟨1648809422712400579721657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1099206281808267053147771 1648809422712400579721657)
            ·
              refine ⟨1236607067034300434791243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1648809422712400579721657 1236607067034300434791243)
              ·
                refine ⟨1854910600551450652186865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1236607067034300434791243 1854910600551450652186865)
                ·
                  refine ⟨1391182950413587989140149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1854910600551450652186865 1391182950413587989140149)
                  ·
                    refine ⟨130423401601273873981889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1391182950413587989140149 130423401601273873981889)
                    ·
                      refine ⟨97817551200955405486417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 130423401601273873981889 97817551200955405486417)
                      ·
                        rfl

theorem cell23_190499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 1, 2, 5, 2].length) (baseStart_190499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_190499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_190499 prefixEnd_190499 := by exact prefixLift 190499
  have htrace : WordTrace (prefixWord ++ tailWord_190499) baseStart_190499 baseEnd_190499 := by
    simpa [prefixWord, tailWord_190499, baseEnd_190499] using wordTrace_append hprefix tailTrace_190499
  have hstable : (prefixWord ++ tailWord_190499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190499).length < 2 ^ (prefixWord ++ tailWord_190499).sum := by decide
  have hdescent : baseEnd_190499 < baseStart_190499 := by decide
  rcases family_descends (prefixWord ++ tailWord_190499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190592 : List Nat := [2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 5]
def baseStart_190592 : Nat := 118140960795 + 190592 * 2 ^ 59
def prefixEnd_190592 : Nat := 4983230072969 + 3 ^ 40 * 190592 * 2
def baseEnd_190592 : Nat := 97865304901823541623489

theorem tailTrace_190592 : CollatzResearch.WordTrace tailWord_190592 prefixEnd_190592 97865304901823541623489 := by
  unfold tailWord_190592
  simp only [CollatzResearch.WordTrace]
  refine ⟨3475730662762604683615015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4634307550350139578153353 3475730662762604683615015)
  ·
    refine ⟨5213595994143907025422523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3475730662762604683615015 5213595994143907025422523)
    ·
      refine ⟨7820393991215860538133785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5213595994143907025422523 7820393991215860538133785)
      ·
        refine ⟨5865295493411895403600339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7820393991215860538133785 5865295493411895403600339)
        ·
          refine ⟨8797943240117843105400509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5865295493411895403600339 8797943240117843105400509)
          ·
            refine ⟨3299228715044191164525191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8797943240117843105400509 3299228715044191164525191)
            ·
              refine ⟨4948843072566286746787787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3299228715044191164525191 4948843072566286746787787)
              ·
                refine ⟨7423264608849430120181681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4948843072566286746787787 7423264608849430120181681)
                ·
                  refine ⟨5567448456637072590136261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7423264608849430120181681 5567448456637072590136261)
                  ·
                    refine ⟨1043896585619451110650549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5567448456637072590136261 1043896585619451110650549)
                    ·
                      refine ⟨97865304901823541623489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1043896585619451110650549 97865304901823541623489)
                      ·
                        rfl

theorem cell23_190592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 5].length) (baseStart_190592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_190592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_190592 prefixEnd_190592 := by exact prefixLift 190592
  have htrace : WordTrace (prefixWord ++ tailWord_190592) baseStart_190592 baseEnd_190592 := by
    simpa [prefixWord, tailWord_190592, baseEnd_190592] using wordTrace_append hprefix tailTrace_190592
  have hstable : (prefixWord ++ tailWord_190592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190592).length < 2 ^ (prefixWord ++ tailWord_190592).sum := by decide
  have hdescent : baseEnd_190592 < baseStart_190592 := by decide
  rcases family_descends (prefixWord ++ tailWord_190592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190596 : List Nat := [2, 3, 2, 1, 2, 1, 1, 2, 5, 1, 3]
def baseStart_190596 : Nat := 118140960795 + 190596 * 2 ^ 59
def prefixEnd_190596 : Nat := 4983230072969 + 3 ^ 40 * 190596 * 2
def baseEnd_190596 : Nat := 97867358824441525973471

theorem tailTrace_190596 : CollatzResearch.WordTrace tailWord_190596 prefixEnd_190596 97867358824441525973471 := by
  unfold tailWord_190596
  simp only [CollatzResearch.WordTrace]
  refine ⟨3475803608755359025187821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4634404811673812033583761 3475803608755359025187821)
  ·
    refine ⟨1303426353283259634445433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3475803608755359025187821 1303426353283259634445433)
    ·
      refine ⟨977569764962444725834075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1303426353283259634445433 977569764962444725834075)
      ·
        refine ⟨1466354647443667088751113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 977569764962444725834075 1466354647443667088751113)
        ·
          refine ⟨1099765985582750316563335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1466354647443667088751113 1099765985582750316563335)
          ·
            refine ⟨1649648978374125474845003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1099765985582750316563335 1649648978374125474845003)
            ·
              refine ⟨2474473467561188212267505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1649648978374125474845003 2474473467561188212267505)
              ·
                refine ⟨1855855100670891159200629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2474473467561188212267505 1855855100670891159200629)
                ·
                  refine ⟨173986415687896046175059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1855855100670891159200629 173986415687896046175059)
                  ·
                    refine ⟨260979623531844069262589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 173986415687896046175059 260979623531844069262589)
                    ·
                      refine ⟨97867358824441525973471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 260979623531844069262589 97867358824441525973471)
                      ·
                        rfl

theorem cell23_190596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 2, 5, 1, 3].length) (baseStart_190596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_190596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_190596 prefixEnd_190596 := by exact prefixLift 190596
  have htrace : WordTrace (prefixWord ++ tailWord_190596) baseStart_190596 baseEnd_190596 := by
    simpa [prefixWord, tailWord_190596, baseEnd_190596] using wordTrace_append hprefix tailTrace_190596
  have hstable : (prefixWord ++ tailWord_190596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190596).length < 2 ^ (prefixWord ++ tailWord_190596).sum := by decide
  have hdescent : baseEnd_190596 < baseStart_190596 := by decide
  rcases family_descends (prefixWord ++ tailWord_190596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190613 : List Nat := [1, 3, 2, 1, 1, 1, 3, 6, 1, 1, 3]
def baseStart_190613 : Nat := 118140960795 + 190613 * 2 ^ 59
def prefixEnd_190613 : Nat := 4983230072969 + 3 ^ 40 * 190613 * 2
def baseEnd_190613 : Nat := 97876087995567959460893

theorem tailTrace_190613 : CollatzResearch.WordTrace tailWord_190613 prefixEnd_190613 97876087995567959460893 := by
  unfold tailWord_190613
  simp only [CollatzResearch.WordTrace]
  refine ⟨6952227258449129953744493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4634818172299419969162995 6952227258449129953744493)
  ·
    refine ⟨2607085221918423732654185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6952227258449129953744493 2607085221918423732654185)
    ·
      refine ⟨1955313916438817799490639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2607085221918423732654185 1955313916438817799490639)
      ·
        refine ⟨2932970874658226699235959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1955313916438817799490639 2932970874658226699235959)
        ·
          refine ⟨4399456311987340048853939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2932970874658226699235959 4399456311987340048853939)
          ·
            refine ⟨6599184467981010073280909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4399456311987340048853939 6599184467981010073280909)
            ·
              refine ⟨2474694175492878777480341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6599184467981010073280909 2474694175492878777480341)
              ·
                refine ⟨116001289476228692694391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2474694175492878777480341 116001289476228692694391)
                ·
                  refine ⟨174001934214343039041587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 116001289476228692694391 174001934214343039041587)
                  ·
                    refine ⟨261002901321514558562381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 174001934214343039041587 261002901321514558562381)
                    ·
                      refine ⟨97876087995567959460893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 261002901321514558562381 97876087995567959460893)
                      ·
                        rfl

theorem cell23_190613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 6, 1, 1, 3].length) (baseStart_190613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_190613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_190613 prefixEnd_190613 := by exact prefixLift 190613
  have htrace : WordTrace (prefixWord ++ tailWord_190613) baseStart_190613 baseEnd_190613 := by
    simpa [prefixWord, tailWord_190613, baseEnd_190613] using wordTrace_append hprefix tailTrace_190613
  have hstable : (prefixWord ++ tailWord_190613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190613).length < 2 ^ (prefixWord ++ tailWord_190613).sum := by decide
  have hdescent : baseEnd_190613 < baseStart_190613 := by decide
  rcases family_descends (prefixWord ++ tailWord_190613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190649 : List Nat := [1, 2, 1, 4, 1, 2, 2, 1, 3, 2, 4]
def baseStart_190649 : Nat := 118140960795 + 190649 * 2 ^ 59
def prefixEnd_190649 : Nat := 4983230072969 + 3 ^ 40 * 190649 * 2
def baseEnd_190649 : Nat := 97894573299129818610727

theorem tailTrace_190649 : CollatzResearch.WordTrace tailWord_190649 prefixEnd_190649 97894573299129818610727 := by
  unfold tailWord_190649
  simp only [CollatzResearch.WordTrace]
  refine ⟨6953540286318708102055001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4635693524212472068036667 6953540286318708102055001)
  ·
    refine ⟨5215155214739031076541251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6953540286318708102055001 5215155214739031076541251)
    ·
      refine ⟨7822732822108546614811877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5215155214739031076541251 7822732822108546614811877)
      ·
        refine ⟨1466762404145352490277227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7822732822108546614811877 1466762404145352490277227)
        ·
          refine ⟨2200143606218028735415841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1466762404145352490277227 2200143606218028735415841)
          ·
            refine ⟨1650107704663521551561881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2200143606218028735415841 1650107704663521551561881)
            ·
              refine ⟨1237580778497641163671411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1650107704663521551561881 1237580778497641163671411)
              ·
                refine ⟨1856371167746461745507117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1237580778497641163671411 1856371167746461745507117)
                ·
                  refine ⟨696139187904923154565169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1856371167746461745507117 696139187904923154565169)
                  ·
                    refine ⟨522104390928692365923877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 696139187904923154565169 522104390928692365923877)
                    ·
                      refine ⟨97894573299129818610727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 522104390928692365923877 97894573299129818610727)
                      ·
                        rfl

theorem cell23_190649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 1, 3, 2, 4].length) (baseStart_190649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_190649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_190649 prefixEnd_190649 := by exact prefixLift 190649
  have htrace : WordTrace (prefixWord ++ tailWord_190649) baseStart_190649 baseEnd_190649 := by
    simpa [prefixWord, tailWord_190649, baseEnd_190649] using wordTrace_append hprefix tailTrace_190649
  have hstable : (prefixWord ++ tailWord_190649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190649).length < 2 ^ (prefixWord ++ tailWord_190649).sum := by decide
  have hdescent : baseEnd_190649 < baseStart_190649 := by decide
  rcases family_descends (prefixWord ++ tailWord_190649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190656 : List Nat := [2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 5]
def baseStart_190656 : Nat := 118140960795 + 190656 * 2 ^ 59
def prefixEnd_190656 : Nat := 4983230072969 + 3 ^ 40 * 190656 * 2
def baseEnd_190656 : Nat := 97898167663711291223195

theorem tailTrace_190656 : CollatzResearch.WordTrace tailWord_190656 prefixEnd_190656 97898167663711291223195 := by
  unfold tailWord_190656
  simp only [CollatzResearch.WordTrace]
  refine ⟨3476897798646674148779911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4635863731528898865039881 3476897798646674148779911)
  ·
    refine ⟨5215346697970011223169867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3476897798646674148779911 5215346697970011223169867)
    ·
      refine ⟨7823020046955016834754801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5215346697970011223169867 7823020046955016834754801)
      ·
        refine ⟨5867265035216262626066101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7823020046955016834754801 5867265035216262626066101)
        ·
          refine ⟨550056097051524621193697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5867265035216262626066101 550056097051524621193697)
          ·
            refine ⟨412542072788643465895273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 550056097051524621193697 412542072788643465895273)
            ·
              refine ⟨309406554591482599421455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 412542072788643465895273 309406554591482599421455)
              ·
                refine ⟨464109831887223899132183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 309406554591482599421455 464109831887223899132183)
                ·
                  refine ⟨696164747830835848698275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 464109831887223899132183 696164747830835848698275)
                  ·
                    refine ⟨1044247121746253773047413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 696164747830835848698275 1044247121746253773047413)
                    ·
                      refine ⟨97898167663711291223195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1044247121746253773047413 97898167663711291223195)
                      ·
                        rfl

theorem cell23_190656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 5].length) (baseStart_190656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_190656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_190656 prefixEnd_190656 := by exact prefixLift 190656
  have htrace : WordTrace (prefixWord ++ tailWord_190656) baseStart_190656 baseEnd_190656 := by
    simpa [prefixWord, tailWord_190656, baseEnd_190656] using wordTrace_append hprefix tailTrace_190656
  have hstable : (prefixWord ++ tailWord_190656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190656).length < 2 ^ (prefixWord ++ tailWord_190656).sum := by decide
  have hdescent : baseEnd_190656 < baseStart_190656 := by decide
  rcases family_descends (prefixWord ++ tailWord_190656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190670 : List Nat := [4, 1, 1, 1, 4, 1, 3, 1, 3, 2, 2]
def baseStart_190670 : Nat := 118140960795 + 190670 * 2 ^ 59
def prefixEnd_190670 : Nat := 4983230072969 + 3 ^ 40 * 190670 * 2
def baseEnd_190670 : Nat := 97905356392874236448131

theorem tailTrace_190670 : CollatzResearch.WordTrace tailWord_190670 prefixEnd_190670 97905356392874236448131 := by
  unfold tailWord_190670
  simp only [CollatzResearch.WordTrace]
  refine ⟨869288277405328586071183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4636204146161752459046309 869288277405328586071183)
  ·
    refine ⟨1303932416107992879106775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 869288277405328586071183 1303932416107992879106775)
    ·
      refine ⟨1955898624161989318660163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1303932416107992879106775 1955898624161989318660163)
      ·
        refine ⟨2933847936242983977990245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1955898624161989318660163 2933847936242983977990245)
        ·
          refine ⟨550096488045559495873171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2933847936242983977990245 550096488045559495873171)
          ·
            refine ⟨825144732068339243809757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 550096488045559495873171 825144732068339243809757)
            ·
              refine ⟨309429274525627216428659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 825144732068339243809757 309429274525627216428659)
              ·
                refine ⟨464143911788440824642989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 309429274525627216428659 464143911788440824642989)
                ·
                  refine ⟨174053966920665309241121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 464143911788440824642989 174053966920665309241121)
                  ·
                    refine ⟨130540475190498981930841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 174053966920665309241121 130540475190498981930841)
                    ·
                      refine ⟨97905356392874236448131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 130540475190498981930841 97905356392874236448131)
                      ·
                        rfl

theorem cell23_190670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 3, 1, 3, 2, 2].length) (baseStart_190670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_190670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_190670 prefixEnd_190670 := by exact prefixLift 190670
  have htrace : WordTrace (prefixWord ++ tailWord_190670) baseStart_190670 baseEnd_190670 := by
    simpa [prefixWord, tailWord_190670, baseEnd_190670] using wordTrace_append hprefix tailTrace_190670
  have hstable : (prefixWord ++ tailWord_190670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190670).length < 2 ^ (prefixWord ++ tailWord_190670).sum := by decide
  have hdescent : baseEnd_190670 < baseStart_190670 := by decide
  rcases family_descends (prefixWord ++ tailWord_190670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190680 : List Nat := [2, 1, 2, 2, 4, 3, 2, 1, 2, 4]
def baseStart_190680 : Nat := 118140960795 + 190680 * 2 ^ 59
def prefixEnd_190680 : Nat := 4983230072969 + 3 ^ 40 * 190680 * 2
def baseEnd_190680 : Nat := 32636830399806399107695

theorem tailTrace_190680 : CollatzResearch.WordTrace tailWord_190680 prefixEnd_190680 32636830399806399107695 := by
  unfold tailWord_190680
  simp only [CollatzResearch.WordTrace]
  refine ⟨3477335474603200198216747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4636447299470933597622329 3477335474603200198216747)
  ·
    refine ⟨5216003211904800297325121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3477335474603200198216747 5216003211904800297325121)
    ·
      refine ⟨3912002408928600222993841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5216003211904800297325121 3912002408928600222993841)
      ·
        refine ⟨2934001806696450167245381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3912002408928600222993841 2934001806696450167245381)
        ·
          refine ⟨550125338755584406358509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2934001806696450167245381 550125338755584406358509)
          ·
            refine ⟨206297002033344152384441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 550125338755584406358509 206297002033344152384441)
            ·
              refine ⟨154722751525008114288331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 206297002033344152384441 154722751525008114288331)
              ·
                refine ⟨232084127287512171432497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 154722751525008114288331 232084127287512171432497)
                ·
                  refine ⟨174063095465634128574373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 232084127287512171432497 174063095465634128574373)
                  ·
                    refine ⟨32636830399806399107695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 174063095465634128574373 32636830399806399107695)
                    ·
                      rfl

theorem cell23_190680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 2, 1, 2, 4].length) (baseStart_190680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_190680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_190680 prefixEnd_190680 := by exact prefixLift 190680
  have htrace : WordTrace (prefixWord ++ tailWord_190680) baseStart_190680 baseEnd_190680 := by
    simpa [prefixWord, tailWord_190680, baseEnd_190680] using wordTrace_append hprefix tailTrace_190680
  have hstable : (prefixWord ++ tailWord_190680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190680).length < 2 ^ (prefixWord ++ tailWord_190680).sum := by decide
  have hdescent : baseEnd_190680 < baseStart_190680 := by decide
  rcases family_descends (prefixWord ++ tailWord_190680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190719 : List Nat := [1, 1, 2, 2, 1, 4, 2, 2, 2, 6]
def baseStart_190719 : Nat := 118140960795 + 190719 * 2 ^ 59
def prefixEnd_190719 : Nat := 4983230072969 + 3 ^ 40 * 190719 * 2
def baseEnd_190719 : Nat := 32643505648314848245135

theorem tailTrace_190719 : CollatzResearch.WordTrace tailWord_190719 prefixEnd_190719 32643505648314848245135 := by
  unfold tailWord_190719
  simp only [CollatzResearch.WordTrace]
  refine ⟨6956093396065110057103211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4637395597376740038068807 6956093396065110057103211)
  ·
    refine ⟨10434140094097665085654817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6956093396065110057103211 10434140094097665085654817)
    ·
      refine ⟨7825605070573248814241113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10434140094097665085654817 7825605070573248814241113)
      ·
        refine ⟨5869203802929936610680835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7825605070573248814241113 5869203802929936610680835)
        ·
          refine ⟨8803805704394904916021253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5869203802929936610680835 8803805704394904916021253)
          ·
            refine ⟨1650713569574044671753985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8803805704394904916021253 1650713569574044671753985)
            ·
              refine ⟨1238035177180533503815489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1650713569574044671753985 1238035177180533503815489)
              ·
                refine ⟨928526382885400127861617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1238035177180533503815489 928526382885400127861617)
                ·
                  refine ⟨696394787164050095896213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 928526382885400127861617 696394787164050095896213)
                  ·
                    refine ⟨32643505648314848245135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 696394787164050095896213 32643505648314848245135)
                    ·
                      rfl

theorem cell23_190719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 2, 2, 6].length) (baseStart_190719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_190719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_190719 prefixEnd_190719 := by exact prefixLift 190719
  have htrace : WordTrace (prefixWord ++ tailWord_190719) baseStart_190719 baseEnd_190719 := by
    simpa [prefixWord, tailWord_190719, baseEnd_190719] using wordTrace_append hprefix tailTrace_190719
  have hstable : (prefixWord ++ tailWord_190719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190719).length < 2 ^ (prefixWord ++ tailWord_190719).sum := by decide
  have hdescent : baseEnd_190719 < baseStart_190719 := by decide
  rcases family_descends (prefixWord ++ tailWord_190719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190743 : List Nat := [1, 1, 3, 4, 1, 2, 1, 3, 1, 4, 2]
def baseStart_190743 : Nat := 118140960795 + 190743 * 2 ^ 59
def prefixEnd_190743 : Nat := 4983230072969 + 3 ^ 40 * 190743 * 2
def baseEnd_190743 : Nat := 97942840480652450835295

theorem tailTrace_190743 : CollatzResearch.WordTrace tailWord_190743 prefixEnd_190743 97942840480652450835295 := by
  unfold tailWord_190743
  simp only [CollatzResearch.WordTrace]
  refine ⟨6956968747978162155976883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4637979165318774770651255 6956968747978162155976883)
  ·
    refine ⟨10435453121967243233965325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6956968747978162155976883 10435453121967243233965325)
    ·
      refine ⟨3913294920737716212736997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10435453121967243233965325 3913294920737716212736997)
      ·
        refine ⟨733742797638321789888187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3913294920737716212736997 733742797638321789888187)
        ·
          refine ⟨1100614196457482684832281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 733742797638321789888187 1100614196457482684832281)
          ·
            refine ⟨825460647343112013624211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1100614196457482684832281 825460647343112013624211)
            ·
              refine ⟨1238190971014668020436317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 825460647343112013624211 1238190971014668020436317)
              ·
                refine ⟨464321614130500507663619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1238190971014668020436317 464321614130500507663619)
                ·
                  refine ⟨696482421195750761495429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 464321614130500507663619 696482421195750761495429)
                  ·
                    refine ⟨130590453974203267780393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 696482421195750761495429 130590453974203267780393)
                    ·
                      refine ⟨97942840480652450835295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 130590453974203267780393 97942840480652450835295)
                      ·
                        rfl

theorem cell23_190743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 3, 1, 4, 2].length) (baseStart_190743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_190743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_190743 prefixEnd_190743 := by exact prefixLift 190743
  have htrace : WordTrace (prefixWord ++ tailWord_190743) baseStart_190743 baseEnd_190743 := by
    simpa [prefixWord, tailWord_190743, baseEnd_190743] using wordTrace_append hprefix tailTrace_190743
  have hstable : (prefixWord ++ tailWord_190743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190743).length < 2 ^ (prefixWord ++ tailWord_190743).sum := by decide
  have hdescent : baseEnd_190743 < baseStart_190743 := by decide
  rcases family_descends (prefixWord ++ tailWord_190743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190776 : List Nat := [2, 1, 2, 1, 3, 1, 3, 2, 2, 3, 3]
def baseStart_190776 : Nat := 118140960795 + 190776 * 2 ^ 59
def prefixEnd_190776 : Nat := 4983230072969 + 3 ^ 40 * 190776 * 2
def baseEnd_190776 : Nat := 97959785342250821722643

theorem tailTrace_190776 : CollatzResearch.WordTrace tailWord_190776 prefixEnd_190776 97959785342250821722643 := by
  unfold tailWord_190776
  simp only [CollatzResearch.WordTrace]
  refine ⟨3479086178429304395964091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4638781571239072527952121 3479086178429304395964091)
  ·
    refine ⟨5218629267643956593946137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3479086178429304395964091 5218629267643956593946137)
    ·
      refine ⟨3913971950732967445459603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5218629267643956593946137 3913971950732967445459603)
      ·
        refine ⟨5870957926099451168189405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3913971950732967445459603 5870957926099451168189405)
        ·
          refine ⟨2201609222287294188071027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5870957926099451168189405 2201609222287294188071027)
          ·
            refine ⟨3302413833430941282106541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2201609222287294188071027 3302413833430941282106541)
            ·
              refine ⟨1238405187536602980789953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3302413833430941282106541 1238405187536602980789953)
              ·
                refine ⟨928803890652452235592465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1238405187536602980789953 928803890652452235592465)
                ·
                  refine ⟨696602917989339176694349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 928803890652452235592465 696602917989339176694349)
                  ·
                    refine ⟨261226094246002191260381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 696602917989339176694349 261226094246002191260381)
                    ·
                      refine ⟨97959785342250821722643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 261226094246002191260381 97959785342250821722643)
                      ·
                        rfl

theorem cell23_190776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 2, 2, 3, 3].length) (baseStart_190776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_190776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_190776 prefixEnd_190776 := by exact prefixLift 190776
  have htrace : WordTrace (prefixWord ++ tailWord_190776) baseStart_190776 baseEnd_190776 := by
    simpa [prefixWord, tailWord_190776, baseEnd_190776] using wordTrace_append hprefix tailTrace_190776
  have hstable : (prefixWord ++ tailWord_190776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190776).length < 2 ^ (prefixWord ++ tailWord_190776).sum := by decide
  have hdescent : baseEnd_190776 < baseStart_190776 := by decide
  rcases family_descends (prefixWord ++ tailWord_190776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190777 : List Nat := [1, 2, 1, 6, 1, 1, 3, 2, 2, 2, 2]
def baseStart_190777 : Nat := 118140960795 + 190777 * 2 ^ 59
def prefixEnd_190777 : Nat := 4983230072969 + 3 ^ 40 * 190777 * 2
def baseEnd_190777 : Nat := 97960298822905317810139

theorem tailTrace_190777 : CollatzResearch.WordTrace tailWord_190777 prefixEnd_190777 97960298822905317810139 := by
  unfold tailWord_190777
  simp only [CollatzResearch.WordTrace]
  refine ⟨6958208829854985962714585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4638805886569990641809723 6958208829854985962714585)
  ·
    refine ⟨5218656622391239472035939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6958208829854985962714585 5218656622391239472035939)
    ·
      refine ⟨7827984933586859208053909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5218656622391239472035939 7827984933586859208053909)
      ·
        refine ⟨366936793761884025377527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 7827984933586859208053909 366936793761884025377527)
        ·
          refine ⟨550405190642826038066291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 366936793761884025377527 550405190642826038066291)
          ·
            refine ⟨825607785964239057099437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 550405190642826038066291 825607785964239057099437)
            ·
              refine ⟨309602919736589646412289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 825607785964239057099437 309602919736589646412289)
              ·
                refine ⟨232202189802442234809217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 309602919736589646412289 232202189802442234809217)
                ·
                  refine ⟨174151642351831676106913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 232202189802442234809217 174151642351831676106913)
                  ·
                    refine ⟨130613731763873757080185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 174151642351831676106913 130613731763873757080185)
                    ·
                      refine ⟨97960298822905317810139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 130613731763873757080185 97960298822905317810139)
                      ·
                        rfl

theorem cell23_190777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 3, 2, 2, 2, 2].length) (baseStart_190777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_190777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_190777 prefixEnd_190777 := by exact prefixLift 190777
  have htrace : WordTrace (prefixWord ++ tailWord_190777) baseStart_190777 baseEnd_190777 := by
    simpa [prefixWord, tailWord_190777, baseEnd_190777] using wordTrace_append hprefix tailTrace_190777
  have hstable : (prefixWord ++ tailWord_190777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190777).length < 2 ^ (prefixWord ++ tailWord_190777).sum := by decide
  have hdescent : baseEnd_190777 < baseStart_190777 := by decide
  rcases family_descends (prefixWord ++ tailWord_190777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190809 : List Nat := [1, 2, 1, 2, 2, 2, 1, 1, 1, 10]
def baseStart_190809 : Nat := 118140960795 + 190809 * 2 ^ 59
def prefixEnd_190809 : Nat := 4983230072969 + 3 ^ 40 * 190809 * 2
def baseEnd_190809 : Nat := 32658910067949730869997

theorem tailTrace_190809 : CollatzResearch.WordTrace tailWord_190809 prefixEnd_190809 32658910067949730869997 := by
  unfold tailWord_190809
  simp only [CollatzResearch.WordTrace]
  refine ⟨6959375965739055427879481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4639583977159370285252987 6959375965739055427879481)
  ·
    refine ⟨5219531974304291570909611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6959375965739055427879481 5219531974304291570909611)
    ·
      refine ⟨7829297961456437356364417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5219531974304291570909611 7829297961456437356364417)
      ·
        refine ⟨5871973471092328017273313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7829297961456437356364417 5871973471092328017273313)
        ·
          refine ⟨4403980103319246012954985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5871973471092328017273313 4403980103319246012954985)
          ·
            refine ⟨3302985077489434509716239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4403980103319246012954985 3302985077489434509716239)
            ·
              refine ⟨4954477616234151764574359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3302985077489434509716239 4954477616234151764574359)
              ·
                refine ⟨7431716424351227646861539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4954477616234151764574359 7431716424351227646861539)
                ·
                  refine ⟨11147574636526841470292309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7431716424351227646861539 11147574636526841470292309)
                  ·
                    refine ⟨32658910067949730869997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 11147574636526841470292309 32658910067949730869997)
                    ·
                      rfl

theorem cell23_190809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 10].length) (baseStart_190809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_190809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_190809 prefixEnd_190809 := by exact prefixLift 190809
  have htrace : WordTrace (prefixWord ++ tailWord_190809) baseStart_190809 baseEnd_190809 := by
    simpa [prefixWord, tailWord_190809, baseEnd_190809] using wordTrace_append hprefix tailTrace_190809
  have hstable : (prefixWord ++ tailWord_190809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190809).length < 2 ^ (prefixWord ++ tailWord_190809).sum := by decide
  have hdescent : baseEnd_190809 < baseStart_190809 := by decide
  rcases family_descends (prefixWord ++ tailWord_190809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190814 : List Nat := [4, 4, 2, 1, 1, 1, 1, 1, 2, 1, 5]
def baseStart_190814 : Nat := 118140960795 + 190814 * 2 ^ 59
def prefixEnd_190814 : Nat := 4983230072969 + 3 ^ 40 * 190814 * 2
def baseEnd_190814 : Nat := 97979297607121673047469

theorem tailTrace_190814 : CollatzResearch.WordTrace tailWord_190814 prefixEnd_190814 97979297607121673047469 := by
  unfold tailWord_190814
  simp only [CollatzResearch.WordTrace]
  refine ⟨869944791340117660226437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4639705553813960854540997 869944791340117660226437)
  ·
    refine ⟨163114648376272061292457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 869944791340117660226437 163114648376272061292457)
    ·
      refine ⟨122335986282204045969343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 163114648376272061292457 122335986282204045969343)
      ·
        refine ⟨183503979423306068954015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122335986282204045969343 183503979423306068954015)
        ·
          refine ⟨275255969134959103431023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183503979423306068954015 275255969134959103431023)
          ·
            refine ⟨412883953702438655146535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 275255969134959103431023 412883953702438655146535)
            ·
              refine ⟨619325930553657982719803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 412883953702438655146535 619325930553657982719803)
              ·
                refine ⟨928988895830486974079705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 619325930553657982719803 928988895830486974079705)
                ·
                  refine ⟨696741671872865230559779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 928988895830486974079705 696741671872865230559779)
                  ·
                    refine ⟨1045112507809297845839669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 696741671872865230559779 1045112507809297845839669)
                    ·
                      refine ⟨97979297607121673047469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1045112507809297845839669 97979297607121673047469)
                      ·
                        rfl

theorem cell23_190814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_190814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_190814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_190814 prefixEnd_190814 := by exact prefixLift 190814
  have htrace : WordTrace (prefixWord ++ tailWord_190814) baseStart_190814 baseEnd_190814 := by
    simpa [prefixWord, tailWord_190814, baseEnd_190814] using wordTrace_append hprefix tailTrace_190814
  have hstable : (prefixWord ++ tailWord_190814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190814).length < 2 ^ (prefixWord ++ tailWord_190814).sum := by decide
  have hdescent : baseEnd_190814 < baseStart_190814 := by decide
  rcases family_descends (prefixWord ++ tailWord_190814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190843 : List Nat := [1, 1, 1, 1, 1, 7, 3, 1, 3, 4]
def baseStart_190843 : Nat := 118140960795 + 190843 * 2 ^ 59
def prefixEnd_190843 : Nat := 4983230072969 + 3 ^ 40 * 190843 * 2
def baseEnd_190843 : Nat := 32664729515367353194945

theorem tailTrace_190843 : CollatzResearch.WordTrace tailWord_190843 prefixEnd_190843 32664729515367353194945 := by
  unfold tailWord_190843
  simp only [CollatzResearch.WordTrace]
  refine ⟨6960616047615879234617183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4640410698410586156411455 6960616047615879234617183)
  ·
    refine ⟨10440924071423818851925775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6960616047615879234617183 10440924071423818851925775)
    ·
      refine ⟨15661386107135728277888663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10440924071423818851925775 15661386107135728277888663)
      ·
        refine ⟨23492079160703592416832995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15661386107135728277888663 23492079160703592416832995)
        ·
          refine ⟨35238118741055388625249493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23492079160703592416832995 35238118741055388625249493)
          ·
            refine ⟨825893407993485670904285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 35238118741055388625249493 825893407993485670904285)
            ·
              refine ⟨309710027997557126589107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 825893407993485670904285 309710027997557126589107)
              ·
                refine ⟨464565041996335689883661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 309710027997557126589107 464565041996335689883661)
                ·
                  refine ⟨174211890748625883706373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 464565041996335689883661 174211890748625883706373)
                  ·
                    refine ⟨32664729515367353194945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 174211890748625883706373 32664729515367353194945)
                    ·
                      rfl

theorem cell23_190843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 3, 1, 3, 4].length) (baseStart_190843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_190843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_190843 prefixEnd_190843 := by exact prefixLift 190843
  have htrace : WordTrace (prefixWord ++ tailWord_190843) baseStart_190843 baseEnd_190843 := by
    simpa [prefixWord, tailWord_190843, baseEnd_190843] using wordTrace_append hprefix tailTrace_190843
  have hstable : (prefixWord ++ tailWord_190843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190843).length < 2 ^ (prefixWord ++ tailWord_190843).sum := by decide
  have hdescent : baseEnd_190843 < baseStart_190843 := by decide
  rcases family_descends (prefixWord ++ tailWord_190843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190910 : List Nat := [4, 2, 1, 1, 1, 1, 2, 2, 4, 3, 2]
def baseStart_190910 : Nat := 118140960795 + 190910 * 2 ^ 59
def prefixEnd_190910 : Nat := 4983230072969 + 3 ^ 40 * 190910 * 2
def baseEnd_190910 : Nat := 98028591749953297447027

theorem tailTrace_190910 : CollatzResearch.WordTrace tailWord_190910 prefixEnd_190910 98028591749953297447027 := by
  unfold tailWord_190910
  simp only [CollatzResearch.WordTrace]
  refine ⟨870382467296643709663273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4642039825582099784870789 870382467296643709663273)
  ·
    refine ⟨652786850472482782247455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 870382467296643709663273 652786850472482782247455)
    ·
      refine ⟨979180275708724173371183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 652786850472482782247455 979180275708724173371183)
      ·
        refine ⟨1468770413563086260056775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 979180275708724173371183 1468770413563086260056775)
        ·
          refine ⟨2203155620344629390085163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1468770413563086260056775 2203155620344629390085163)
          ·
            refine ⟨3304733430516944085127745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2203155620344629390085163 3304733430516944085127745)
            ·
              refine ⟨2478550072887708063845809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3304733430516944085127745 2478550072887708063845809)
              ·
                refine ⟨1858912554665781047884357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2478550072887708063845809 1858912554665781047884357)
                ·
                  refine ⟨348546103999833946478317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1858912554665781047884357 348546103999833946478317)
                  ·
                    refine ⟨130704788999937729929369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 348546103999833946478317 130704788999937729929369)
                    ·
                      refine ⟨98028591749953297447027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 130704788999937729929369 98028591749953297447027)
                      ·
                        rfl

theorem cell23_190910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 2, 4, 3, 2].length) (baseStart_190910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_190910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_190910 prefixEnd_190910 := by exact prefixLift 190910
  have htrace : WordTrace (prefixWord ++ tailWord_190910) baseStart_190910 baseEnd_190910 := by
    simpa [prefixWord, tailWord_190910, baseEnd_190910] using wordTrace_append hprefix tailTrace_190910
  have hstable : (prefixWord ++ tailWord_190910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190910).length < 2 ^ (prefixWord ++ tailWord_190910).sum := by decide
  have hdescent : baseEnd_190910 < baseStart_190910 := by decide
  rcases family_descends (prefixWord ++ tailWord_190910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190923 : List Nat := [1, 1, 1, 1, 3, 3, 1, 6, 1, 1, 4]
def baseStart_190923 : Nat := 118140960795 + 190923 * 2 ^ 59
def prefixEnd_190923 : Nat := 4983230072969 + 3 ^ 40 * 190923 * 2
def baseEnd_190923 : Nat := 98035266998461746584467

theorem tailTrace_190923 : CollatzResearch.WordTrace tailWord_190923 prefixEnd_190923 98035266998461746584467 := by
  unfold tailWord_190923
  simp only [CollatzResearch.WordTrace]
  refine ⟨6963533887326052897529423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4642355924884035265019615 6963533887326052897529423)
  ·
    refine ⟨10445300830989079346294135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6963533887326052897529423 10445300830989079346294135)
    ·
      refine ⟨15667951246483619019441203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10445300830989079346294135 15667951246483619019441203)
      ·
        refine ⟨23501926869725428529161805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15667951246483619019441203 23501926869725428529161805)
        ·
          refine ⟨8813222576147035698435677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23501926869725428529161805 8813222576147035698435677)
          ·
            refine ⟨3304958466055138386913379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8813222576147035698435677 3304958466055138386913379)
            ·
              refine ⟨4957437699082707580370069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3304958466055138386913379 4957437699082707580370069)
              ·
                refine ⟨232379892144501917829847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4957437699082707580370069 232379892144501917829847)
                ·
                  refine ⟨348569838216752876744771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 232379892144501917829847 348569838216752876744771)
                  ·
                    refine ⟨522854757325129315117157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 348569838216752876744771 522854757325129315117157)
                    ·
                      refine ⟨98035266998461746584467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 522854757325129315117157 98035266998461746584467)
                      ·
                        rfl

theorem cell23_190923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 6, 1, 1, 4].length) (baseStart_190923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_190923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_190923 prefixEnd_190923 := by exact prefixLift 190923
  have htrace : WordTrace (prefixWord ++ tailWord_190923) baseStart_190923 baseEnd_190923 := by
    simpa [prefixWord, tailWord_190923, baseEnd_190923] using wordTrace_append hprefix tailTrace_190923
  have hstable : (prefixWord ++ tailWord_190923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190923).length < 2 ^ (prefixWord ++ tailWord_190923).sum := by decide
  have hdescent : baseEnd_190923 < baseStart_190923 := by decide
  rcases family_descends (prefixWord ++ tailWord_190923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190933 : List Nat := [1, 3, 2, 3, 1, 2, 2, 2, 1, 6]
def baseStart_190933 : Nat := 118140960795 + 190933 * 2 ^ 59
def prefixEnd_190933 : Nat := 4983230072969 + 3 ^ 40 * 190933 * 2
def baseEnd_190933 : Nat := 32680133935002235819807

theorem tailTrace_190933 : CollatzResearch.WordTrace tailWord_190933 prefixEnd_190933 32680133935002235819807 := by
  unfold tailWord_190933
  simp only [CollatzResearch.WordTrace]
  refine ⟨6963898617289824605393453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4642599078193216403595635 6963898617289824605393453)
  ·
    refine ⟨2611461981483684227022545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6963898617289824605393453 2611461981483684227022545)
    ·
      refine ⟨1958596486112763170266909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2611461981483684227022545 1958596486112763170266909)
      ·
        refine ⟨734473682292286188850091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1958596486112763170266909 734473682292286188850091)
        ·
          refine ⟨1101710523438429283275137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 734473682292286188850091 1101710523438429283275137)
          ·
            refine ⟨826282892578821962456353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1101710523438429283275137 826282892578821962456353)
            ·
              refine ⟨619712169434116471842265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 826282892578821962456353 619712169434116471842265)
              ·
                refine ⟨464784127075587353881699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 619712169434116471842265 464784127075587353881699)
                ·
                  refine ⟨697176190613381030822549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 464784127075587353881699 697176190613381030822549)
                  ·
                    refine ⟨32680133935002235819807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 697176190613381030822549 32680133935002235819807)
                    ·
                      rfl

theorem cell23_190933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 2, 1, 6].length) (baseStart_190933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_190933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_190933 prefixEnd_190933 := by exact prefixLift 190933
  have htrace : WordTrace (prefixWord ++ tailWord_190933) baseStart_190933 baseEnd_190933 := by
    simpa [prefixWord, tailWord_190933, baseEnd_190933] using wordTrace_append hprefix tailTrace_190933
  have hstable : (prefixWord ++ tailWord_190933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190933).length < 2 ^ (prefixWord ++ tailWord_190933).sum := by decide
  have hdescent : baseEnd_190933 < baseStart_190933 := by decide
  rcases family_descends (prefixWord ++ tailWord_190933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190936 : List Nat := [2, 1, 2, 2, 2, 1, 1, 2, 3, 1, 6]
def baseStart_190936 : Nat := 118140960795 + 190936 * 2 ^ 59
def prefixEnd_190936 : Nat := 4983230072969 + 3 ^ 40 * 190936 * 2
def baseEnd_190936 : Nat := 98041942246970195721907

theorem tailTrace_190936 : CollatzResearch.WordTrace tailWord_190936 prefixEnd_190936 98041942246970195721907 := by
  unfold tailWord_190936
  simp only [CollatzResearch.WordTrace]
  refine ⟨3482004018139478058876331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4642672024185970745168441 3482004018139478058876331)
  ·
    refine ⟨5223006027209217088314497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3482004018139478058876331 5223006027209217088314497)
    ·
      refine ⟨3917254520406912816235873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5223006027209217088314497 3917254520406912816235873)
      ·
        refine ⟨2937940890305184612176905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3917254520406912816235873 2937940890305184612176905)
        ·
          refine ⟨2203455667728888459132679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2937940890305184612176905 2203455667728888459132679)
          ·
            refine ⟨3305183501593332688699019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2203455667728888459132679 3305183501593332688699019)
            ·
              refine ⟨4957775252389999033048529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3305183501593332688699019 4957775252389999033048529)
              ·
                refine ⟨3718331439292499274786397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4957775252389999033048529 3718331439292499274786397)
                ·
                  refine ⟨1394374289734687228044899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3718331439292499274786397 1394374289734687228044899)
                  ·
                    refine ⟨2091561434602030842067349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1394374289734687228044899 2091561434602030842067349)
                    ·
                      refine ⟨98041942246970195721907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2091561434602030842067349 98041942246970195721907)
                      ·
                        rfl

theorem cell23_190936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 3, 1, 6].length) (baseStart_190936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_190936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_190936 prefixEnd_190936 := by exact prefixLift 190936
  have htrace : WordTrace (prefixWord ++ tailWord_190936) baseStart_190936 baseEnd_190936 := by
    simpa [prefixWord, tailWord_190936, baseEnd_190936] using wordTrace_append hprefix tailTrace_190936
  have hstable : (prefixWord ++ tailWord_190936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190936).length < 2 ^ (prefixWord ++ tailWord_190936).sum := by decide
  have hdescent : baseEnd_190936 < baseStart_190936 := by decide
  rcases family_descends (prefixWord ++ tailWord_190936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190977 : List Nat := [1, 2, 4, 1, 3, 2, 2, 2, 1, 2, 3]
def baseStart_190977 : Nat := 118140960795 + 190977 * 2 ^ 59
def prefixEnd_190977 : Nat := 4983230072969 + 3 ^ 40 * 190977 * 2
def baseEnd_190977 : Nat := 98062994953804535309219

theorem tailTrace_190977 : CollatzResearch.WordTrace tailWord_190977 prefixEnd_190977 98062994953804535309219 := by
  unfold tailWord_190977
  simp only [CollatzResearch.WordTrace]
  refine ⟨6965503429130420119995185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4643668952753613413330123 6965503429130420119995185)
  ·
    refine ⟨5224127571847815089996389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6965503429130420119995185 5224127571847815089996389)
    ·
      refine ⟨979523919721465329374323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5224127571847815089996389 979523919721465329374323)
      ·
        refine ⟨1469285879582197994061485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 979523919721465329374323 1469285879582197994061485)
        ·
          refine ⟨550982204843324247773057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1469285879582197994061485 550982204843324247773057)
          ·
            refine ⟨413236653632493185829793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 550982204843324247773057 413236653632493185829793)
            ·
              refine ⟨309927490224369889372345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 413236653632493185829793 309927490224369889372345)
              ·
                refine ⟨232445617668277417029259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 309927490224369889372345 232445617668277417029259)
                ·
                  refine ⟨348668426502416125543889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 232445617668277417029259 348668426502416125543889)
                  ·
                    refine ⟨261501319876812094157917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 348668426502416125543889 261501319876812094157917)
                    ·
                      refine ⟨98062994953804535309219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 261501319876812094157917 98062994953804535309219)
                      ·
                        rfl

theorem cell23_190977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 2, 2, 1, 2, 3].length) (baseStart_190977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_190977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_190977 prefixEnd_190977 := by exact prefixLift 190977
  have htrace : WordTrace (prefixWord ++ tailWord_190977) baseStart_190977 baseEnd_190977 := by
    simpa [prefixWord, tailWord_190977, baseEnd_190977] using wordTrace_append hprefix tailTrace_190977
  have hstable : (prefixWord ++ tailWord_190977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190977).length < 2 ^ (prefixWord ++ tailWord_190977).sum := by decide
  have hdescent : baseEnd_190977 < baseStart_190977 := by decide
  rcases family_descends (prefixWord ++ tailWord_190977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_190980 : List Nat := [2, 3, 2, 3, 1, 1, 4, 7]
def baseStart_190980 : Nat := 118140960795 + 190980 * 2 ^ 59
def prefixEnd_190980 : Nat := 4983230072969 + 3 ^ 40 * 190980 * 2
def baseEnd_190980 : Nat := 3632019829472889761915

theorem tailTrace_190980 : CollatzResearch.WordTrace tailWord_190980 prefixEnd_190980 3632019829472889761915 := by
  unfold tailWord_190980
  simp only [CollatzResearch.WordTrace]
  refine ⟨3482806424059775816177197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4643741898746367754902929 3482806424059775816177197)
  ·
    refine ⟨1306052409022415931066449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3482806424059775816177197 1306052409022415931066449)
    ·
      refine ⟨979539306766811948299837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1306052409022415931066449 979539306766811948299837)
      ·
        refine ⟨367327240037554480612439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 979539306766811948299837 367327240037554480612439)
        ·
          refine ⟨550990860056331720918659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 367327240037554480612439 550990860056331720918659)
          ·
            refine ⟨826486290084497581377989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 550990860056331720918659 826486290084497581377989)
            ·
              refine ⟨154966179390843296508373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 826486290084497581377989 154966179390843296508373)
              ·
                refine ⟨3632019829472889761915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 154966179390843296508373 3632019829472889761915)
                ·
                  rfl

theorem cell23_190980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 4, 7].length) (baseStart_190980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_190980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_190980 prefixEnd_190980 := by exact prefixLift 190980
  have htrace : WordTrace (prefixWord ++ tailWord_190980) baseStart_190980 baseEnd_190980 := by
    simpa [prefixWord, tailWord_190980, baseEnd_190980] using wordTrace_append hprefix tailTrace_190980
  have hstable : (prefixWord ++ tailWord_190980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_190980).length < 2 ^ (prefixWord ++ tailWord_190980).sum := by decide
  have hdescent : baseEnd_190980 < baseStart_190980 := by decide
  rcases family_descends (prefixWord ++ tailWord_190980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191008 : List Nat := [2, 1, 1, 6, 2, 1, 3, 2, 1, 2, 2]
def baseStart_191008 : Nat := 118140960795 + 191008 * 2 ^ 59
def prefixEnd_191008 : Nat := 4983230072969 + 3 ^ 40 * 191008 * 2
def baseEnd_191008 : Nat := 98078912854093914021577

theorem tailTrace_191008 : CollatzResearch.WordTrace tailWord_191008 prefixEnd_191008 98078912854093914021577 := by
  unfold tailWord_191008
  simp only [CollatzResearch.WordTrace]
  refine ⟨3483317046009056207186839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4644422728012074942915785 3483317046009056207186839)
  ·
    refine ⟨5224975569013584310780259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3483317046009056207186839 5224975569013584310780259)
    ·
      refine ⟨7837463353520376466170389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5224975569013584310780259 7837463353520376466170389)
      ·
        refine ⟨367381094696267646851737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 7837463353520376466170389 367381094696267646851737)
        ·
          refine ⟨275535821022200735138803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 367381094696267646851737 275535821022200735138803)
          ·
            refine ⟨413303731533301102708205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 275535821022200735138803 413303731533301102708205)
            ·
              refine ⟨154988899324987913515577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 413303731533301102708205 154988899324987913515577)
              ·
                refine ⟨116241674493740935136683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 154988899324987913515577 116241674493740935136683)
                ·
                  refine ⟨174362511740611402705025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 116241674493740935136683 174362511740611402705025)
                  ·
                    refine ⟨130771883805458552028769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 174362511740611402705025 130771883805458552028769)
                    ·
                      refine ⟨98078912854093914021577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 130771883805458552028769 98078912854093914021577)
                      ·
                        rfl

theorem cell23_191008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 3, 2, 1, 2, 2].length) (baseStart_191008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_191008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_191008 prefixEnd_191008 := by exact prefixLift 191008
  have htrace : WordTrace (prefixWord ++ tailWord_191008) baseStart_191008 baseEnd_191008 := by
    simpa [prefixWord, tailWord_191008, baseEnd_191008] using wordTrace_append hprefix tailTrace_191008
  have hstable : (prefixWord ++ tailWord_191008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191008).length < 2 ^ (prefixWord ++ tailWord_191008).sum := by decide
  have hdescent : baseEnd_191008 < baseStart_191008 := by decide
  rcases family_descends (prefixWord ++ tailWord_191008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191028 : List Nat := [2, 5, 1, 3, 2, 1, 1, 2, 1, 2, 3]
def baseStart_191028 : Nat := 118140960795 + 191028 * 2 ^ 59
def prefixEnd_191028 : Nat := 4983230072969 + 3 ^ 40 * 191028 * 2
def baseEnd_191028 : Nat := 98089182467183835771485

theorem tailTrace_191028 : CollatzResearch.WordTrace tailWord_191028 prefixEnd_191028 98089182467183835771485 := by
  unfold tailWord_191028
  simp only [CollatzResearch.WordTrace]
  refine ⟨3483681775972827915050869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4644909034630437220067825 3483681775972827915050869)
  ·
    refine ⟨326595166497452617036019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3483681775972827915050869 326595166497452617036019)
    ·
      refine ⟨489892749746178925554029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 326595166497452617036019 489892749746178925554029)
      ·
        refine ⟨183709781154817097082761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 489892749746178925554029 183709781154817097082761)
        ·
          refine ⟨137782335866112822812071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183709781154817097082761 137782335866112822812071)
          ·
            refine ⟨206673503799169234218107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137782335866112822812071 206673503799169234218107)
            ·
              refine ⟨310010255698753851327161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 206673503799169234218107 310010255698753851327161)
              ·
                refine ⟨232507691774065388495371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 310010255698753851327161 232507691774065388495371)
                ·
                  refine ⟨348761537661098082743057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 232507691774065388495371 348761537661098082743057)
                  ·
                    refine ⟨261571153245823562057293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 348761537661098082743057 261571153245823562057293)
                    ·
                      refine ⟨98089182467183835771485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 261571153245823562057293 98089182467183835771485)
                      ·
                        rfl

theorem cell23_191028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_191028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_191028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_191028 prefixEnd_191028 := by exact prefixLift 191028
  have htrace : WordTrace (prefixWord ++ tailWord_191028) baseStart_191028 baseEnd_191028 := by
    simpa [prefixWord, tailWord_191028, baseEnd_191028] using wordTrace_append hprefix tailTrace_191028
  have hstable : (prefixWord ++ tailWord_191028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191028).length < 2 ^ (prefixWord ++ tailWord_191028).sum := by decide
  have hdescent : baseEnd_191028 < baseStart_191028 := by decide
  rcases family_descends (prefixWord ++ tailWord_191028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191033 : List Nat := [1, 2, 1, 5, 1, 1, 1, 1, 4, 1, 5]
def baseStart_191033 : Nat := 118140960795 + 191033 * 2 ^ 59
def prefixEnd_191033 : Nat := 4983230072969 + 3 ^ 40 * 191033 * 2
def baseEnd_191033 : Nat := 98091749870456316208961

theorem tailTrace_191033 : CollatzResearch.WordTrace tailWord_191033 prefixEnd_191033 98091749870456316208961 := by
  unfold tailWord_191033
  simp only [CollatzResearch.WordTrace]
  refine ⟨6967545916927541684033753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4645030611285027789355835 6967545916927541684033753)
  ·
    refine ⟨5225659437695656263025315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6967545916927541684033753 5225659437695656263025315)
    ·
      refine ⟨7838489156543484394537973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5225659437695656263025315 7838489156543484394537973)
      ·
        refine ⟨734858358425951661987935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7838489156543484394537973 734858358425951661987935)
        ·
          refine ⟨1102287537638927492981903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 734858358425951661987935 1102287537638927492981903)
          ·
            refine ⟨1653431306458391239472855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1102287537638927492981903 1653431306458391239472855)
            ·
              refine ⟨2480146959687586859209283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1653431306458391239472855 2480146959687586859209283)
              ·
                refine ⟨3720220439531380288813925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2480146959687586859209283 3720220439531380288813925)
                ·
                  refine ⟨697541332412133804152611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3720220439531380288813925 697541332412133804152611)
                  ·
                    refine ⟨1046311998618200706228917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 697541332412133804152611 1046311998618200706228917)
                    ·
                      refine ⟨98091749870456316208961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1046311998618200706228917 98091749870456316208961)
                      ·
                        rfl

theorem cell23_191033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_191033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_191033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_191033 prefixEnd_191033 := by exact prefixLift 191033
  have htrace : WordTrace (prefixWord ++ tailWord_191033) baseStart_191033 baseEnd_191033 := by
    simpa [prefixWord, tailWord_191033, baseEnd_191033] using wordTrace_append hprefix tailTrace_191033
  have hstable : (prefixWord ++ tailWord_191033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191033).length < 2 ^ (prefixWord ++ tailWord_191033).sum := by decide
  have hdescent : baseEnd_191033 < baseStart_191033 := by decide
  rcases family_descends (prefixWord ++ tailWord_191033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191034 : List Nat := [3, 1, 1, 1, 3, 5, 1, 2, 1, 3, 2]
def baseStart_191034 : Nat := 118140960795 + 191034 * 2 ^ 59
def prefixEnd_191034 : Nat := 4983230072969 + 3 ^ 40 * 191034 * 2
def baseEnd_191034 : Nat := 98092263351110812296457

theorem tailTrace_191034 : CollatzResearch.WordTrace tailWord_191034 prefixEnd_191034 98092263351110812296457 := by
  unfold tailWord_191034
  simp only [CollatzResearch.WordTrace]
  refine ⟨1741895597480979713705039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4645054926615945903213437 1741895597480979713705039)
  ·
    refine ⟨2612843396221469570557559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1741895597480979713705039 2612843396221469570557559)
    ·
      refine ⟨3919265094332204355836339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2612843396221469570557559 3919265094332204355836339)
      ·
        refine ⟨5878897641498306533754509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3919265094332204355836339 5878897641498306533754509)
        ·
          refine ⟨2204586615561864950157941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5878897641498306533754509 2204586615561864950157941)
          ·
            refine ⟨206679995208924839077307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2204586615561864950157941 206679995208924839077307)
            ·
              refine ⟨310019992813387258615961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 206679995208924839077307 310019992813387258615961)
              ·
                refine ⟨232514994610040443961971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 310019992813387258615961 232514994610040443961971)
                ·
                  refine ⟨348772491915060665942957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 232514994610040443961971 348772491915060665942957)
                  ·
                    refine ⟨130789684468147749728609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 348772491915060665942957 130789684468147749728609)
                    ·
                      refine ⟨98092263351110812296457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 130789684468147749728609 98092263351110812296457)
                      ·
                        rfl

theorem cell23_191034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 1, 2, 1, 3, 2].length) (baseStart_191034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_191034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_191034 prefixEnd_191034 := by exact prefixLift 191034
  have htrace : WordTrace (prefixWord ++ tailWord_191034) baseStart_191034 baseEnd_191034 := by
    simpa [prefixWord, tailWord_191034, baseEnd_191034] using wordTrace_append hprefix tailTrace_191034
  have hstable : (prefixWord ++ tailWord_191034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191034).length < 2 ^ (prefixWord ++ tailWord_191034).sum := by decide
  have hdescent : baseEnd_191034 < baseStart_191034 := by decide
  rcases family_descends (prefixWord ++ tailWord_191034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191047 : List Nat := [1, 1, 4, 1, 4, 2, 1, 2, 1, 4, 2]
def baseStart_191047 : Nat := 118140960795 + 191047 * 2 ^ 59
def prefixEnd_191047 : Nat := 4983230072969 + 3 ^ 40 * 191047 * 2
def baseEnd_191047 : Nat := 98098938599619261433897

theorem tailTrace_191047 : CollatzResearch.WordTrace tailWord_191047 prefixEnd_191047 98098938599619261433897 := by
  unfold tailWord_191047
  simp only [CollatzResearch.WordTrace]
  refine ⟨6968056538876822075043395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4645371025917881383362263 6968056538876822075043395)
  ·
    refine ⟨10452084808315233112565093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6968056538876822075043395 10452084808315233112565093)
    ·
      refine ⟨1959765901559106208605955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10452084808315233112565093 1959765901559106208605955)
      ·
        refine ⟨2939648852338659312908933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1959765901559106208605955 2939648852338659312908933)
        ·
          refine ⟨551184159813498621170425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2939648852338659312908933 551184159813498621170425)
          ·
            refine ⟨413388119860123965877819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 551184159813498621170425 413388119860123965877819)
            ·
              refine ⟨620082179790185948816729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 413388119860123965877819 620082179790185948816729)
              ·
                refine ⟨465061634842639461612547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 620082179790185948816729 465061634842639461612547)
                ·
                  refine ⟨697592452263959192418821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 465061634842639461612547 697592452263959192418821)
                  ·
                    refine ⟨130798584799492348578529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 697592452263959192418821 130798584799492348578529)
                    ·
                      refine ⟨98098938599619261433897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 130798584799492348578529 98098938599619261433897)
                      ·
                        rfl

theorem cell23_191047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 2, 1, 4, 2].length) (baseStart_191047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_191047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_191047 prefixEnd_191047 := by exact prefixLift 191047
  have htrace : WordTrace (prefixWord ++ tailWord_191047) baseStart_191047 baseEnd_191047 := by
    simpa [prefixWord, tailWord_191047, baseEnd_191047] using wordTrace_append hprefix tailTrace_191047
  have hstable : (prefixWord ++ tailWord_191047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191047).length < 2 ^ (prefixWord ++ tailWord_191047).sum := by decide
  have hdescent : baseEnd_191047 < baseStart_191047 := by decide
  rcases family_descends (prefixWord ++ tailWord_191047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191100 : List Nat := [2, 2, 2, 1, 1, 2, 5, 1, 2, 5]
def baseStart_191100 : Nat := 118140960795 + 191100 * 2 ^ 59
def prefixEnd_191100 : Nat := 4983230072969 + 3 ^ 40 * 191100 * 2
def baseEnd_191100 : Nat := 32708717691435851357051

theorem tailTrace_191100 : CollatzResearch.WordTrace tailWord_191100 prefixEnd_191100 32708717691435851357051 := by
  unfold tailWord_191100
  simp only [CollatzResearch.WordTrace]
  refine ⟨3484994803842406063361377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4646659738456541417815169 3484994803842406063361377)
  ·
    refine ⟨2613746102881804547521033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3484994803842406063361377 2613746102881804547521033)
    ·
      refine ⟨1960309577161353410640775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2613746102881804547521033 1960309577161353410640775)
      ·
        refine ⟨2940464365742030115961163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1960309577161353410640775 2940464365742030115961163)
        ·
          refine ⟨4410696548613045173941745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2940464365742030115961163 4410696548613045173941745)
          ·
            refine ⟨3308022411459783880456309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4410696548613045173941745 3308022411459783880456309)
            ·
              refine ⟨310127101074354738792779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3308022411459783880456309 310127101074354738792779)
              ·
                refine ⟨465190651611532108189169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 310127101074354738792779 465190651611532108189169)
                ·
                  refine ⟨348892988708649081141877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 465190651611532108189169 348892988708649081141877)
                  ·
                    refine ⟨32708717691435851357051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 348892988708649081141877 32708717691435851357051)
                    ·
                      rfl

theorem cell23_191100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 5, 1, 2, 5].length) (baseStart_191100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_191100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_191100 prefixEnd_191100 := by exact prefixLift 191100
  have htrace : WordTrace (prefixWord ++ tailWord_191100) baseStart_191100 baseEnd_191100 := by
    simpa [prefixWord, tailWord_191100, baseEnd_191100] using wordTrace_append hprefix tailTrace_191100
  have hstable : (prefixWord ++ tailWord_191100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191100).length < 2 ^ (prefixWord ++ tailWord_191100).sum := by decide
  have hdescent : baseEnd_191100 < baseStart_191100 := by decide
  rcases family_descends (prefixWord ++ tailWord_191100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191140 : List Nat := [2, 3, 1, 2, 2, 1, 1, 1, 3, 4, 3]
def baseStart_191140 : Nat := 118140960795 + 191140 * 2 ^ 59
def prefixEnd_191140 : Nat := 4983230072969 + 3 ^ 40 * 191140 * 2
def baseEnd_191140 : Nat := 98146692300487397570969

theorem tailTrace_191140 : CollatzResearch.WordTrace tailWord_191140 prefixEnd_191140 98146692300487397570969 := by
  unfold tailWord_191140
  simp only [CollatzResearch.WordTrace]
  refine ⟨3485724263769949479089437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4647632351693265972119249 3485724263769949479089437)
  ·
    refine ⟨1307146598913731054658539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3485724263769949479089437 1307146598913731054658539)
    ·
      refine ⟨1960719898370596581987809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1307146598913731054658539 1960719898370596581987809)
      ·
        refine ⟨1470539923777947436490857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1960719898370596581987809 1470539923777947436490857)
        ·
          refine ⟨1102904942833460577368143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1470539923777947436490857 1102904942833460577368143)
          ·
            refine ⟨1654357414250190866052215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1102904942833460577368143 1654357414250190866052215)
            ·
              refine ⟨2481536121375286299078323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1654357414250190866052215 2481536121375286299078323)
              ·
                refine ⟨3722304182062929448617485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2481536121375286299078323 3722304182062929448617485)
                ·
                  refine ⟨1395864068273598543231557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3722304182062929448617485 1395864068273598543231557)
                  ·
                    refine ⟨261724512801299726855917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1395864068273598543231557 261724512801299726855917)
                    ·
                      refine ⟨98146692300487397570969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 261724512801299726855917 98146692300487397570969)
                      ·
                        rfl

theorem cell23_191140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 1, 3, 4, 3].length) (baseStart_191140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_191140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_191140 prefixEnd_191140 := by exact prefixLift 191140
  have htrace : WordTrace (prefixWord ++ tailWord_191140) baseStart_191140 baseEnd_191140 := by
    simpa [prefixWord, tailWord_191140, baseEnd_191140] using wordTrace_append hprefix tailTrace_191140
  have hstable : (prefixWord ++ tailWord_191140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191140).length < 2 ^ (prefixWord ++ tailWord_191140).sum := by decide
  have hdescent : baseEnd_191140 < baseStart_191140 := by decide
  rcases family_descends (prefixWord ++ tailWord_191140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191157 : List Nat := [1, 3, 3, 3, 1, 1, 2, 1, 1, 4, 3]
def baseStart_191157 : Nat := 118140960795 + 191157 * 2 ^ 59
def prefixEnd_191157 : Nat := 4983230072969 + 3 ^ 40 * 191157 * 2
def baseEnd_191157 : Nat := 98155421471613831058391

theorem tailTrace_191157 : CollatzResearch.WordTrace tailWord_191157 prefixEnd_191157 98155421471613831058391 := by
  unfold tailWord_191157
  simp only [CollatzResearch.WordTrace]
  refine ⟨6972068568478310861547725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4648045712318873907698483 6972068568478310861547725)
  ·
    refine ⟨2614525713179366573080397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6972068568478310861547725 2614525713179366573080397)
    ·
      refine ⟨980447142442262464905149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2614525713179366573080397 980447142442262464905149)
      ·
        refine ⟨367667678415848424339431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 980447142442262464905149 367667678415848424339431)
        ·
          refine ⟨551501517623772636509147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 367667678415848424339431 551501517623772636509147)
          ·
            refine ⟨827252276435658954763721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 551501517623772636509147 827252276435658954763721)
            ·
              refine ⟨620439207326744216072791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 827252276435658954763721 620439207326744216072791)
              ·
                refine ⟨930658810990116324109187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 620439207326744216072791 930658810990116324109187)
                ·
                  refine ⟨1395988216485174486163781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 930658810990116324109187 1395988216485174486163781)
                  ·
                    refine ⟨261747790590970216155709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1395988216485174486163781 261747790590970216155709)
                    ·
                      refine ⟨98155421471613831058391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 261747790590970216155709 98155421471613831058391)
                      ·
                        rfl

theorem cell23_191157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_191157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_191157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_191157 prefixEnd_191157 := by exact prefixLift 191157
  have htrace : WordTrace (prefixWord ++ tailWord_191157) baseStart_191157 baseEnd_191157 := by
    simpa [prefixWord, tailWord_191157, baseEnd_191157] using wordTrace_append hprefix tailTrace_191157
  have hstable : (prefixWord ++ tailWord_191157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191157).length < 2 ^ (prefixWord ++ tailWord_191157).sum := by decide
  have hdescent : baseEnd_191157 < baseStart_191157 := by decide
  rcases family_descends (prefixWord ++ tailWord_191157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191183 : List Nat := [1, 1, 2, 1, 1, 3, 1, 1, 4, 1, 7]
def baseStart_191183 : Nat := 118140960795 + 191183 * 2 ^ 59
def prefixEnd_191183 : Nat := 4983230072969 + 3 ^ 40 * 191183 * 2
def baseEnd_191183 : Nat := 98168771968630729333271

theorem tailTrace_191183 : CollatzResearch.WordTrace tailWord_191183 prefixEnd_191183 98168771968630729333271 := by
  unfold tailWord_191183
  simp only [CollatzResearch.WordTrace]
  refine ⟨6973016866384117301994203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4648677910922744867996135 6973016866384117301994203)
  ·
    refine ⟨10459525299576175952991305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6973016866384117301994203 10459525299576175952991305)
    ·
      refine ⟨7844643974682131964743479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10459525299576175952991305 7844643974682131964743479)
      ·
        refine ⟨11766965962023197947115219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7844643974682131964743479 11766965962023197947115219)
        ·
          refine ⟨17650448943034796920672829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11766965962023197947115219 17650448943034796920672829)
          ·
            refine ⟨6618918353638048845252311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17650448943034796920672829 6618918353638048845252311)
            ·
              refine ⟨9928377530457073267878467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6618918353638048845252311 9928377530457073267878467)
              ·
                refine ⟨14892566295685609901817701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9928377530457073267878467 14892566295685609901817701)
                ·
                  refine ⟨2792356180441051856590819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14892566295685609901817701 2792356180441051856590819)
                  ·
                    refine ⟨4188534270661577784886229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2792356180441051856590819 4188534270661577784886229)
                    ·
                      refine ⟨98168771968630729333271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 4188534270661577784886229 98168771968630729333271)
                      ·
                        rfl

theorem cell23_191183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 4, 1, 7].length) (baseStart_191183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_191183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_191183 prefixEnd_191183 := by exact prefixLift 191183
  have htrace : WordTrace (prefixWord ++ tailWord_191183) baseStart_191183 baseEnd_191183 := by
    simpa [prefixWord, tailWord_191183, baseEnd_191183] using wordTrace_append hprefix tailTrace_191183
  have hstable : (prefixWord ++ tailWord_191183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191183).length < 2 ^ (prefixWord ++ tailWord_191183).sum := by decide
  have hdescent : baseEnd_191183 < baseStart_191183 := by decide
  rcases family_descends (prefixWord ++ tailWord_191183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191214 : List Nat := [4, 1, 2, 1, 1, 3, 1, 3, 2, 3, 2]
def baseStart_191214 : Nat := 118140960795 + 191214 * 2 ^ 59
def prefixEnd_191214 : Nat := 4983230072969 + 3 ^ 40 * 191214 * 2
def baseEnd_191214 : Nat := 98184689868920108045629

theorem tailTrace_191214 : CollatzResearch.WordTrace tailWord_191214 prefixEnd_191214 98184689868920108045629 := by
  unfold tailWord_191214
  simp only [CollatzResearch.WordTrace]
  refine ⟨871768441158976199546587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4649431686181206397581797 871768441158976199546587)
  ·
    refine ⟨1307652661738464299319881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 871768441158976199546587 1307652661738464299319881)
    ·
      refine ⟨980739496303848224489911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1307652661738464299319881 980739496303848224489911)
      ·
        refine ⟨1471109244455772336734867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 980739496303848224489911 1471109244455772336734867)
        ·
          refine ⟨2206663866683658505102301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1471109244455772336734867 2206663866683658505102301)
          ·
            refine ⟨827498950006371939413363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2206663866683658505102301 827498950006371939413363)
            ·
              refine ⟨1241248425009557909120045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 827498950006371939413363 1241248425009557909120045)
              ·
                refine ⟨465468159378584215920017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1241248425009557909120045 465468159378584215920017)
                ·
                  refine ⟨349101119533938161940013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 465468159378584215920017 349101119533938161940013)
                  ·
                    refine ⟨130912919825226810727505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 349101119533938161940013 130912919825226810727505)
                    ·
                      refine ⟨98184689868920108045629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 130912919825226810727505 98184689868920108045629)
                      ·
                        rfl

theorem cell23_191214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 3, 2, 3, 2].length) (baseStart_191214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_191214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_191214 prefixEnd_191214 := by exact prefixLift 191214
  have htrace : WordTrace (prefixWord ++ tailWord_191214) baseStart_191214 baseEnd_191214 := by
    simpa [prefixWord, tailWord_191214, baseEnd_191214] using wordTrace_append hprefix tailTrace_191214
  have hstable : (prefixWord ++ tailWord_191214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191214).length < 2 ^ (prefixWord ++ tailWord_191214).sum := by decide
  have hdescent : baseEnd_191214 < baseStart_191214 := by decide
  rcases family_descends (prefixWord ++ tailWord_191214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191244 : List Nat := [2, 2, 1, 2, 2, 1, 1, 5, 3, 2, 2]
def baseStart_191244 : Nat := 118140960795 + 191244 * 2 ^ 59
def prefixEnd_191244 : Nat := 4983230072969 + 3 ^ 40 * 191244 * 2
def baseEnd_191244 : Nat := 98200094288554990670491

theorem tailTrace_191244 : CollatzResearch.WordTrace tailWord_191244 prefixEnd_191244 98200094288554990670491 := by
  unfold tailWord_191244
  simp only [CollatzResearch.WordTrace]
  refine ⟨3487620859581562359982393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4650161146108749813309857 3487620859581562359982393)
  ·
    refine ⟨2615715644686171769986795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3487620859581562359982393 2615715644686171769986795)
    ·
      refine ⟨3923573467029257654980193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2615715644686171769986795 3923573467029257654980193)
      ·
        refine ⟨2942680100271943241235145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3923573467029257654980193 2942680100271943241235145)
        ·
          refine ⟨2207010075203957430926359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2942680100271943241235145 2207010075203957430926359)
          ·
            refine ⟨3310515112805936146389539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2207010075203957430926359 3310515112805936146389539)
            ·
              refine ⟨4965772669208904219584309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3310515112805936146389539 4965772669208904219584309)
              ·
                refine ⟨465541187738334770586029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4965772669208904219584309 465541187738334770586029)
                ·
                  refine ⟨174577945401875538969761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 465541187738334770586029 174577945401875538969761)
                  ·
                    refine ⟨130933459051406654227321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 174577945401875538969761 130933459051406654227321)
                    ·
                      refine ⟨98200094288554990670491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 130933459051406654227321 98200094288554990670491)
                      ·
                        rfl

theorem cell23_191244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 5, 3, 2, 2].length) (baseStart_191244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_191244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_191244 prefixEnd_191244 := by exact prefixLift 191244
  have htrace : WordTrace (prefixWord ++ tailWord_191244) baseStart_191244 baseEnd_191244 := by
    simpa [prefixWord, tailWord_191244, baseEnd_191244] using wordTrace_append hprefix tailTrace_191244
  have hstable : (prefixWord ++ tailWord_191244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191244).length < 2 ^ (prefixWord ++ tailWord_191244).sum := by decide
  have hdescent : baseEnd_191244 < baseStart_191244 := by decide
  rcases family_descends (prefixWord ++ tailWord_191244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191278 : List Nat := [4, 1, 3, 2, 1, 3, 2, 1, 1, 1, 4]
def baseStart_191278 : Nat := 118140960795 + 191278 * 2 ^ 59
def prefixEnd_191278 : Nat := 4983230072969 + 3 ^ 40 * 191278 * 2
def baseEnd_191278 : Nat := 98217552630807857645335

theorem tailTrace_191278 : CollatzResearch.WordTrace tailWord_191278 prefixEnd_191278 98217552630807857645335 := by
  unfold tailWord_191278
  simp only [CollatzResearch.WordTrace]
  refine ⟨872060225129993565837811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4650987867359965684468325 872060225129993565837811)
  ·
    refine ⟨1308090337694990348756717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 872060225129993565837811 1308090337694990348756717)
    ·
      refine ⟨490533876635621380783769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1308090337694990348756717 490533876635621380783769)
      ·
        refine ⟨367900407476716035587827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 490533876635621380783769 367900407476716035587827)
        ·
          refine ⟨551850611215074053381741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 367900407476716035587827 551850611215074053381741)
          ·
            refine ⟨206943979205652770018153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 551850611215074053381741 206943979205652770018153)
            ·
              refine ⟨155207984404239577513615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 206943979205652770018153 155207984404239577513615)
              ·
                refine ⟨232811976606359366270423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 155207984404239577513615 232811976606359366270423)
                ·
                  refine ⟨349217964909539049405635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 232811976606359366270423 349217964909539049405635)
                  ·
                    refine ⟨523826947364308574108453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 349217964909539049405635 523826947364308574108453)
                    ·
                      refine ⟨98217552630807857645335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 523826947364308574108453 98217552630807857645335)
                      ·
                        rfl

theorem cell23_191278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 2, 1, 1, 1, 4].length) (baseStart_191278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_191278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_191278 prefixEnd_191278 := by exact prefixLift 191278
  have htrace : WordTrace (prefixWord ++ tailWord_191278) baseStart_191278 baseEnd_191278 := by
    simpa [prefixWord, tailWord_191278, baseEnd_191278] using wordTrace_append hprefix tailTrace_191278
  have hstable : (prefixWord ++ tailWord_191278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191278).length < 2 ^ (prefixWord ++ tailWord_191278).sum := by decide
  have hdescent : baseEnd_191278 < baseStart_191278 := by decide
  rcases family_descends (prefixWord ++ tailWord_191278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191320 : List Nat := [2, 1, 2, 2, 1, 1, 1, 2, 3, 3, 5]
def baseStart_191320 : Nat := 118140960795 + 191320 * 2 ^ 59
def prefixEnd_191320 : Nat := 4983230072969 + 3 ^ 40 * 191320 * 2
def baseEnd_191320 : Nat := 98239118818296693320141

theorem tailTrace_191320 : CollatzResearch.WordTrace tailWord_191320 prefixEnd_191320 98239118818296693320141 := by
  unfold tailWord_191320
  simp only [CollatzResearch.WordTrace]
  refine ⟨3489006833443894849865707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4652009111258526466487609 3489006833443894849865707)
  ·
    refine ⟨5233510250165842274798561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3489006833443894849865707 5233510250165842274798561)
    ·
      refine ⟨3925132687624381706098921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5233510250165842274798561 3925132687624381706098921)
      ·
        refine ⟨2943849515718286279574191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3925132687624381706098921 2943849515718286279574191)
        ·
          refine ⟨4415774273577429419361287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2943849515718286279574191 4415774273577429419361287)
          ·
            refine ⟨6623661410366144129041931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4415774273577429419361287 6623661410366144129041931)
            ·
              refine ⟨9935492115549216193562897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6623661410366144129041931 9935492115549216193562897)
              ·
                refine ⟨7451619086661912145172173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9935492115549216193562897 7451619086661912145172173)
                ·
                  refine ⟨2794357157498217054439565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7451619086661912145172173 2794357157498217054439565)
                  ·
                    refine ⟨1047883934061831395414837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2794357157498217054439565 1047883934061831395414837)
                    ·
                      refine ⟨98239118818296693320141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1047883934061831395414837 98239118818296693320141)
                      ·
                        rfl

theorem cell23_191320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 3, 3, 5].length) (baseStart_191320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_191320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_191320 prefixEnd_191320 := by exact prefixLift 191320
  have htrace : WordTrace (prefixWord ++ tailWord_191320) baseStart_191320 baseEnd_191320 := by
    simpa [prefixWord, tailWord_191320, baseEnd_191320] using wordTrace_append hprefix tailTrace_191320
  have hstable : (prefixWord ++ tailWord_191320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191320).length < 2 ^ (prefixWord ++ tailWord_191320).sum := by decide
  have hdescent : baseEnd_191320 < baseStart_191320 := by decide
  rcases family_descends (prefixWord ++ tailWord_191320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191321 : List Nat := [1, 2, 1, 2, 2, 5, 2, 2, 1, 3, 2]
def baseStart_191321 : Nat := 118140960795 + 191321 * 2 ^ 59
def prefixEnd_191321 : Nat := 4983230072969 + 3 ^ 40 * 191321 * 2
def baseEnd_191321 : Nat := 98239632298951189407637

theorem tailTrace_191321 : CollatzResearch.WordTrace tailWord_191321 prefixEnd_191321 98239632298951189407637 := by
  unfold tailWord_191321
  simp only [CollatzResearch.WordTrace]
  refine ⟨6978050139884166870517817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4652033426589444580345211 6978050139884166870517817)
  ·
    refine ⟨5233537604913125152888363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6978050139884166870517817 5233537604913125152888363)
    ·
      refine ⟨7850306407369687729332545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5233537604913125152888363 7850306407369687729332545)
      ·
        refine ⟨5887729805527265796999409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7850306407369687729332545 5887729805527265796999409)
        ·
          refine ⟨4415797354145449347749557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5887729805527265796999409 4415797354145449347749557)
          ·
            refine ⟨413981001951135876351521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4415797354145449347749557 413981001951135876351521)
            ·
              refine ⟨310485751463351907263641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 413981001951135876351521 310485751463351907263641)
              ·
                refine ⟨232864313597513930447731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 310485751463351907263641 232864313597513930447731)
                ·
                  refine ⟨349296470396270895671597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 232864313597513930447731 349296470396270895671597)
                  ·
                    refine ⟨130986176398601585876849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 349296470396270895671597 130986176398601585876849)
                    ·
                      refine ⟨98239632298951189407637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 130986176398601585876849 98239632298951189407637)
                      ·
                        rfl

theorem cell23_191321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 2, 2, 1, 3, 2].length) (baseStart_191321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_191321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_191321 prefixEnd_191321 := by exact prefixLift 191321
  have htrace : WordTrace (prefixWord ++ tailWord_191321) baseStart_191321 baseEnd_191321 := by
    simpa [prefixWord, tailWord_191321, baseEnd_191321] using wordTrace_append hprefix tailTrace_191321
  have hstable : (prefixWord ++ tailWord_191321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191321).length < 2 ^ (prefixWord ++ tailWord_191321).sum := by decide
  have hdescent : baseEnd_191321 < baseStart_191321 := by decide
  rcases family_descends (prefixWord ++ tailWord_191321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191357 : List Nat := [1, 4, 1, 1, 2, 1, 5, 1, 7]
def baseStart_191357 : Nat := 118140960795 + 191357 * 2 ^ 59
def prefixEnd_191357 : Nat := 4983230072969 + 3 ^ 40 * 191357 * 2
def baseEnd_191357 : Nat := 10917568622501449839719

theorem tailTrace_191357 : CollatzResearch.WordTrace tailWord_191357 prefixEnd_191357 10917568622501449839719 := by
  unfold tailWord_191357
  simp only [CollatzResearch.WordTrace]
  refine ⟨6979363167753745018828325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4652908778502496679218883 6979363167753745018828325)
  ·
    refine ⟨1308630593953827191030311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6979363167753745018828325 1308630593953827191030311)
    ·
      refine ⟨1962945890930740786545467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1308630593953827191030311 1962945890930740786545467)
      ·
        refine ⟨2944418836396111179818201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1962945890930740786545467 2944418836396111179818201)
        ·
          refine ⟨2208314127297083384863651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2944418836396111179818201 2208314127297083384863651)
          ·
            refine ⟨3312471190945625077295477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2208314127297083384863651 3312471190945625077295477)
            ·
              refine ⟨310544174151152350996451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3312471190945625077295477 310544174151152350996451)
              ·
                refine ⟨465816261226728526494677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 310544174151152350996451 465816261226728526494677)
                ·
                  refine ⟨10917568622501449839719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 465816261226728526494677 10917568622501449839719)
                  ·
                    rfl

theorem cell23_191357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 5, 1, 7].length) (baseStart_191357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_191357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_191357 prefixEnd_191357 := by exact prefixLift 191357
  have htrace : WordTrace (prefixWord ++ tailWord_191357) baseStart_191357 baseEnd_191357 := by
    simpa [prefixWord, tailWord_191357, baseEnd_191357] using wordTrace_append hprefix tailTrace_191357
  have hstable : (prefixWord ++ tailWord_191357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191357).length < 2 ^ (prefixWord ++ tailWord_191357).sum := by decide
  have hdescent : baseEnd_191357 < baseStart_191357 := by decide
  rcases family_descends (prefixWord ++ tailWord_191357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191360 : List Nat := [2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 8]
def baseStart_191360 : Nat := 118140960795 + 191360 * 2 ^ 59
def prefixEnd_191360 : Nat := 4983230072969 + 3 ^ 40 * 191360 * 2
def baseEnd_191360 : Nat := 98259658044476536819957

theorem tailTrace_191360 : CollatzResearch.WordTrace tailWord_191360 prefixEnd_191360 98259658044476536819957 := by
  unfold tailWord_191360
  simp only [CollatzResearch.WordTrace]
  refine ⟨3489736293371438265593767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4652981724495251020791689 3489736293371438265593767)
  ·
    refine ⟨5234604440057157398390651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3489736293371438265593767 5234604440057157398390651)
    ·
      refine ⟨7851906660085736097585977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5234604440057157398390651 7851906660085736097585977)
      ·
        refine ⟨5888929995064302073189483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7851906660085736097585977 5888929995064302073189483)
        ·
          refine ⟨8833394992596453109784225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5888929995064302073189483 8833394992596453109784225)
          ·
            refine ⟨6625046244447339832338169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8833394992596453109784225 6625046244447339832338169)
            ·
              refine ⟨4968784683335504874253627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6625046244447339832338169 4968784683335504874253627)
              ·
                refine ⟨7453177025003257311380441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4968784683335504874253627 7453177025003257311380441)
                ·
                  refine ⟨5589882768752442983535331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7453177025003257311380441 5589882768752442983535331)
                  ·
                    refine ⟨8384824153128664475302997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5589882768752442983535331 8384824153128664475302997)
                    ·
                      refine ⟨98259658044476536819957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 8384824153128664475302997 98259658044476536819957)
                      ·
                        rfl

theorem cell23_191360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 8].length) (baseStart_191360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_191360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_191360 prefixEnd_191360 := by exact prefixLift 191360
  have htrace : WordTrace (prefixWord ++ tailWord_191360) baseStart_191360 baseEnd_191360 := by
    simpa [prefixWord, tailWord_191360, baseEnd_191360] using wordTrace_append hprefix tailTrace_191360
  have hstable : (prefixWord ++ tailWord_191360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191360).length < 2 ^ (prefixWord ++ tailWord_191360).sum := by decide
  have hdescent : baseEnd_191360 < baseStart_191360 := by decide
  rcases family_descends (prefixWord ++ tailWord_191360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191368 : List Nat := [2, 1, 3, 3, 2, 2, 1, 3, 2, 2, 2]
def baseStart_191368 : Nat := 118140960795 + 191368 * 2 ^ 59
def prefixEnd_191368 : Nat := 4983230072969 + 3 ^ 40 * 191368 * 2
def baseEnd_191368 : Nat := 98263765889712505519921

theorem tailTrace_191368 : CollatzResearch.WordTrace tailWord_191368 prefixEnd_191368 98263765889712505519921 := by
  unfold tailWord_191368
  simp only [CollatzResearch.WordTrace]
  refine ⟨3489882185356946948739379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4653176247142595931652505 3489882185356946948739379)
  ·
    refine ⟨5234823278035420423109069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3489882185356946948739379 5234823278035420423109069)
    ·
      refine ⟨1963058729263282658665901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5234823278035420423109069 1963058729263282658665901)
      ·
        refine ⟨736147023473730996999713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1963058729263282658665901 736147023473730996999713)
        ·
          refine ⟨552110267605298247749785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 736147023473730996999713 552110267605298247749785)
          ·
            refine ⟨414082700703973685812339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 552110267605298247749785 414082700703973685812339)
            ·
              refine ⟨621124051055960528718509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 414082700703973685812339 621124051055960528718509)
              ·
                refine ⟨232921519145985198269441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 621124051055960528718509 232921519145985198269441)
                ·
                  refine ⟨174691139359488898702081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 232921519145985198269441 174691139359488898702081)
                  ·
                    refine ⟨131018354519616674026561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 174691139359488898702081 131018354519616674026561)
                    ·
                      refine ⟨98263765889712505519921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 131018354519616674026561 98263765889712505519921)
                      ·
                        rfl

theorem cell23_191368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 3, 2, 2, 2].length) (baseStart_191368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_191368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_191368 prefixEnd_191368 := by exact prefixLift 191368
  have htrace : WordTrace (prefixWord ++ tailWord_191368) baseStart_191368 baseEnd_191368 := by
    simpa [prefixWord, tailWord_191368, baseEnd_191368] using wordTrace_append hprefix tailTrace_191368
  have hstable : (prefixWord ++ tailWord_191368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191368).length < 2 ^ (prefixWord ++ tailWord_191368).sum := by decide
  have hdescent : baseEnd_191368 < baseStart_191368 := by decide
  rcases family_descends (prefixWord ++ tailWord_191368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191407 : List Nat := [1, 1, 2, 1, 2, 2, 2, 3, 4, 1, 4]
def baseStart_191407 : Nat := 118140960795 + 191407 * 2 ^ 59
def prefixEnd_191407 : Nat := 4983230072969 + 3 ^ 40 * 191407 * 2
def baseEnd_191407 : Nat := 98283791635237852932241

theorem tailTrace_191407 : CollatzResearch.WordTrace tailWord_191407 prefixEnd_191407 98283791635237852932241 := by
  unfold tailWord_191407
  simp only [CollatzResearch.WordTrace]
  refine ⟨6981186817572603558148475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4654124545048402372098983 6981186817572603558148475)
  ·
    refine ⟨10471780226358905337222713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6981186817572603558148475 10471780226358905337222713)
    ·
      refine ⟨7853835169769179002917035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10471780226358905337222713 7853835169769179002917035)
      ·
        refine ⟨11780752754653768504375553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7853835169769179002917035 11780752754653768504375553)
        ·
          refine ⟨8835564565990326378281665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11780752754653768504375553 8835564565990326378281665)
          ·
            refine ⟨6626673424492744783711249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8835564565990326378281665 6626673424492744783711249)
            ·
              refine ⟨4970005068369558587783437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6626673424492744783711249 4970005068369558587783437)
              ·
                refine ⟨1863751900638584470418789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4970005068369558587783437 1863751900638584470418789)
                ·
                  refine ⟨349453481369734588203523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1863751900638584470418789 349453481369734588203523)
                  ·
                    refine ⟨524180222054601882305285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 349453481369734588203523 524180222054601882305285)
                    ·
                      refine ⟨98283791635237852932241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 524180222054601882305285 98283791635237852932241)
                      ·
                        rfl

theorem cell23_191407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 3, 4, 1, 4].length) (baseStart_191407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_191407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_191407 prefixEnd_191407 := by exact prefixLift 191407
  have htrace : WordTrace (prefixWord ++ tailWord_191407) baseStart_191407 baseEnd_191407 := by
    simpa [prefixWord, tailWord_191407, baseEnd_191407] using wordTrace_append hprefix tailTrace_191407
  have hstable : (prefixWord ++ tailWord_191407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191407).length < 2 ^ (prefixWord ++ tailWord_191407).sum := by decide
  have hdescent : baseEnd_191407 < baseStart_191407 := by decide
  rcases family_descends (prefixWord ++ tailWord_191407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191424 : List Nat := [2, 1, 1, 2, 3, 3, 1, 1, 1, 6, 2]
def baseStart_191424 : Nat := 118140960795 + 191424 * 2 ^ 59
def prefixEnd_191424 : Nat := 4983230072969 + 3 ^ 40 * 191424 * 2
def baseEnd_191424 : Nat := 98292520806364286419663

theorem tailTrace_191424 : CollatzResearch.WordTrace tailWord_191424 prefixEnd_191424 98292520806364286419663 := by
  unfold tailWord_191424
  simp only [CollatzResearch.WordTrace]
  refine ⟨3490903429255507730758663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4654537905674010307678217 3490903429255507730758663)
  ·
    refine ⟨5236355143883261596137995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3490903429255507730758663 5236355143883261596137995)
    ·
      refine ⟨7854532715824892394206993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5236355143883261596137995 7854532715824892394206993)
      ·
        refine ⟨5890899536868669295655245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7854532715824892394206993 5890899536868669295655245)
        ·
          refine ⟨2209087326325750985870717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5890899536868669295655245 2209087326325750985870717)
          ·
            refine ⟨828407747372156619701519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2209087326325750985870717 828407747372156619701519)
            ·
              refine ⟨1242611621058234929552279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 828407747372156619701519 1242611621058234929552279)
              ·
                refine ⟨1863917431587352394328419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1242611621058234929552279 1863917431587352394328419)
                ·
                  refine ⟨2795876147381028591492629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1863917431587352394328419 2795876147381028591492629)
                  ·
                    refine ⟨131056694408485715226217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2795876147381028591492629 131056694408485715226217)
                    ·
                      refine ⟨98292520806364286419663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 131056694408485715226217 98292520806364286419663)
                      ·
                        rfl

theorem cell23_191424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 1, 1, 6, 2].length) (baseStart_191424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_191424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_191424 prefixEnd_191424 := by exact prefixLift 191424
  have htrace : WordTrace (prefixWord ++ tailWord_191424) baseStart_191424 baseEnd_191424 := by
    simpa [prefixWord, tailWord_191424, baseEnd_191424] using wordTrace_append hprefix tailTrace_191424
  have hstable : (prefixWord ++ tailWord_191424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191424).length < 2 ^ (prefixWord ++ tailWord_191424).sum := by decide
  have hdescent : baseEnd_191424 < baseStart_191424 := by decide
  rcases family_descends (prefixWord ++ tailWord_191424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191427 : List Nat := [1, 1, 1, 3, 1, 1, 2, 3, 3, 4, 3]
def baseStart_191427 : Nat := 118140960795 + 191427 * 2 ^ 59
def prefixEnd_191427 : Nat := 4983230072969 + 3 ^ 40 * 191427 * 2
def baseEnd_191427 : Nat := 98294061248327774682149

theorem tailTrace_191427 : CollatzResearch.WordTrace tailWord_191427 prefixEnd_191427 98294061248327774682149 := by
  unfold tailWord_191427
  simp only [CollatzResearch.WordTrace]
  refine ⟨6981916277500146973876535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4654610851666764649251023 6981916277500146973876535)
  ·
    refine ⟨10472874416250220460814803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6981916277500146973876535 10472874416250220460814803)
    ·
      refine ⟨15709311624375330691222205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10472874416250220460814803 15709311624375330691222205)
      ·
        refine ⟨5890991859140749009208327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15709311624375330691222205 5890991859140749009208327)
        ·
          refine ⟨8836487788711123513812491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5890991859140749009208327 8836487788711123513812491)
          ·
            refine ⟨13254731683066685270718737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8836487788711123513812491 13254731683066685270718737)
            ·
              refine ⟨9941048762300013953039053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13254731683066685270718737 9941048762300013953039053)
              ·
                refine ⟨3727893285862505232389645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9941048762300013953039053 3727893285862505232389645)
                ·
                  refine ⟨1397959982198439462146117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3727893285862505232389645 1397959982198439462146117)
                  ·
                    refine ⟨262117496662207399152397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1397959982198439462146117 262117496662207399152397)
                    ·
                      refine ⟨98294061248327774682149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 262117496662207399152397 98294061248327774682149)
                      ·
                        rfl

theorem cell23_191427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 3, 3, 4, 3].length) (baseStart_191427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_191427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_191427 prefixEnd_191427 := by exact prefixLift 191427
  have htrace : WordTrace (prefixWord ++ tailWord_191427) baseStart_191427 baseEnd_191427 := by
    simpa [prefixWord, tailWord_191427, baseEnd_191427] using wordTrace_append hprefix tailTrace_191427
  have hstable : (prefixWord ++ tailWord_191427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191427).length < 2 ^ (prefixWord ++ tailWord_191427).sum := by decide
  have hdescent : baseEnd_191427 < baseStart_191427 := by decide
  rcases family_descends (prefixWord ++ tailWord_191427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191458 : List Nat := [3, 3, 3, 1, 1, 1, 1, 2, 2, 4, 2]
def baseStart_191458 : Nat := 118140960795 + 191458 * 2 ^ 59
def prefixEnd_191458 : Nat := 4983230072969 + 3 ^ 40 * 191458 * 2
def baseEnd_191458 : Nat := 98309979148617153394507

theorem tailTrace_191458 : CollatzResearch.WordTrace tailWord_191458 prefixEnd_191458 98309979148617153394507 := by
  unfold tailWord_191458
  simp only [CollatzResearch.WordTrace]
  refine ⟨1745761735096959817063757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4655364626925226178836685 1745761735096959817063757)
  ·
    refine ⟨654660650661359931398909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1745761735096959817063757 654660650661359931398909)
    ·
      refine ⟨245497743998009974274591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 654660650661359931398909 245497743998009974274591)
      ·
        refine ⟨368246615997014961411887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245497743998009974274591 368246615997014961411887)
        ·
          refine ⟨552369923995522442117831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 368246615997014961411887 552369923995522442117831)
          ·
            refine ⟨828554885993283663176747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 552369923995522442117831 828554885993283663176747)
            ·
              refine ⟨1242832328989925494765121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 828554885993283663176747 1242832328989925494765121)
              ·
                refine ⟨932124246742444121073841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1242832328989925494765121 932124246742444121073841)
                ·
                  refine ⟨699093185056833090805381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 932124246742444121073841 699093185056833090805381)
                  ·
                    refine ⟨131079972198156204526009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 699093185056833090805381 131079972198156204526009)
                    ·
                      refine ⟨98309979148617153394507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 131079972198156204526009 98309979148617153394507)
                      ·
                        rfl

theorem cell23_191458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 2, 2, 4, 2].length) (baseStart_191458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_191458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_191458 prefixEnd_191458 := by exact prefixLift 191458
  have htrace : WordTrace (prefixWord ++ tailWord_191458) baseStart_191458 baseEnd_191458 := by
    simpa [prefixWord, tailWord_191458, baseEnd_191458] using wordTrace_append hprefix tailTrace_191458
  have hstable : (prefixWord ++ tailWord_191458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191458).length < 2 ^ (prefixWord ++ tailWord_191458).sum := by decide
  have hdescent : baseEnd_191458 < baseStart_191458 := by decide
  rcases family_descends (prefixWord ++ tailWord_191458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191464 : List Nat := [2, 1, 4, 1, 1, 1, 5, 2, 6]
def baseStart_191464 : Nat := 118140960795 + 191464 * 2 ^ 59
def prefixEnd_191464 : Nat := 4983230072969 + 3 ^ 40 * 191464 * 2
def baseEnd_191464 : Nat := 10923673336949347768831

theorem tailTrace_191464 : CollatzResearch.WordTrace tailWord_191464 prefixEnd_191464 10923673336949347768831 := by
  unfold tailWord_191464
  simp only [CollatzResearch.WordTrace]
  refine ⟨3491632889183051146486723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4655510518910734861982297 3491632889183051146486723)
  ·
    refine ⟨5237449333774576719730085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3491632889183051146486723 5237449333774576719730085)
    ·
      refine ⟨982021750082733134949391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5237449333774576719730085 982021750082733134949391)
      ·
        refine ⟨1473032625124099702424087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 982021750082733134949391 1473032625124099702424087)
        ·
          refine ⟨2209548937686149553636131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1473032625124099702424087 2209548937686149553636131)
          ·
            refine ⟨3314323406529224330454197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2209548937686149553636131 3314323406529224330454197)
            ·
              refine ⟨310717819362114780980081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3314323406529224330454197 310717819362114780980081)
              ·
                refine ⟨233038364521586085735061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 310717819362114780980081 233038364521586085735061)
                ·
                  refine ⟨10923673336949347768831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 233038364521586085735061 10923673336949347768831)
                  ·
                    rfl

theorem cell23_191464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 5, 2, 6].length) (baseStart_191464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_191464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_191464 prefixEnd_191464 := by exact prefixLift 191464
  have htrace : WordTrace (prefixWord ++ tailWord_191464) baseStart_191464 baseEnd_191464 := by
    simpa [prefixWord, tailWord_191464, baseEnd_191464] using wordTrace_append hprefix tailTrace_191464
  have hstable : (prefixWord ++ tailWord_191464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191464).length < 2 ^ (prefixWord ++ tailWord_191464).sum := by decide
  have hdescent : baseEnd_191464 < baseStart_191464 := by decide
  rcases family_descends (prefixWord ++ tailWord_191464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191497 : List Nat := [1, 2, 1, 1, 3, 1, 1, 2, 2, 5, 4]
def baseStart_191497 : Nat := 118140960795 + 191497 * 2 ^ 59
def prefixEnd_191497 : Nat := 4983230072969 + 3 ^ 40 * 191497 * 2
def baseEnd_191497 : Nat := 98330004894142500806827

theorem tailTrace_191497 : CollatzResearch.WordTrace tailWord_191497 prefixEnd_191497 98330004894142500806827 := by
  unfold tailWord_191497
  simp only [CollatzResearch.WordTrace]
  refine ⟨6984469387246548928924745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4656312924831032619283163 6984469387246548928924745)
  ·
    refine ⟨5238352040434911696693559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6984469387246548928924745 5238352040434911696693559)
    ·
      refine ⟨7857528060652367545040339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5238352040434911696693559 7857528060652367545040339)
      ·
        refine ⟨11786292090978551317560509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7857528060652367545040339 11786292090978551317560509)
        ·
          refine ⟨4419859534116956744085191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11786292090978551317560509 4419859534116956744085191)
          ·
            refine ⟨6629789301175435116127787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4419859534116956744085191 6629789301175435116127787)
            ·
              refine ⟨9944683951763152674191681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6629789301175435116127787 9944683951763152674191681)
              ·
                refine ⟨7458512963822364505643761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9944683951763152674191681 7458512963822364505643761)
                ·
                  refine ⟨5593884722866773379232821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7458512963822364505643761 5593884722866773379232821)
                  ·
                    refine ⟨524426692768760004303077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5593884722866773379232821 524426692768760004303077)
                    ·
                      refine ⟨98330004894142500806827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 524426692768760004303077 98330004894142500806827)
                      ·
                        rfl

theorem cell23_191497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 5, 4].length) (baseStart_191497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_191497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_191497 prefixEnd_191497 := by exact prefixLift 191497
  have htrace : WordTrace (prefixWord ++ tailWord_191497) baseStart_191497 baseEnd_191497 := by
    simpa [prefixWord, tailWord_191497, baseEnd_191497] using wordTrace_append hprefix tailTrace_191497
  have hstable : (prefixWord ++ tailWord_191497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191497).length < 2 ^ (prefixWord ++ tailWord_191497).sum := by decide
  have hdescent : baseEnd_191497 < baseStart_191497 := by decide
  rcases family_descends (prefixWord ++ tailWord_191497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191507 : List Nat := [1, 1, 1, 2, 1, 4, 1, 3, 3, 6]
def baseStart_191507 : Nat := 118140960795 + 191507 * 2 ^ 59
def prefixEnd_191507 : Nat := 4983230072969 + 3 ^ 40 * 191507 * 2
def baseEnd_191507 : Nat := 32778379900229153893927

theorem tailTrace_191507 : CollatzResearch.WordTrace tailWord_191507 prefixEnd_191507 32778379900229153893927 := by
  unfold tailWord_191507
  simp only [CollatzResearch.WordTrace]
  refine ⟨6984834117210320636788775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4656556078140213757859183 6984834117210320636788775)
  ·
    refine ⟨10477251175815480955183163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6984834117210320636788775 10477251175815480955183163)
    ·
      refine ⟨15715876763723221432774745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10477251175815480955183163 15715876763723221432774745)
      ·
        refine ⟨11786907572792416074581059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15715876763723221432774745 11786907572792416074581059)
        ·
          refine ⟨17680361359188624111871589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11786907572792416074581059 17680361359188624111871589)
          ·
            refine ⟨3315067754847867020975923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17680361359188624111871589 3315067754847867020975923)
            ·
              refine ⟨4972601632271800531463885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3315067754847867020975923 4972601632271800531463885)
              ·
                refine ⟨1864725612101925199298957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4972601632271800531463885 1864725612101925199298957)
                ·
                  refine ⟨699272104538221949737109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1864725612101925199298957 699272104538221949737109)
                  ·
                    refine ⟨32778379900229153893927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 699272104538221949737109 32778379900229153893927)
                    ·
                      rfl

theorem cell23_191507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 3, 3, 6].length) (baseStart_191507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_191507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_191507 prefixEnd_191507 := by exact prefixLift 191507
  have htrace : WordTrace (prefixWord ++ tailWord_191507) baseStart_191507 baseEnd_191507 := by
    simpa [prefixWord, tailWord_191507, baseEnd_191507] using wordTrace_append hprefix tailTrace_191507
  have hstable : (prefixWord ++ tailWord_191507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191507).length < 2 ^ (prefixWord ++ tailWord_191507).sum := by decide
  have hdescent : baseEnd_191507 < baseStart_191507 := by decide
  rcases family_descends (prefixWord ++ tailWord_191507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191511 : List Nat := [1, 1, 3, 5, 1, 1, 2, 3, 1, 5]
def baseStart_191511 : Nat := 118140960795 + 191511 * 2 ^ 59
def prefixEnd_191511 : Nat := 4983230072969 + 3 ^ 40 * 191511 * 2
def baseEnd_191511 : Nat := 32779064541101815343921

theorem tailTrace_191511 : CollatzResearch.WordTrace tailWord_191511 prefixEnd_191511 32779064541101815343921 := by
  unfold tailWord_191511
  simp only [CollatzResearch.WordTrace]
  refine ⟨6984980009195829319934387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4656653339463886213289591 6984980009195829319934387)
  ·
    refine ⟨10477470013793743979901581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6984980009195829319934387 10477470013793743979901581)
    ·
      refine ⟨3929051255172653992463093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10477470013793743979901581 3929051255172653992463093)
      ·
        refine ⟨368348555172436311793415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3929051255172653992463093 368348555172436311793415)
        ·
          refine ⟨552522832758654467690123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 368348555172436311793415 552522832758654467690123)
          ·
            refine ⟨828784249137981701535185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 552522832758654467690123 828784249137981701535185)
            ·
              refine ⟨621588186853486276151389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 828784249137981701535185 621588186853486276151389)
              ·
                refine ⟨233095570070057353556771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 621588186853486276151389 233095570070057353556771)
                ·
                  refine ⟨349643355105086030335157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 233095570070057353556771 349643355105086030335157)
                  ·
                    refine ⟨32779064541101815343921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 349643355105086030335157 32779064541101815343921)
                    ·
                      rfl

theorem cell23_191511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 3, 1, 5].length) (baseStart_191511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_191511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_191511 prefixEnd_191511 := by exact prefixLift 191511
  have htrace : WordTrace (prefixWord ++ tailWord_191511) baseStart_191511 baseEnd_191511 := by
    simpa [prefixWord, tailWord_191511, baseEnd_191511] using wordTrace_append hprefix tailTrace_191511
  have hstable : (prefixWord ++ tailWord_191511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191511).length < 2 ^ (prefixWord ++ tailWord_191511).sum := by decide
  have hdescent : baseEnd_191511 < baseStart_191511 := by decide
  rcases family_descends (prefixWord ++ tailWord_191511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191525 : List Nat := [1, 3, 1, 2, 2, 2, 5, 2, 1, 1, 3]
def baseStart_191525 : Nat := 118140960795 + 191525 * 2 ^ 59
def prefixEnd_191525 : Nat := 4983230072969 + 3 ^ 40 * 191525 * 2
def baseEnd_191525 : Nat := 98344382352468391256699

theorem tailTrace_191525 : CollatzResearch.WordTrace tailWord_191525 prefixEnd_191525 98344382352468391256699 := by
  unfold tailWord_191525
  simp only [CollatzResearch.WordTrace]
  refine ⟨6985490631145109710944029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4656993754096739807296019 6985490631145109710944029)
  ·
    refine ⟨2619558986679416141604011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6985490631145109710944029 2619558986679416141604011)
    ·
      refine ⟨3929338480019124212406017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2619558986679416141604011 3929338480019124212406017)
      ·
        refine ⟨2947003860014343159304513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3929338480019124212406017 2947003860014343159304513)
        ·
          refine ⟨2210252895010757369478385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2947003860014343159304513 2210252895010757369478385)
          ·
            refine ⟨1657689671258068027108789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2210252895010757369478385 1657689671258068027108789)
            ·
              refine ⟨155408406680443877541449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1657689671258068027108789 155408406680443877541449)
              ·
                refine ⟨116556305010332908156087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 155408406680443877541449 116556305010332908156087)
                ·
                  refine ⟨174834457515499362234131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 116556305010332908156087 174834457515499362234131)
                  ·
                    refine ⟨262251686273249043351197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 174834457515499362234131 262251686273249043351197)
                    ·
                      refine ⟨98344382352468391256699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 262251686273249043351197 98344382352468391256699)
                      ·
                        rfl

theorem cell23_191525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 5, 2, 1, 1, 3].length) (baseStart_191525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_191525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_191525 prefixEnd_191525 := by exact prefixLift 191525
  have htrace : WordTrace (prefixWord ++ tailWord_191525) baseStart_191525 baseEnd_191525 := by
    simpa [prefixWord, tailWord_191525, baseEnd_191525] using wordTrace_append hprefix tailTrace_191525
  have hstable : (prefixWord ++ tailWord_191525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191525).length < 2 ^ (prefixWord ++ tailWord_191525).sum := by decide
  have hdescent : baseEnd_191525 < baseStart_191525 := by decide
  rcases family_descends (prefixWord ++ tailWord_191525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191544 : List Nat := [2, 1, 2, 1, 5, 1, 2, 1, 1, 1, 6]
def baseStart_191544 : Nat := 118140960795 + 191544 * 2 ^ 59
def prefixEnd_191544 : Nat := 4983230072969 + 3 ^ 40 * 191544 * 2
def baseEnd_191544 : Nat := 98354138484903816919111

theorem tailTrace_191544 : CollatzResearch.WordTrace tailWord_191544 prefixEnd_191544 98354138484903816919111 := by
  unfold tailWord_191544
  simp only [CollatzResearch.WordTrace]
  refine ⟨3493091809038137977942843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4657455745384183970590457 3493091809038137977942843)
  ·
    refine ⟨5239637713557206966914265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3493091809038137977942843 5239637713557206966914265)
    ·
      refine ⟨3929728285167905225185699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5239637713557206966914265 3929728285167905225185699)
      ·
        refine ⟨5894592427751857837778549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3929728285167905225185699 5894592427751857837778549)
        ·
          refine ⟨552618040101736672291739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5894592427751857837778549 552618040101736672291739)
          ·
            refine ⟨828927060152605008437609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 552618040101736672291739 828927060152605008437609)
            ·
              refine ⟨621695295114453756328207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 828927060152605008437609 621695295114453756328207)
              ·
                refine ⟨932542942671680634492311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 621695295114453756328207 932542942671680634492311)
                ·
                  refine ⟨1398814414007520951738467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 932542942671680634492311 1398814414007520951738467)
                  ·
                    refine ⟨2098221621011281427607701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1398814414007520951738467 2098221621011281427607701)
                    ·
                      refine ⟨98354138484903816919111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2098221621011281427607701 98354138484903816919111)
                      ·
                        rfl

theorem cell23_191544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 1, 1, 1, 6].length) (baseStart_191544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_191544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_191544 prefixEnd_191544 := by exact prefixLift 191544
  have htrace : WordTrace (prefixWord ++ tailWord_191544) baseStart_191544 baseEnd_191544 := by
    simpa [prefixWord, tailWord_191544, baseEnd_191544] using wordTrace_append hprefix tailTrace_191544
  have hstable : (prefixWord ++ tailWord_191544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191544).length < 2 ^ (prefixWord ++ tailWord_191544).sum := by decide
  have hdescent : baseEnd_191544 < baseStart_191544 := by decide
  rcases family_descends (prefixWord ++ tailWord_191544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191548 : List Nat := [2, 2, 2, 2, 2, 4, 1, 2, 1, 1, 4]
def baseStart_191548 : Nat := 118140960795 + 191548 * 2 ^ 59
def prefixEnd_191548 : Nat := 4983230072969 + 3 ^ 40 * 191548 * 2
def baseEnd_191548 : Nat := 98356192407521801269093

theorem tailTrace_191548 : CollatzResearch.WordTrace tailWord_191548 prefixEnd_191548 98356192407521801269093 := by
  unfold tailWord_191548
  simp only [CollatzResearch.WordTrace]
  refine ⟨3493164755030892319515649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4657553006707856426020865 3493164755030892319515649)
  ·
    refine ⟨2619873566273169239636737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3493164755030892319515649 2619873566273169239636737)
    ·
      refine ⟨1964905174704876929727553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2619873566273169239636737 1964905174704876929727553)
      ·
        refine ⟨1473678881028657697295665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1964905174704876929727553 1473678881028657697295665)
        ·
          refine ⟨1105259160771493272971749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1473678881028657697295665 1105259160771493272971749)
          ·
            refine ⟨207236092644654988682203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1105259160771493272971749 207236092644654988682203)
            ·
              refine ⟨310854138966982483023305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 207236092644654988682203 310854138966982483023305)
              ·
                refine ⟨233140604225236862267479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 310854138966982483023305 233140604225236862267479)
                ·
                  refine ⟨349710906337855293401219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 233140604225236862267479 349710906337855293401219)
                  ·
                    refine ⟨524566359506782940101829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 349710906337855293401219 524566359506782940101829)
                    ·
                      refine ⟨98356192407521801269093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 524566359506782940101829 98356192407521801269093)
                      ·
                        rfl

theorem cell23_191548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 1, 2, 1, 1, 4].length) (baseStart_191548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_191548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_191548 prefixEnd_191548 := by exact prefixLift 191548
  have htrace : WordTrace (prefixWord ++ tailWord_191548) baseStart_191548 baseEnd_191548 := by
    simpa [prefixWord, tailWord_191548, baseEnd_191548] using wordTrace_append hprefix tailTrace_191548
  have hstable : (prefixWord ++ tailWord_191548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191548).length < 2 ^ (prefixWord ++ tailWord_191548).sum := by decide
  have hdescent : baseEnd_191548 < baseStart_191548 := by decide
  rcases family_descends (prefixWord ++ tailWord_191548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191558 : List Nat := [6, 1, 1, 1, 1, 3, 1, 2, 1, 6]
def baseStart_191558 : Nat := 118140960795 + 191558 * 2 ^ 59
def prefixEnd_191558 : Nat := 4983230072969 + 3 ^ 40 * 191558 * 2
def baseEnd_191558 : Nat := 32787109071355587381349

theorem tailTrace_191558 : CollatzResearch.WordTrace tailWord_191558 prefixEnd_191558 32787109071355587381349 := by
  unfold tailWord_191558
  simp only [CollatzResearch.WordTrace]
  refine ⟨218334195000798635840479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 4657796160017037564596885 218334195000798635840479)
  ·
    refine ⟨327501292501197953760719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 218334195000798635840479 327501292501197953760719)
    ·
      refine ⟨491251938751796930641079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 327501292501197953760719 491251938751796930641079)
      ·
        refine ⟨736877908127695395961619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 491251938751796930641079 736877908127695395961619)
        ·
          refine ⟨1105316862191543093942429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 736877908127695395961619 1105316862191543093942429)
          ·
            refine ⟨414493823321828660228411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1105316862191543093942429 414493823321828660228411)
            ·
              refine ⟨621740734982742990342617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 414493823321828660228411 621740734982742990342617)
              ·
                refine ⟨466305551237057242756963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 621740734982742990342617 466305551237057242756963)
                ·
                  refine ⟨699458326855585864135445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 466305551237057242756963 699458326855585864135445)
                  ·
                    refine ⟨32787109071355587381349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 699458326855585864135445 32787109071355587381349)
                    ·
                      rfl

theorem cell23_191558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 2, 1, 6].length) (baseStart_191558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_191558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_191558 prefixEnd_191558 := by exact prefixLift 191558
  have htrace : WordTrace (prefixWord ++ tailWord_191558) baseStart_191558 baseEnd_191558 := by
    simpa [prefixWord, tailWord_191558, baseEnd_191558] using wordTrace_append hprefix tailTrace_191558
  have hstable : (prefixWord ++ tailWord_191558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191558).length < 2 ^ (prefixWord ++ tailWord_191558).sum := by decide
  have hdescent : baseEnd_191558 < baseStart_191558 := by decide
  rcases family_descends (prefixWord ++ tailWord_191558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191565 : List Nat := [1, 6, 1, 1, 1, 3, 3, 1, 1, 1, 4]
def baseStart_191565 : Nat := 118140960795 + 191565 * 2 ^ 59
def prefixEnd_191565 : Nat := 4983230072969 + 3 ^ 40 * 191565 * 2
def baseEnd_191565 : Nat := 98364921578648234756515

theorem tailTrace_191565 : CollatzResearch.WordTrace tailWord_191565 prefixEnd_191565 98364921578648234756515 := by
  unfold tailWord_191565
  simp only [CollatzResearch.WordTrace]
  refine ⟨6986949551000196542400149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4657966367333464361600099 6986949551000196542400149)
  ·
    refine ⟨327513260203134212925007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 6986949551000196542400149 327513260203134212925007)
    ·
      refine ⟨491269890304701319387511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 327513260203134212925007 491269890304701319387511)
      ·
        refine ⟨736904835457051979081267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 491269890304701319387511 736904835457051979081267)
        ·
          refine ⟨1105357253185577968621901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 736904835457051979081267 1105357253185577968621901)
          ·
            refine ⟨414508969944591738233213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1105357253185577968621901 414508969944591738233213)
            ·
              refine ⟨155440863729221901837455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 414508969944591738233213 155440863729221901837455)
              ·
                refine ⟨233161295593832852756183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 155440863729221901837455 233161295593832852756183)
                ·
                  refine ⟨349741943390749279134275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 233161295593832852756183 349741943390749279134275)
                  ·
                    refine ⟨524612915086123918701413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 349741943390749279134275 524612915086123918701413)
                    ·
                      refine ⟨98364921578648234756515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 524612915086123918701413 98364921578648234756515)
                      ·
                        rfl

theorem cell23_191565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 3, 1, 1, 1, 4].length) (baseStart_191565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_191565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_191565 prefixEnd_191565 := by exact prefixLift 191565
  have htrace : WordTrace (prefixWord ++ tailWord_191565) baseStart_191565 baseEnd_191565 := by
    simpa [prefixWord, tailWord_191565, baseEnd_191565] using wordTrace_append hprefix tailTrace_191565
  have hstable : (prefixWord ++ tailWord_191565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191565).length < 2 ^ (prefixWord ++ tailWord_191565).sum := by decide
  have hdescent : baseEnd_191565 < baseStart_191565 := by decide
  rcases family_descends (prefixWord ++ tailWord_191565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191567 : List Nat := [1, 1, 2, 1, 1, 2, 2, 1, 3, 9]
def baseStart_191567 : Nat := 118140960795 + 191567 * 2 ^ 59
def prefixEnd_191567 : Nat := 4983230072969 + 3 ^ 40 * 191567 * 2
def baseEnd_191567 : Nat := 32788649513319075643835

theorem tailTrace_191567 : CollatzResearch.WordTrace tailWord_191567 prefixEnd_191567 32788649513319075643835 := by
  unfold tailWord_191567
  simp only [CollatzResearch.WordTrace]
  refine ⟨6987022496992950883972955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4658014997995300589315303 6987022496992950883972955)
  ·
    refine ⟨10480533745489426325959433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6987022496992950883972955 10480533745489426325959433)
    ·
      refine ⟨7860400309117069744469575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10480533745489426325959433 7860400309117069744469575)
      ·
        refine ⟨11790600463675604616704363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7860400309117069744469575 11790600463675604616704363)
        ·
          refine ⟨17685900695513406925056545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11790600463675604616704363 17685900695513406925056545)
          ·
            refine ⟨13264425521635055193792409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17685900695513406925056545 13264425521635055193792409)
            ·
              refine ⟨9948319141226291395344307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13264425521635055193792409 9948319141226291395344307)
              ·
                refine ⟨14922478711839437093016461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9948319141226291395344307 14922478711839437093016461)
                ·
                  refine ⟨5595929516939788909881173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14922478711839437093016461 5595929516939788909881173)
                  ·
                    refine ⟨32788649513319075643835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 5595929516939788909881173 32788649513319075643835)
                    ·
                      rfl

theorem cell23_191567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 3, 9].length) (baseStart_191567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_191567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_191567 prefixEnd_191567 := by exact prefixLift 191567
  have htrace : WordTrace (prefixWord ++ tailWord_191567) baseStart_191567 baseEnd_191567 := by
    simpa [prefixWord, tailWord_191567, baseEnd_191567] using wordTrace_append hprefix tailTrace_191567
  have hstable : (prefixWord ++ tailWord_191567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191567).length < 2 ^ (prefixWord ++ tailWord_191567).sum := by decide
  have hdescent : baseEnd_191567 < baseStart_191567 := by decide
  rcases family_descends (prefixWord ++ tailWord_191567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191598 : List Nat := [4, 1, 2, 2, 1, 3, 2, 1, 1, 3, 3]
def baseStart_191598 : Nat := 118140960795 + 191598 * 2 ^ 59
def prefixEnd_191598 : Nat := 4983230072969 + 3 ^ 40 * 191598 * 2
def baseEnd_191598 : Nat := 98381866440246605643863

theorem tailTrace_191598 : CollatzResearch.WordTrace tailWord_191598 prefixEnd_191598 98381866440246605643863 := by
  unfold tailWord_191598
  simp only [CollatzResearch.WordTrace]
  refine ⟨873519144985080397293931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4658768773253762118900965 873519144985080397293931)
  ·
    refine ⟨1310278717477620595940897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 873519144985080397293931 1310278717477620595940897)
    ·
      refine ⟨982709038108215446955673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1310278717477620595940897 982709038108215446955673)
      ·
        refine ⟨737031778581161585216755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 982709038108215446955673 737031778581161585216755)
        ·
          refine ⟨1105547667871742377825133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 737031778581161585216755 1105547667871742377825133)
          ·
            refine ⟨414580375451903391684425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1105547667871742377825133 414580375451903391684425)
            ·
              refine ⟨310935281588927543763319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 414580375451903391684425 310935281588927543763319)
              ·
                refine ⟨466402922383391315644979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 310935281588927543763319 466402922383391315644979)
                ·
                  refine ⟨699604383575086973467469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 466402922383391315644979 699604383575086973467469)
                  ·
                    refine ⟨262351643840657615050301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 699604383575086973467469 262351643840657615050301)
                    ·
                      refine ⟨98381866440246605643863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 262351643840657615050301 98381866440246605643863)
                      ·
                        rfl

theorem cell23_191598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 2, 1, 1, 3, 3].length) (baseStart_191598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_191598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_191598 prefixEnd_191598 := by exact prefixLift 191598
  have htrace : WordTrace (prefixWord ++ tailWord_191598) baseStart_191598 baseEnd_191598 := by
    simpa [prefixWord, tailWord_191598, baseEnd_191598] using wordTrace_append hprefix tailTrace_191598
  have hstable : (prefixWord ++ tailWord_191598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191598).length < 2 ^ (prefixWord ++ tailWord_191598).sum := by decide
  have hdescent : baseEnd_191598 < baseStart_191598 := by decide
  rcases family_descends (prefixWord ++ tailWord_191598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191625 : List Nat := [1, 2, 1, 1, 4, 3, 4, 1, 1, 3, 2]
def baseStart_191625 : Nat := 118140960795 + 191625 * 2 ^ 59
def prefixEnd_191625 : Nat := 4983230072969 + 3 ^ 40 * 191625 * 2
def baseEnd_191625 : Nat := 98395730417918000006239

theorem tailTrace_191625 : CollatzResearch.WordTrace tailWord_191625 prefixEnd_191625 98395730417918000006239 := by
  unfold tailWord_191625
  simp only [CollatzResearch.WordTrace]
  refine ⟨6989137930782826789584329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4659425287188551193056219 6989137930782826789584329)
  ·
    refine ⟨5241853448087120092188247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6989137930782826789584329 5241853448087120092188247)
    ·
      refine ⟨7862780172130680138282371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5241853448087120092188247 7862780172130680138282371)
      ·
        refine ⟨11794170258196020207423557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7862780172130680138282371 11794170258196020207423557)
        ·
          refine ⟨2211406923411753788891917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11794170258196020207423557 2211406923411753788891917)
          ·
            refine ⟨829277596279407670834469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2211406923411753788891917 829277596279407670834469)
            ·
              refine ⟨155489549302388938281463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 829277596279407670834469 155489549302388938281463)
              ·
                refine ⟨233234323953583407422195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 155489549302388938281463 233234323953583407422195)
                ·
                  refine ⟨349851485930375111133293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 233234323953583407422195 349851485930375111133293)
                  ·
                    refine ⟨131194307223890666674985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 349851485930375111133293 131194307223890666674985)
                    ·
                      refine ⟨98395730417918000006239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 131194307223890666674985 98395730417918000006239)
                      ·
                        rfl

theorem cell23_191625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 4, 1, 1, 3, 2].length) (baseStart_191625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_191625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_191625 prefixEnd_191625 := by exact prefixLift 191625
  have htrace : WordTrace (prefixWord ++ tailWord_191625) baseStart_191625 baseEnd_191625 := by
    simpa [prefixWord, tailWord_191625, baseEnd_191625] using wordTrace_append hprefix tailTrace_191625
  have hstable : (prefixWord ++ tailWord_191625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191625).length < 2 ^ (prefixWord ++ tailWord_191625).sum := by decide
  have hdescent : baseEnd_191625 < baseStart_191625 := by decide
  rcases family_descends (prefixWord ++ tailWord_191625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191655 : List Nat := [1, 1, 6, 2, 1, 1, 3, 1, 1, 4, 2]
def baseStart_191655 : Nat := 118140960795 + 191655 * 2 ^ 59
def prefixEnd_191655 : Nat := 4983230072969 + 3 ^ 40 * 191655 * 2
def baseEnd_191655 : Nat := 98411134837552882631101

theorem tailTrace_191655 : CollatzResearch.WordTrace tailWord_191655 prefixEnd_191655 98411134837552882631101 := by
  unfold tailWord_191655
  simp only [CollatzResearch.WordTrace]
  refine ⟨6990232120674141913176419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4660154747116094608784279 6990232120674141913176419)
  ·
    refine ⟨10485348181011212869764629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6990232120674141913176419 10485348181011212869764629)
    ·
      refine ⟨491500695984900603270217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 10485348181011212869764629 491500695984900603270217)
      ·
        refine ⟨368625521988675452452663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 491500695984900603270217 368625521988675452452663)
        ·
          refine ⟨552938282983013178678995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 368625521988675452452663 552938282983013178678995)
          ·
            refine ⟨829407424474519768018493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 552938282983013178678995 829407424474519768018493)
            ·
              refine ⟨311027784177944913006935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 829407424474519768018493 311027784177944913006935)
              ·
                refine ⟨466541676266917369510403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 311027784177944913006935 466541676266917369510403)
                ·
                  refine ⟨699812514400376054265605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 466541676266917369510403 699812514400376054265605)
                  ·
                    refine ⟨131214846450070510174801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 699812514400376054265605 131214846450070510174801)
                    ·
                      refine ⟨98411134837552882631101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 131214846450070510174801 98411134837552882631101)
                      ·
                        rfl

theorem cell23_191655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 3, 1, 1, 4, 2].length) (baseStart_191655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_191655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_191655 prefixEnd_191655 := by exact prefixLift 191655
  have htrace : WordTrace (prefixWord ++ tailWord_191655) baseStart_191655 baseEnd_191655 := by
    simpa [prefixWord, tailWord_191655, baseEnd_191655] using wordTrace_append hprefix tailTrace_191655
  have hstable : (prefixWord ++ tailWord_191655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191655).length < 2 ^ (prefixWord ++ tailWord_191655).sum := by decide
  have hdescent : baseEnd_191655 < baseStart_191655 := by decide
  rcases family_descends (prefixWord ++ tailWord_191655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191698 : List Nat := [3, 2, 2, 2, 1, 1, 2, 1, 2, 5, 2]
def baseStart_191698 : Nat := 118140960795 + 191698 * 2 ^ 59
def prefixEnd_191698 : Nat := 4983230072969 + 3 ^ 40 * 191698 * 2
def baseEnd_191698 : Nat := 98433214505696214393403

theorem tailTrace_191698 : CollatzResearch.WordTrace tailWord_191698 prefixEnd_191698 98433214505696214393403 := by
  unfold tailWord_191698
  simp only [CollatzResearch.WordTrace]
  refine ⟨1747950114879590064247937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4661200306345573504661165 1747950114879590064247937)
  ·
    refine ⟨1310962586159692548185953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1747950114879590064247937 1310962586159692548185953)
    ·
      refine ⟨983221939619769411139465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1310962586159692548185953 983221939619769411139465)
      ·
        refine ⟨737416454714827058354599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 983221939619769411139465 737416454714827058354599)
        ·
          refine ⟨1106124682072240587531899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 737416454714827058354599 1106124682072240587531899)
          ·
            refine ⟨1659187023108360881297849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1106124682072240587531899 1659187023108360881297849)
            ·
              refine ⟨1244390267331270660973387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1659187023108360881297849 1244390267331270660973387)
              ·
                refine ⟨1866585400996905991460081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1244390267331270660973387 1866585400996905991460081)
                ·
                  refine ⟨1399939050747679493595061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1866585400996905991460081 1399939050747679493595061)
                  ·
                    refine ⟨131244286007594952524537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1399939050747679493595061 131244286007594952524537)
                    ·
                      refine ⟨98433214505696214393403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 131244286007594952524537 98433214505696214393403)
                      ·
                        rfl

theorem cell23_191698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 1, 2, 5, 2].length) (baseStart_191698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_191698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_191698 prefixEnd_191698 := by exact prefixLift 191698
  have htrace : WordTrace (prefixWord ++ tailWord_191698) baseStart_191698 baseEnd_191698 := by
    simpa [prefixWord, tailWord_191698, baseEnd_191698] using wordTrace_append hprefix tailTrace_191698
  have hstable : (prefixWord ++ tailWord_191698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191698).length < 2 ^ (prefixWord ++ tailWord_191698).sum := by decide
  have hdescent : baseEnd_191698 < baseStart_191698 := by decide
  rcases family_descends (prefixWord ++ tailWord_191698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191701 : List Nat := [1, 3, 2, 4, 1, 1, 1, 1, 1, 1, 7]
def baseStart_191701 : Nat := 118140960795 + 191701 * 2 ^ 59
def prefixEnd_191701 : Nat := 4983230072969 + 3 ^ 40 * 191701 * 2
def baseEnd_191701 : Nat := 98434754947659702655889

theorem tailTrace_191701 : CollatzResearch.WordTrace tailWord_191701 prefixEnd_191701 98434754947659702655889 := by
  unfold tailWord_191701
  simp only [CollatzResearch.WordTrace]
  refine ⟨6991909878507491769350957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4661273252338327846233971 6991909878507491769350957)
  ·
    refine ⟨2621966204440309413506609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6991909878507491769350957 2621966204440309413506609)
    ·
      refine ⟨1966474653330232060129957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2621966204440309413506609 1966474653330232060129957)
      ·
        refine ⟨368713997499418511274367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1966474653330232060129957 368713997499418511274367)
        ·
          refine ⟨553070996249127766911551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 368713997499418511274367 553070996249127766911551)
          ·
            refine ⟨829606494373691650367327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 553070996249127766911551 829606494373691650367327)
            ·
              refine ⟨1244409741560537475550991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 829606494373691650367327 1244409741560537475550991)
              ·
                refine ⟨1866614612340806213326487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1244409741560537475550991 1866614612340806213326487)
                ·
                  refine ⟨2799921918511209319989731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1866614612340806213326487 2799921918511209319989731)
                  ·
                    refine ⟨4199882877766813979984597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2799921918511209319989731 4199882877766813979984597)
                    ·
                      refine ⟨98434754947659702655889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 4199882877766813979984597 98434754947659702655889)
                      ·
                        rfl

theorem cell23_191701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_191701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_191701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_191701 prefixEnd_191701 := by exact prefixLift 191701
  have htrace : WordTrace (prefixWord ++ tailWord_191701) baseStart_191701 baseEnd_191701 := by
    simpa [prefixWord, tailWord_191701, baseEnd_191701] using wordTrace_append hprefix tailTrace_191701
  have hstable : (prefixWord ++ tailWord_191701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191701).length < 2 ^ (prefixWord ++ tailWord_191701).sum := by decide
  have hdescent : baseEnd_191701 < baseStart_191701 := by decide
  rcases family_descends (prefixWord ++ tailWord_191701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191755 : List Nat := [1, 1, 1, 1, 5, 4, 1, 4, 1, 4]
def baseStart_191755 : Nat := 118140960795 + 191755 * 2 ^ 59
def prefixEnd_191755 : Nat := 4983230072969 + 3 ^ 40 * 191755 * 2
def baseEnd_191755 : Nat := 32820827634334163793547

theorem tailTrace_191755 : CollatzResearch.WordTrace tailWord_191755 prefixEnd_191755 32820827634334163793547 := by
  unfold tailWord_191755
  simp only [CollatzResearch.WordTrace]
  refine ⟨6993879420311858991816719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4662586280207905994544479 6993879420311858991816719)
  ·
    refine ⟨10490819130467788487725079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6993879420311858991816719 10490819130467788487725079)
    ·
      refine ⟨15736228695701682731587619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10490819130467788487725079 15736228695701682731587619)
      ·
        refine ⟨23604343043552524097381429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15736228695701682731587619 23604343043552524097381429)
        ·
          refine ⟨2212907160333049134129509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23604343043552524097381429 2212907160333049134129509)
          ·
            refine ⟨414920092562446712649283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2212907160333049134129509 414920092562446712649283)
            ·
              refine ⟨622380138843670068973925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 414920092562446712649283 622380138843670068973925)
              ·
                refine ⟨116696276033188137932611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 622380138843670068973925 116696276033188137932611)
                ·
                  refine ⟨175044414049782206898917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 116696276033188137932611 175044414049782206898917)
                  ·
                    refine ⟨32820827634334163793547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 175044414049782206898917 32820827634334163793547)
                    ·
                      rfl

theorem cell23_191755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 4, 1, 4].length) (baseStart_191755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_191755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_191755 prefixEnd_191755 := by exact prefixLift 191755
  have htrace : WordTrace (prefixWord ++ tailWord_191755) baseStart_191755 baseEnd_191755 := by
    simpa [prefixWord, tailWord_191755, baseEnd_191755] using wordTrace_append hprefix tailTrace_191755
  have hstable : (prefixWord ++ tailWord_191755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191755).length < 2 ^ (prefixWord ++ tailWord_191755).sum := by decide
  have hdescent : baseEnd_191755 < baseStart_191755 := by decide
  rcases family_descends (prefixWord ++ tailWord_191755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191789 : List Nat := [1, 5, 3, 1, 1, 2, 2, 3, 1, 4]
def baseStart_191789 : Nat := 118140960795 + 191789 * 2 ^ 59
def prefixEnd_191789 : Nat := 4983230072969 + 3 ^ 40 * 191789 * 2
def baseEnd_191789 : Nat := 32826647081751786118495

theorem tailTrace_191789 : CollatzResearch.WordTrace tailWord_191789 prefixEnd_191789 32826647081751786118495 := by
  unfold tailWord_191789
  simp only [CollatzResearch.WordTrace]
  refine ⟨6995119502188682798554421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4663413001459121865702947 6995119502188682798554421)
  ·
    refine ⟨655792453330189012364477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6995119502188682798554421 655792453330189012364477)
    ·
      refine ⟨245922169998820879636679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 655792453330189012364477 245922169998820879636679)
      ·
        refine ⟨368883254998231319455019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245922169998820879636679 368883254998231319455019)
        ·
          refine ⟨553324882497346979182529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 368883254998231319455019 553324882497346979182529)
          ·
            refine ⟨414993661873010234386897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 553324882497346979182529 414993661873010234386897)
            ·
              refine ⟨311245246404757675790173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 414993661873010234386897 311245246404757675790173)
              ·
                refine ⟨116716967401784128421315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 311245246404757675790173 116716967401784128421315)
                ·
                  refine ⟨175075451102676192631973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 116716967401784128421315 175075451102676192631973)
                  ·
                    refine ⟨32826647081751786118495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 175075451102676192631973 32826647081751786118495)
                    ·
                      rfl

theorem cell23_191789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_191789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_191789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_191789 prefixEnd_191789 := by exact prefixLift 191789
  have htrace : WordTrace (prefixWord ++ tailWord_191789) baseStart_191789 baseEnd_191789 := by
    simpa [prefixWord, tailWord_191789, baseEnd_191789] using wordTrace_append hprefix tailTrace_191789
  have hstable : (prefixWord ++ tailWord_191789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191789).length < 2 ^ (prefixWord ++ tailWord_191789).sum := by decide
  have hdescent : baseEnd_191789 < baseStart_191789 := by decide
  rcases family_descends (prefixWord ++ tailWord_191789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191812 : List Nat := [2, 3, 4, 1, 1, 1, 1, 3, 3, 1, 3]
def baseStart_191812 : Nat := 118140960795 + 191812 * 2 ^ 59
def prefixEnd_191812 : Nat := 4983230072969 + 3 ^ 40 * 191812 * 2
def baseEnd_191812 : Nat := 98491751300308768367879

theorem tailTrace_191812 : CollatzResearch.WordTrace tailWord_191812 prefixEnd_191812 98491751300308768367879 := by
  unfold tailWord_191812
  simp only [CollatzResearch.WordTrace]
  refine ⟨3497979190552678863320845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4663972254070238484427793 3497979190552678863320845)
  ·
    refine ⟨1311742196457254573745317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3497979190552678863320845 1311742196457254573745317)
    ·
      refine ⟨245951661835735232577247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1311742196457254573745317 245951661835735232577247)
      ·
        refine ⟨368927492753602848865871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 245951661835735232577247 368927492753602848865871)
        ·
          refine ⟨553391239130404273298807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 368927492753602848865871 553391239130404273298807)
          ·
            refine ⟨830086858695606409948211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 553391239130404273298807 830086858695606409948211)
            ·
              refine ⟨1245130288043409614922317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 830086858695606409948211 1245130288043409614922317)
              ·
                refine ⟨466923858016278605595869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1245130288043409614922317 466923858016278605595869)
                ·
                  refine ⟨175096446756104477098451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 466923858016278605595869 175096446756104477098451)
                  ·
                    refine ⟨262644670134156715647677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 175096446756104477098451 262644670134156715647677)
                    ·
                      refine ⟨98491751300308768367879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 262644670134156715647677 98491751300308768367879)
                      ·
                        rfl

theorem cell23_191812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_191812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_191812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_191812 prefixEnd_191812 := by exact prefixLift 191812
  have htrace : WordTrace (prefixWord ++ tailWord_191812) baseStart_191812 baseEnd_191812 := by
    simpa [prefixWord, tailWord_191812, baseEnd_191812] using wordTrace_append hprefix tailTrace_191812
  have hstable : (prefixWord ++ tailWord_191812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191812).length < 2 ^ (prefixWord ++ tailWord_191812).sum := by decide
  have hdescent : baseEnd_191812 < baseStart_191812 := by decide
  rcases family_descends (prefixWord ++ tailWord_191812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191928 : List Nat := [2, 1, 2, 1, 2, 2, 3, 1, 2, 4, 3]
def baseStart_191928 : Nat := 118140960795 + 191928 * 2 ^ 59
def prefixEnd_191928 : Nat := 4983230072969 + 3 ^ 40 * 191928 * 2
def baseEnd_191928 : Nat := 98551315056230314517345

theorem tailTrace_191928 : CollatzResearch.WordTrace tailWord_191928 prefixEnd_191928 98551315056230314517345 := by
  unfold tailWord_191928
  simp only [CollatzResearch.WordTrace]
  refine ⟨3500094624342554768932219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4666792832456739691909625 3500094624342554768932219)
  ·
    refine ⟨5250141936513832153398329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3500094624342554768932219 5250141936513832153398329)
    ·
      refine ⟨3937606452385374115048747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5250141936513832153398329 3937606452385374115048747)
      ·
        refine ⟨5906409678578061172573121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3937606452385374115048747 5906409678578061172573121)
        ·
          refine ⟨4429807258933545879429841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5906409678578061172573121 4429807258933545879429841)
          ·
            refine ⟨3322355444200159409572381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4429807258933545879429841 3322355444200159409572381)
            ·
              refine ⟨1245883291575059778589643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3322355444200159409572381 1245883291575059778589643)
              ·
                refine ⟨1868824937362589667884465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1245883291575059778589643 1868824937362589667884465)
                ·
                  refine ⟨1401618703021942250913349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1868824937362589667884465 1401618703021942250913349)
                  ·
                    refine ⟨262803506816614172046253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1401618703021942250913349 262803506816614172046253)
                    ·
                      refine ⟨98551315056230314517345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 262803506816614172046253 98551315056230314517345)
                      ·
                        rfl

theorem cell23_191928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 1, 2, 4, 3].length) (baseStart_191928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_191928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_191928 prefixEnd_191928 := by exact prefixLift 191928
  have htrace : WordTrace (prefixWord ++ tailWord_191928) baseStart_191928 baseEnd_191928 := by
    simpa [prefixWord, tailWord_191928, baseEnd_191928] using wordTrace_append hprefix tailTrace_191928
  have hstable : (prefixWord ++ tailWord_191928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191928).length < 2 ^ (prefixWord ++ tailWord_191928).sum := by decide
  have hdescent : baseEnd_191928 < baseStart_191928 := by decide
  rcases family_descends (prefixWord ++ tailWord_191928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191948 : List Nat := [2, 2, 1, 4, 2, 1, 1, 1, 9]
def baseStart_191948 : Nat := 118140960795 + 191948 * 2 ^ 59
def prefixEnd_191948 : Nat := 4983230072969 + 3 ^ 40 * 191948 * 2
def baseEnd_191948 : Nat := 10951287185480026251917

theorem tailTrace_191948 : CollatzResearch.WordTrace tailWord_191948 prefixEnd_191948 10951287185480026251917 := by
  unfold tailWord_191948
  simp only [CollatzResearch.WordTrace]
  refine ⟨3500459354306326476796249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4667279139075101969061665 3500459354306326476796249)
  ·
    refine ⟨2625344515729744857597187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3500459354306326476796249 2625344515729744857597187)
    ·
      refine ⟨3938016773594617286395781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2625344515729744857597187 3938016773594617286395781)
      ·
        refine ⟨738378145048990741199209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3938016773594617286395781 738378145048990741199209)
        ·
          refine ⟨553783608786743055899407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 738378145048990741199209 553783608786743055899407)
          ·
            refine ⟨830675413180114583849111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 553783608786743055899407 830675413180114583849111)
            ·
              refine ⟨1246013119770171875773667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 830675413180114583849111 1246013119770171875773667)
              ·
                refine ⟨1869019679655257813660501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1246013119770171875773667 1869019679655257813660501)
                ·
                  refine ⟨10951287185480026251917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 1869019679655257813660501 10951287185480026251917)
                  ·
                    rfl

theorem cell23_191948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 1, 9].length) (baseStart_191948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_191948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_191948 prefixEnd_191948 := by exact prefixLift 191948
  have htrace : WordTrace (prefixWord ++ tailWord_191948) baseStart_191948 baseEnd_191948 := by
    simpa [prefixWord, tailWord_191948, baseEnd_191948] using wordTrace_append hprefix tailTrace_191948
  have hstable : (prefixWord ++ tailWord_191948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191948).length < 2 ^ (prefixWord ++ tailWord_191948).sum := by decide
  have hdescent : baseEnd_191948 < baseStart_191948 := by decide
  rcases family_descends (prefixWord ++ tailWord_191948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_191975 : List Nat := [1, 1, 5, 2, 1, 2, 1, 2, 2, 3, 3]
def baseStart_191975 : Nat := 118140960795 + 191975 * 2 ^ 59
def prefixEnd_191975 : Nat := 4983230072969 + 3 ^ 40 * 191975 * 2
def baseEnd_191975 : Nat := 98575448646991630629629

theorem tailTrace_191975 : CollatzResearch.WordTrace tailWord_191975 prefixEnd_191975 98575448646991630629629 := by
  unfold tailWord_191975
  simp only [CollatzResearch.WordTrace]
  refine ⟨7001903479514836564825379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4667935653009891043216919 7001903479514836564825379)
  ·
    refine ⟨10502855219272254847238069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7001903479514836564825379 10502855219272254847238069)
    ·
      refine ⟨984642676806773891928569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10502855219272254847238069 984642676806773891928569)
      ·
        refine ⟨738482007605080418946427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 984642676806773891928569 738482007605080418946427)
        ·
          refine ⟨1107723011407620628419641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 738482007605080418946427 1107723011407620628419641)
          ·
            refine ⟨830792258555715471314731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1107723011407620628419641 830792258555715471314731)
            ·
              refine ⟨1246188387833573206972097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 830792258555715471314731 1246188387833573206972097)
              ·
                refine ⟨934641290875179905229073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1246188387833573206972097 934641290875179905229073)
                ·
                  refine ⟨700980968156384928921805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 934641290875179905229073 700980968156384928921805)
                  ·
                    refine ⟨262867863058644348345677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 700980968156384928921805 262867863058644348345677)
                    ·
                      refine ⟨98575448646991630629629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 262867863058644348345677 98575448646991630629629)
                      ·
                        rfl

theorem cell23_191975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 2, 2, 3, 3].length) (baseStart_191975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_191975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_191975 prefixEnd_191975 := by exact prefixLift 191975
  have htrace : WordTrace (prefixWord ++ tailWord_191975) baseStart_191975 baseEnd_191975 := by
    simpa [prefixWord, tailWord_191975, baseEnd_191975] using wordTrace_append hprefix tailTrace_191975
  have hstable : (prefixWord ++ tailWord_191975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_191975).length < 2 ^ (prefixWord ++ tailWord_191975).sum := by decide
  have hdescent : baseEnd_191975 < baseStart_191975 := by decide
  rcases family_descends (prefixWord ++ tailWord_191975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192032 : List Nat := [2, 1, 1, 6, 1, 2, 1, 2, 2, 1, 4]
def baseStart_192032 : Nat := 118140960795 + 192032 * 2 ^ 59
def prefixEnd_192032 : Nat := 4983230072969 + 3 ^ 40 * 192032 * 2
def baseEnd_192032 : Nat := 98604717044297907616867

theorem tailTrace_192032 : CollatzResearch.WordTrace tailWord_192032 prefixEnd_192032 98604717044297907616867 := by
  unfold tailWord_192032
  simp only [CollatzResearch.WordTrace]
  refine ⟨3501991220154167649825175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4669321626872223533100233 3501991220154167649825175)
  ·
    refine ⟨5252986830231251474737763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3501991220154167649825175 5252986830231251474737763)
    ·
      refine ⟨7879480245346877212106645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5252986830231251474737763 7879480245346877212106645)
      ·
        refine ⟨369350636500634869317499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 7879480245346877212106645 369350636500634869317499)
        ·
          refine ⟨554025954750952303976249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 369350636500634869317499 554025954750952303976249)
          ·
            refine ⟨415519466063214227982187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 554025954750952303976249 415519466063214227982187)
            ·
              refine ⟨623279199094821341973281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 415519466063214227982187 623279199094821341973281)
              ·
                refine ⟨467459399321116006479961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 623279199094821341973281 467459399321116006479961)
                ·
                  refine ⟨350594549490837004859971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 467459399321116006479961 350594549490837004859971)
                  ·
                    refine ⟨525891824236255507289957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 350594549490837004859971 525891824236255507289957)
                    ·
                      refine ⟨98604717044297907616867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 525891824236255507289957 98604717044297907616867)
                      ·
                        rfl

theorem cell23_192032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_192032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_192032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_192032 prefixEnd_192032 := by exact prefixLift 192032
  have htrace : WordTrace (prefixWord ++ tailWord_192032) baseStart_192032 baseEnd_192032 := by
    simpa [prefixWord, tailWord_192032, baseEnd_192032] using wordTrace_append hprefix tailTrace_192032
  have hstable : (prefixWord ++ tailWord_192032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192032).length < 2 ^ (prefixWord ++ tailWord_192032).sum := by decide
  have hdescent : baseEnd_192032 < baseStart_192032 := by decide
  rcases family_descends (prefixWord ++ tailWord_192032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192055 : List Nat := [1, 1, 3, 1, 2, 5, 1, 3, 6]
def baseStart_192055 : Nat := 118140960795 + 192055 * 2 ^ 59
def prefixEnd_192055 : Nat := 4983230072969 + 3 ^ 40 * 192055 * 2
def baseEnd_192055 : Nat := 10957391899927924181029

theorem tailTrace_192055 : CollatzResearch.WordTrace tailWord_192055 prefixEnd_192055 10957391899927924181029 := by
  unfold tailWord_192055
  simp only [CollatzResearch.WordTrace]
  refine ⟨7004821319225010227737619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4669880879483340151825079 7004821319225010227737619)
  ·
    refine ⟨10507231978837515341606429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7004821319225010227737619 10507231978837515341606429)
    ·
      refine ⟨3940211992064068253102411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10507231978837515341606429 3940211992064068253102411)
      ·
        refine ⟨5910317988096102379653617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3940211992064068253102411 5910317988096102379653617)
        ·
          refine ⟨4432738491072076784740213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5910317988096102379653617 4432738491072076784740213)
          ·
            refine ⟨415569233538007198569395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4432738491072076784740213 415569233538007198569395)
            ·
              refine ⟨623353850307010797854093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 415569233538007198569395 623353850307010797854093)
              ·
                refine ⟨233757693865129049195285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 623353850307010797854093 233757693865129049195285)
                ·
                  refine ⟨10957391899927924181029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 233757693865129049195285 10957391899927924181029)
                  ·
                    rfl

theorem cell23_192055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 3, 6].length) (baseStart_192055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_192055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_192055 prefixEnd_192055 := by exact prefixLift 192055
  have htrace : WordTrace (prefixWord ++ tailWord_192055) baseStart_192055 baseEnd_192055 := by
    simpa [prefixWord, tailWord_192055, baseEnd_192055] using wordTrace_append hprefix tailTrace_192055
  have hstable : (prefixWord ++ tailWord_192055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192055).length < 2 ^ (prefixWord ++ tailWord_192055).sum := by decide
  have hdescent : baseEnd_192055 < baseStart_192055 := by decide
  rcases family_descends (prefixWord ++ tailWord_192055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192093 : List Nat := [1, 4, 4, 2, 1, 1, 1, 4, 1, 4]
def baseStart_192093 : Nat := 118140960795 + 192093 * 2 ^ 59
def prefixEnd_192093 : Nat := 4983230072969 + 3 ^ 40 * 192093 * 2
def baseEnd_192093 : Nat := 32878679788074056318029

theorem tailTrace_192093 : CollatzResearch.WordTrace tailWord_192093 prefixEnd_192093 32878679788074056318029 := by
  unfold tailWord_192093
  simp only [CollatzResearch.WordTrace]
  refine ⟨7006207293087342717620933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4670804862058228478413955 7006207293087342717620933)
  ·
    refine ⟨1313663867453876759553925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7006207293087342717620933 1313663867453876759553925)
    ·
      refine ⟨246311975147601892416361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1313663867453876759553925 246311975147601892416361)
      ·
        refine ⟨184733981360701419312271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 246311975147601892416361 184733981360701419312271)
        ·
          refine ⟨277100972041052128968407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184733981360701419312271 277100972041052128968407)
          ·
            refine ⟨415651458061578193452611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 277100972041052128968407 415651458061578193452611)
            ·
              refine ⟨623477187092367290178917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 415651458061578193452611 623477187092367290178917)
              ·
                refine ⟨116901972579818866908547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 623477187092367290178917 116901972579818866908547)
                ·
                  refine ⟨175352958869728300362821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 116901972579818866908547 175352958869728300362821)
                  ·
                    refine ⟨32878679788074056318029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 175352958869728300362821 32878679788074056318029)
                    ·
                      rfl

theorem cell23_192093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_192093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_192093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_192093 prefixEnd_192093 := by exact prefixLift 192093
  have htrace : WordTrace (prefixWord ++ tailWord_192093) baseStart_192093 baseEnd_192093 := by
    simpa [prefixWord, tailWord_192093, baseEnd_192093] using wordTrace_append hprefix tailTrace_192093
  have hstable : (prefixWord ++ tailWord_192093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192093).length < 2 ^ (prefixWord ++ tailWord_192093).sum := by decide
  have hdescent : baseEnd_192093 < baseStart_192093 := by decide
  rcases family_descends (prefixWord ++ tailWord_192093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192105 : List Nat := [1, 2, 1, 1, 1, 4, 3, 2, 3, 1, 4]
def baseStart_192105 : Nat := 118140960795 + 192105 * 2 ^ 59
def prefixEnd_192105 : Nat := 4983230072969 + 3 ^ 40 * 192105 * 2
def baseEnd_192105 : Nat := 98642201132076122004031

theorem tailTrace_192105 : CollatzResearch.WordTrace tailWord_192105 prefixEnd_192105 98642201132076122004031 := by
  unfold tailWord_192105
  simp only [CollatzResearch.WordTrace]
  refine ⟨7006644969043868767057769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4671096646029245844705179 7006644969043868767057769)
  ·
    refine ⟨5254983726782901575293327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7006644969043868767057769 5254983726782901575293327)
    ·
      refine ⟨7882475590174352362939991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5254983726782901575293327 7882475590174352362939991)
      ·
        refine ⟨11823713385261528544409987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7882475590174352362939991 11823713385261528544409987)
        ·
          refine ⟨17735570077892292816614981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11823713385261528544409987 17735570077892292816614981)
          ·
            refine ⟨3325419389604804903115309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17735570077892292816614981 3325419389604804903115309)
            ·
              refine ⟨1247032271101801838668241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3325419389604804903115309 1247032271101801838668241)
              ·
                refine ⟨935274203326351379001181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1247032271101801838668241 935274203326351379001181)
                ·
                  refine ⟨350727826247381767125443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 935274203326351379001181 350727826247381767125443)
                  ·
                    refine ⟨526091739371072650688165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 350727826247381767125443 526091739371072650688165)
                    ·
                      refine ⟨98642201132076122004031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 526091739371072650688165 98642201132076122004031)
                      ·
                        rfl

theorem cell23_192105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 2, 3, 1, 4].length) (baseStart_192105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_192105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_192105 prefixEnd_192105 := by exact prefixLift 192105
  have htrace : WordTrace (prefixWord ++ tailWord_192105) baseStart_192105 baseEnd_192105 := by
    simpa [prefixWord, tailWord_192105, baseEnd_192105] using wordTrace_append hprefix tailTrace_192105
  have hstable : (prefixWord ++ tailWord_192105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192105).length < 2 ^ (prefixWord ++ tailWord_192105).sum := by decide
  have hdescent : baseEnd_192105 < baseStart_192105 := by decide
  rcases family_descends (prefixWord ++ tailWord_192105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192159 : List Nat := [1, 1, 2, 7, 1, 1, 1, 2, 1, 1, 5]
def baseStart_192159 : Nat := 118140960795 + 192159 * 2 ^ 59
def prefixEnd_192159 : Nat := 4983230072969 + 3 ^ 40 * 192159 * 2
def baseEnd_192159 : Nat := 98669929087418910728783

theorem tailTrace_192159 : CollatzResearch.WordTrace tailWord_192159 prefixEnd_192159 98669929087418910728783 := by
  unfold tailWord_192159
  simp only [CollatzResearch.WordTrace]
  refine ⟨7008614510848235989523531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4672409673898823993015687 7008614510848235989523531)
  ·
    refine ⟨10512921766272353984285297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7008614510848235989523531 10512921766272353984285297)
    ·
      refine ⟨7884691324704265488213973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10512921766272353984285297 7884691324704265488213973)
      ·
        refine ⟨184797452922756222380015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 7884691324704265488213973 184797452922756222380015)
        ·
          refine ⟨277196179384134333570023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184797452922756222380015 277196179384134333570023)
          ·
            refine ⟨415794269076201500355035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 277196179384134333570023 415794269076201500355035)
            ·
              refine ⟨623691403614302250532553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 415794269076201500355035 623691403614302250532553)
              ·
                refine ⟨467768552710726687899415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 623691403614302250532553 467768552710726687899415)
                ·
                  refine ⟨701652829066090031849123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 467768552710726687899415 701652829066090031849123)
                  ·
                    refine ⟨1052479243599135047773685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 701652829066090031849123 1052479243599135047773685)
                    ·
                      refine ⟨98669929087418910728783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1052479243599135047773685 98669929087418910728783)
                      ·
                        rfl

theorem cell23_192159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_192159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_192159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_192159 prefixEnd_192159 := by exact prefixLift 192159
  have htrace : WordTrace (prefixWord ++ tailWord_192159) baseStart_192159 baseEnd_192159 := by
    simpa [prefixWord, tailWord_192159, baseEnd_192159] using wordTrace_append hprefix tailTrace_192159
  have hstable : (prefixWord ++ tailWord_192159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192159).length < 2 ^ (prefixWord ++ tailWord_192159).sum := by decide
  have hdescent : baseEnd_192159 < baseStart_192159 := by decide
  rcases family_descends (prefixWord ++ tailWord_192159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192185 : List Nat := [1, 2, 1, 4, 1, 1, 3, 1, 2, 2, 5]
def baseStart_192185 : Nat := 118140960795 + 192185 * 2 ^ 59
def prefixEnd_192185 : Nat := 4983230072969 + 3 ^ 40 * 192185 * 2
def baseEnd_192185 : Nat := 98683279584435809003663

theorem tailTrace_192185 : CollatzResearch.WordTrace tailWord_192185 prefixEnd_192185 98683279584435809003663 := by
  unfold tailWord_192185
  simp only [CollatzResearch.WordTrace]
  refine ⟨7009562808754042429970009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4673041872502694953313339 7009562808754042429970009)
  ·
    refine ⟨5257172106565531822477507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7009562808754042429970009 5257172106565531822477507)
    ·
      refine ⟨7885758159848297733716261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5257172106565531822477507 7885758159848297733716261)
      ·
        refine ⟨1478579654971555825071799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7885758159848297733716261 1478579654971555825071799)
        ·
          refine ⟨2217869482457333737607699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1478579654971555825071799 2217869482457333737607699)
          ·
            refine ⟨3326804223686000606411549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2217869482457333737607699 3326804223686000606411549)
            ·
              refine ⟨1247551583882250227404331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3326804223686000606411549 1247551583882250227404331)
              ·
                refine ⟨1871327375823375341106497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1247551583882250227404331 1871327375823375341106497)
                ·
                  refine ⟨1403495531867531505829873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1871327375823375341106497 1403495531867531505829873)
                  ·
                    refine ⟨1052621648900648629372405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1403495531867531505829873 1052621648900648629372405)
                    ·
                      refine ⟨98683279584435809003663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1052621648900648629372405 98683279584435809003663)
                      ·
                        rfl

theorem cell23_192185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 1, 2, 2, 5].length) (baseStart_192185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_192185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_192185 prefixEnd_192185 := by exact prefixLift 192185
  have htrace : WordTrace (prefixWord ++ tailWord_192185) baseStart_192185 baseEnd_192185 := by
    simpa [prefixWord, tailWord_192185, baseEnd_192185] using wordTrace_append hprefix tailTrace_192185
  have hstable : (prefixWord ++ tailWord_192185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192185).length < 2 ^ (prefixWord ++ tailWord_192185).sum := by decide
  have hdescent : baseEnd_192185 < baseStart_192185 := by decide
  rcases family_descends (prefixWord ++ tailWord_192185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192190 : List Nat := [4, 2, 1, 1, 2, 4, 1, 3, 1, 2, 2]
def baseStart_192190 : Nat := 118140960795 + 192190 * 2 ^ 59
def prefixEnd_192190 : Nat := 4983230072969 + 3 ^ 40 * 192190 * 2
def baseEnd_192190 : Nat := 98685846987708289441141

theorem tailTrace_192190 : CollatzResearch.WordTrace tailWord_192190 prefixEnd_192190 98685846987708289441141 := by
  unfold tailWord_192190
  simp only [CollatzResearch.WordTrace]
  refine ⟨876218146716991035487753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4673163449157285522601349 876218146716991035487753)
  ·
    refine ⟨657163610037743276615815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 876218146716991035487753 657163610037743276615815)
    ·
      refine ⟨985745415056614914923723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 657163610037743276615815 985745415056614914923723)
      ·
        refine ⟨1478618122584922372385585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 985745415056614914923723 1478618122584922372385585)
        ·
          refine ⟨1108963591938691779289189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1478618122584922372385585 1108963591938691779289189)
          ·
            refine ⟨207930673488504708616723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1108963591938691779289189 207930673488504708616723)
            ·
              refine ⟨311896010232757062925085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 207930673488504708616723 311896010232757062925085)
              ·
                refine ⟨116961003837283898596907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 311896010232757062925085 116961003837283898596907)
                ·
                  refine ⟨175441505755925847895361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 116961003837283898596907 175441505755925847895361)
                  ·
                    refine ⟨131581129316944385921521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 175441505755925847895361 131581129316944385921521)
                    ·
                      refine ⟨98685846987708289441141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 131581129316944385921521 98685846987708289441141)
                      ·
                        rfl

theorem cell23_192190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 1, 3, 1, 2, 2].length) (baseStart_192190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_192190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_192190 prefixEnd_192190 := by exact prefixLift 192190
  have htrace : WordTrace (prefixWord ++ tailWord_192190) baseStart_192190 baseEnd_192190 := by
    simpa [prefixWord, tailWord_192190, baseEnd_192190] using wordTrace_append hprefix tailTrace_192190
  have hstable : (prefixWord ++ tailWord_192190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192190).length < 2 ^ (prefixWord ++ tailWord_192190).sum := by decide
  have hdescent : baseEnd_192190 < baseStart_192190 := by decide
  rcases family_descends (prefixWord ++ tailWord_192190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192199 : List Nat := [1, 1, 4, 1, 1, 1, 3, 5, 1, 3, 2]
def baseStart_192199 : Nat := 118140960795 + 192199 * 2 ^ 59
def prefixEnd_192199 : Nat := 4983230072969 + 3 ^ 40 * 192199 * 2
def baseEnd_192199 : Nat := 98690468313598754228599

theorem tailTrace_192199 : CollatzResearch.WordTrace tailWord_192199 prefixEnd_192199 98690468313598754228599 := by
  unfold tailWord_192199
  simp only [CollatzResearch.WordTrace]
  refine ⟨7010073430703322820979651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4673382287135548547319767 7010073430703322820979651)
  ·
    refine ⟨10515110146054984231469477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7010073430703322820979651 10515110146054984231469477)
    ·
      refine ⟨1971583152385309543400527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10515110146054984231469477 1971583152385309543400527)
      ·
        refine ⟨2957374728577964315100791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1971583152385309543400527 2957374728577964315100791)
        ·
          refine ⟨4436062092866946472651187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2957374728577964315100791 4436062092866946472651187)
          ·
            refine ⟨6654093139300419708976781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4436062092866946472651187 6654093139300419708976781)
            ·
              refine ⟨2495284927237657390866293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6654093139300419708976781 2495284927237657390866293)
              ·
                refine ⟨233932961928530380393715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2495284927237657390866293 233932961928530380393715)
                ·
                  refine ⟨350899442892795570590573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 233932961928530380393715 350899442892795570590573)
                  ·
                    refine ⟨131587291084798338971465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 350899442892795570590573 131587291084798338971465)
                    ·
                      refine ⟨98690468313598754228599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 131587291084798338971465 98690468313598754228599)
                      ·
                        rfl

theorem cell23_192199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 5, 1, 3, 2].length) (baseStart_192199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_192199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_192199 prefixEnd_192199 := by exact prefixLift 192199
  have htrace : WordTrace (prefixWord ++ tailWord_192199) baseStart_192199 baseEnd_192199 := by
    simpa [prefixWord, tailWord_192199, baseEnd_192199] using wordTrace_append hprefix tailTrace_192199
  have hstable : (prefixWord ++ tailWord_192199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192199).length < 2 ^ (prefixWord ++ tailWord_192199).sum := by decide
  have hdescent : baseEnd_192199 < baseStart_192199 := by decide
  rcases family_descends (prefixWord ++ tailWord_192199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192215 : List Nat := [1, 1, 3, 2, 1, 3, 1, 2, 1, 3, 5]
def baseStart_192215 : Nat := 118140960795 + 192215 * 2 ^ 59
def prefixEnd_192215 : Nat := 4983230072969 + 3 ^ 40 * 192215 * 2
def baseEnd_192215 : Nat := 98698684004070691628525

theorem tailTrace_192215 : CollatzResearch.WordTrace tailWord_192215 prefixEnd_192215 98698684004070691628525 := by
  unfold tailWord_192215
  simp only [CollatzResearch.WordTrace]
  refine ⟨7010656998645357553562099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4673771332430238369041399 7010656998645357553562099)
  ·
    refine ⟨10515985497968036330343149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7010656998645357553562099 10515985497968036330343149)
    ·
      refine ⟨3943494561738013623878681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10515985497968036330343149 3943494561738013623878681)
      ·
        refine ⟨2957620921303510217909011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3943494561738013623878681 2957620921303510217909011)
        ·
          refine ⟨4436431381955265326863517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2957620921303510217909011 4436431381955265326863517)
          ·
            refine ⟨1663661768233224497573819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4436431381955265326863517 1663661768233224497573819)
            ·
              refine ⟨2495492652349836746360729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1663661768233224497573819 2495492652349836746360729)
              ·
                refine ⟨1871619489262377559770547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2495492652349836746360729 1871619489262377559770547)
                ·
                  refine ⟨2807429233893566339655821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1871619489262377559770547 2807429233893566339655821)
                  ·
                    refine ⟨1052785962710087377370933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2807429233893566339655821 1052785962710087377370933)
                    ·
                      refine ⟨98698684004070691628525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1052785962710087377370933 98698684004070691628525)
                      ·
                        rfl

theorem cell23_192215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 2, 1, 3, 5].length) (baseStart_192215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_192215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_192215 prefixEnd_192215 := by exact prefixLift 192215
  have htrace : WordTrace (prefixWord ++ tailWord_192215) baseStart_192215 baseEnd_192215 := by
    simpa [prefixWord, tailWord_192215, baseEnd_192215] using wordTrace_append hprefix tailTrace_192215
  have hstable : (prefixWord ++ tailWord_192215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192215).length < 2 ^ (prefixWord ++ tailWord_192215).sum := by decide
  have hdescent : baseEnd_192215 < baseStart_192215 := by decide
  rcases family_descends (prefixWord ++ tailWord_192215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192229 : List Nat := [1, 3, 1, 4, 1, 1, 2, 3, 1, 4, 2]
def baseStart_192229 : Nat := 118140960795 + 192229 * 2 ^ 59
def prefixEnd_192229 : Nat := 4983230072969 + 3 ^ 40 * 192229 * 2
def baseEnd_192229 : Nat := 98705872733233636853461

theorem tailTrace_192229 : CollatzResearch.WordTrace tailWord_192229 prefixEnd_192229 98705872733233636853461 := by
  unfold tailWord_192229
  simp only [CollatzResearch.WordTrace]
  refine ⟨7011167620594637944571741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4674111747063091963047827 7011167620594637944571741)
  ·
    refine ⟨2629187857722989229214403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7011167620594637944571741 2629187857722989229214403)
    ·
      refine ⟨3943781786584483843821605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2629187857722989229214403 3943781786584483843821605)
      ·
        refine ⟨739459084984590720716551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3943781786584483843821605 739459084984590720716551)
        ·
          refine ⟨1109188627476886081074827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 739459084984590720716551 1109188627476886081074827)
          ·
            refine ⟨1663782941215329121612241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1109188627476886081074827 1663782941215329121612241)
            ·
              refine ⟨1247837205911496841209181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1663782941215329121612241 1247837205911496841209181)
              ·
                refine ⟨467938952216811315453443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1247837205911496841209181 467938952216811315453443)
                ·
                  refine ⟨701908428325216973180165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 467938952216811315453443 701908428325216973180165)
                  ·
                    refine ⟨131607830310978182471281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 701908428325216973180165 131607830310978182471281)
                    ·
                      refine ⟨98705872733233636853461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 131607830310978182471281 98705872733233636853461)
                      ·
                        rfl

theorem cell23_192229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 3, 1, 4, 2].length) (baseStart_192229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_192229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_192229 prefixEnd_192229 := by exact prefixLift 192229
  have htrace : WordTrace (prefixWord ++ tailWord_192229) baseStart_192229 baseEnd_192229 := by
    simpa [prefixWord, tailWord_192229, baseEnd_192229] using wordTrace_append hprefix tailTrace_192229
  have hstable : (prefixWord ++ tailWord_192229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192229).length < 2 ^ (prefixWord ++ tailWord_192229).sum := by decide
  have hdescent : baseEnd_192229 < baseStart_192229 := by decide
  rcases family_descends (prefixWord ++ tailWord_192229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192232 : List Nat := [2, 1, 4, 1, 3, 1, 1, 2, 2, 1, 5]
def baseStart_192232 : Nat := 118140960795 + 192232 * 2 ^ 59
def prefixEnd_192232 : Nat := 4983230072969 + 3 ^ 40 * 192232 * 2
def baseEnd_192232 : Nat := 98707413175197125115947

theorem tailTrace_192232 : CollatzResearch.WordTrace tailWord_192232 prefixEnd_192232 98707413175197125115947 := by
  unfold tailWord_192232
  simp only [CollatzResearch.WordTrace]
  refine ⟨3505638519791884728465475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4674184693055846304620633 3505638519791884728465475)
  ·
    refine ⟨5258457779687827092698213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3505638519791884728465475 5258457779687827092698213)
    ·
      refine ⟨985960833691467579880915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5258457779687827092698213 985960833691467579880915)
      ·
        refine ⟨1478941250537201369821373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 985960833691467579880915 1478941250537201369821373)
        ·
          refine ⟨554602968951450513683015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1478941250537201369821373 554602968951450513683015)
          ·
            refine ⟨831904453427175770524523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 554602968951450513683015 831904453427175770524523)
            ·
              refine ⟨1247856680140763655786785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 831904453427175770524523 1247856680140763655786785)
              ·
                refine ⟨935892510105572741840089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1247856680140763655786785 935892510105572741840089)
                ·
                  refine ⟨701919382579179556380067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 935892510105572741840089 701919382579179556380067)
                  ·
                    refine ⟨1052879073868769334570101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 701919382579179556380067 1052879073868769334570101)
                    ·
                      refine ⟨98707413175197125115947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1052879073868769334570101 98707413175197125115947)
                      ·
                        rfl

theorem cell23_192232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 2, 2, 1, 5].length) (baseStart_192232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_192232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_192232 prefixEnd_192232 := by exact prefixLift 192232
  have htrace : WordTrace (prefixWord ++ tailWord_192232) baseStart_192232 baseEnd_192232 := by
    simpa [prefixWord, tailWord_192232, baseEnd_192232] using wordTrace_append hprefix tailTrace_192232
  have hstable : (prefixWord ++ tailWord_192232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192232).length < 2 ^ (prefixWord ++ tailWord_192232).sum := by decide
  have hdescent : baseEnd_192232 < baseStart_192232 := by decide
  rcases family_descends (prefixWord ++ tailWord_192232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192235 : List Nat := [1, 1, 1, 1, 2, 4, 2, 4, 7]
def baseStart_192235 : Nat := 118140960795 + 192235 * 2 ^ 59
def prefixEnd_192235 : Nat := 4983230072969 + 3 ^ 40 * 192235 * 2
def baseEnd_192235 : Nat := 10967661513017845930937

theorem tailTrace_192235 : CollatzResearch.WordTrace tailWord_192235 prefixEnd_192235 10967661513017845930937 := by
  unfold tailWord_192235
  simp only [CollatzResearch.WordTrace]
  refine ⟨7011386458572900969290159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4674257639048600646193439 7011386458572900969290159)
  ·
    refine ⟨10517079687859351453935239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7011386458572900969290159 10517079687859351453935239)
    ·
      refine ⟨15775619531789027180902859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10517079687859351453935239 15775619531789027180902859)
      ·
        refine ⟨23663429297683540771354289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15775619531789027180902859 23663429297683540771354289)
        ·
          refine ⟨17747571973262655578515717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23663429297683540771354289 17747571973262655578515717)
          ·
            refine ⟨3327669744986747920971697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17747571973262655578515717 3327669744986747920971697)
            ·
              refine ⟨2495752308740060940728773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3327669744986747920971697 2495752308740060940728773)
              ·
                refine ⟨467953557888761426386645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2495752308740060940728773 467953557888761426386645)
                ·
                  refine ⟨10967661513017845930937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 467953557888761426386645 10967661513017845930937)
                  ·
                    rfl

theorem cell23_192235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 4, 7].length) (baseStart_192235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_192235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_192235 prefixEnd_192235 := by exact prefixLift 192235
  have htrace : WordTrace (prefixWord ++ tailWord_192235) baseStart_192235 baseEnd_192235 := by
    simpa [prefixWord, tailWord_192235, baseEnd_192235] using wordTrace_append hprefix tailTrace_192235
  have hstable : (prefixWord ++ tailWord_192235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192235).length < 2 ^ (prefixWord ++ tailWord_192235).sum := by decide
  have hdescent : baseEnd_192235 < baseStart_192235 := by decide
  rcases family_descends (prefixWord ++ tailWord_192235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192246 : List Nat := [5, 1, 1, 1, 1, 4, 1, 2, 1, 4, 2]
def baseStart_192246 : Nat := 118140960795 + 192246 * 2 ^ 59
def prefixEnd_192246 : Nat := 4983230072969 + 3 ^ 40 * 192246 * 2
def baseEnd_192246 : Nat := 98714601904360070340883

theorem tailTrace_192246 : CollatzResearch.WordTrace tailWord_192246 prefixEnd_192246 98714601904360070340883 := by
  unfold tailWord_192246
  simp only [CollatzResearch.WordTrace]
  refine ⟨438236728845815615496287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4674525107688699898627061 438236728845815615496287)
  ·
    refine ⟨657355093268723423244431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 438236728845815615496287 657355093268723423244431)
    ·
      refine ⟨986032639903085134866647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 657355093268723423244431 986032639903085134866647)
      ·
        refine ⟨1479048959854627702299971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 986032639903085134866647 1479048959854627702299971)
        ·
          refine ⟨2218573439781941553449957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1479048959854627702299971 2218573439781941553449957)
          ·
            refine ⟨415982519959114041271867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2218573439781941553449957 415982519959114041271867)
            ·
              refine ⟨623973779938671061907801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 415982519959114041271867 623973779938671061907801)
              ·
                refine ⟨467980334954003296430851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 623973779938671061907801 467980334954003296430851)
                ·
                  refine ⟨701970502431004944646277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 467980334954003296430851 701970502431004944646277)
                  ·
                    refine ⟨131619469205813427121177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 701970502431004944646277 131619469205813427121177)
                    ·
                      refine ⟨98714601904360070340883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 131619469205813427121177 98714601904360070340883)
                      ·
                        rfl

theorem cell23_192246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 2, 1, 4, 2].length) (baseStart_192246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_192246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_192246 prefixEnd_192246 := by exact prefixLift 192246
  have htrace : WordTrace (prefixWord ++ tailWord_192246) baseStart_192246 baseEnd_192246 := by
    simpa [prefixWord, tailWord_192246, baseEnd_192246] using wordTrace_append hprefix tailTrace_192246
  have hstable : (prefixWord ++ tailWord_192246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192246).length < 2 ^ (prefixWord ++ tailWord_192246).sum := by decide
  have hdescent : baseEnd_192246 < baseStart_192246 := by decide
  rcases family_descends (prefixWord ++ tailWord_192246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192265 : List Nat := [1, 2, 1, 1, 3, 2, 1, 2, 3, 7]
def baseStart_192265 : Nat := 118140960795 + 192265 * 2 ^ 59
def prefixEnd_192265 : Nat := 4983230072969 + 3 ^ 40 * 192265 * 2
def baseEnd_192265 : Nat := 32908119345598498667765

theorem tailTrace_192265 : CollatzResearch.WordTrace tailWord_192265 prefixEnd_192265 32908119345598498667765 := by
  unfold tailWord_192265
  simp only [CollatzResearch.WordTrace]
  refine ⟨7012480648464216092882249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4674987098976144061921499 7012480648464216092882249)
  ·
    refine ⟨5259360486348162069661687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7012480648464216092882249 5259360486348162069661687)
    ·
      refine ⟨7889040729522243104492531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5259360486348162069661687 7889040729522243104492531)
      ·
        refine ⟨11833561094283364656738797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7889040729522243104492531 11833561094283364656738797)
        ·
          refine ⟨4437585410356261746277049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11833561094283364656738797 4437585410356261746277049)
          ·
            refine ⟨3328189057767196309707787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4437585410356261746277049 3328189057767196309707787)
            ·
              refine ⟨4992283586650794464561681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3328189057767196309707787 4992283586650794464561681)
              ·
                refine ⟨3744212689988095848421261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4992283586650794464561681 3744212689988095848421261)
                ·
                  refine ⟨1404079758745535943157973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3744212689988095848421261 1404079758745535943157973)
                  ·
                    refine ⟨32908119345598498667765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1404079758745535943157973 32908119345598498667765)
                    ·
                      rfl

theorem cell23_192265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 2, 3, 7].length) (baseStart_192265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_192265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_192265 prefixEnd_192265 := by exact prefixLift 192265
  have htrace : WordTrace (prefixWord ++ tailWord_192265) baseStart_192265 baseEnd_192265 := by
    simpa [prefixWord, tailWord_192265, baseEnd_192265] using wordTrace_append hprefix tailTrace_192265
  have hstable : (prefixWord ++ tailWord_192265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192265).length < 2 ^ (prefixWord ++ tailWord_192265).sum := by decide
  have hdescent : baseEnd_192265 < baseStart_192265 := by decide
  rcases family_descends (prefixWord ++ tailWord_192265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192275 : List Nat := [1, 1, 1, 2, 1, 3, 2, 3, 1, 1, 7]
def baseStart_192275 : Nat := 118140960795 + 192275 * 2 ^ 59
def prefixEnd_192275 : Nat := 4983230072969 + 3 ^ 40 * 192275 * 2
def baseEnd_192275 : Nat := 98729492843340456878249

theorem tailTrace_192275 : CollatzResearch.WordTrace tailWord_192275 prefixEnd_192275 98729492843340456878249 := by
  unfold tailWord_192275
  simp only [CollatzResearch.WordTrace]
  refine ⟨7012845378427987800746279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4675230252285325200497519 7012845378427987800746279)
  ·
    refine ⟨10519268067641981701119419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7012845378427987800746279 10519268067641981701119419)
    ·
      refine ⟨15778902101462972551679129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10519268067641981701119419 15778902101462972551679129)
      ·
        refine ⟨11834176576097229413759347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15778902101462972551679129 11834176576097229413759347)
        ·
          refine ⟨17751264864145844120639021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11834176576097229413759347 17751264864145844120639021)
          ·
            refine ⟨6656724324054691545239633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17751264864145844120639021 6656724324054691545239633)
            ·
              refine ⟨4992543243041018658929725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6656724324054691545239633 4992543243041018658929725)
              ·
                refine ⟨1872203716140381997098647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4992543243041018658929725 1872203716140381997098647)
                ·
                  refine ⟨2808305574210572995647971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1872203716140381997098647 2808305574210572995647971)
                  ·
                    refine ⟨4212458361315859493471957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2808305574210572995647971 4212458361315859493471957)
                    ·
                      refine ⟨98729492843340456878249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 4212458361315859493471957 98729492843340456878249)
                      ·
                        rfl

theorem cell23_192275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 3, 1, 1, 7].length) (baseStart_192275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_192275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_192275 prefixEnd_192275 := by exact prefixLift 192275
  have htrace : WordTrace (prefixWord ++ tailWord_192275) baseStart_192275 baseEnd_192275 := by
    simpa [prefixWord, tailWord_192275, baseEnd_192275] using wordTrace_append hprefix tailTrace_192275
  have hstable : (prefixWord ++ tailWord_192275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192275).length < 2 ^ (prefixWord ++ tailWord_192275).sum := by decide
  have hdescent : baseEnd_192275 < baseStart_192275 := by decide
  rcases family_descends (prefixWord ++ tailWord_192275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192279 : List Nat := [1, 1, 3, 4, 2, 2, 1, 1, 2, 3, 3]
def baseStart_192279 : Nat := 118140960795 + 192279 * 2 ^ 59
def prefixEnd_192279 : Nat := 4983230072969 + 3 ^ 40 * 192279 * 2
def baseEnd_192279 : Nat := 98731546765958441228231

theorem tailTrace_192279 : CollatzResearch.WordTrace tailWord_192279 prefixEnd_192279 98731546765958441228231 := by
  unfold tailWord_192279
  simp only [CollatzResearch.WordTrace]
  refine ⟨7012991270413496483891891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4675327513608997655927927 7012991270413496483891891)
  ·
    refine ⟨10519486905620244725837837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7012991270413496483891891 10519486905620244725837837)
    ·
      refine ⟨3944807589607591772189189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10519486905620244725837837 3944807589607591772189189)
      ·
        refine ⟨739651423051423457285473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3944807589607591772189189 739651423051423457285473)
        ·
          refine ⟨554738567288567592964105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 739651423051423457285473 554738567288567592964105)
          ·
            refine ⟨416053925466425694723079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 554738567288567592964105 416053925466425694723079)
            ·
              refine ⟨624080888199638542084619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 416053925466425694723079 624080888199638542084619)
              ·
                refine ⟨936121332299457813126929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 624080888199638542084619 936121332299457813126929)
                ·
                  refine ⟨702090999224593359845197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 936121332299457813126929 702090999224593359845197)
                  ·
                    refine ⟨263284124709222509941949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 702090999224593359845197 263284124709222509941949)
                    ·
                      refine ⟨98731546765958441228231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 263284124709222509941949 98731546765958441228231)
                      ·
                        rfl

theorem cell23_192279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 1, 2, 3, 3].length) (baseStart_192279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_192279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_192279 prefixEnd_192279 := by exact prefixLift 192279
  have htrace : WordTrace (prefixWord ++ tailWord_192279) baseStart_192279 baseEnd_192279 := by
    simpa [prefixWord, tailWord_192279, baseEnd_192279] using wordTrace_append hprefix tailTrace_192279
  have hstable : (prefixWord ++ tailWord_192279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192279).length < 2 ^ (prefixWord ++ tailWord_192279).sum := by decide
  have hdescent : baseEnd_192279 < baseStart_192279 := by decide
  rcases family_descends (prefixWord ++ tailWord_192279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192329 : List Nat := [1, 2, 1, 1, 2, 4, 4, 1, 3, 4]
def baseStart_192329 : Nat := 118140960795 + 192329 * 2 ^ 59
def prefixEnd_192329 : Nat := 4983230072969 + 3 ^ 40 * 192329 * 2
def baseEnd_192329 : Nat := 32919073599561081867667

theorem tailTrace_192329 : CollatzResearch.WordTrace tailWord_192329 prefixEnd_192329 32919073599561081867667 := by
  unfold tailWord_192329
  simp only [CollatzResearch.WordTrace]
  refine ⟨7014814920232355023212041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4676543280154903348808027 7014814920232355023212041)
  ·
    refine ⟨5261111190174266267409031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7014814920232355023212041 5261111190174266267409031)
    ·
      refine ⟨7891666785261399401113547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5261111190174266267409031 7891666785261399401113547)
      ·
        refine ⟨11837500177892099101670321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7891666785261399401113547 11837500177892099101670321)
        ·
          refine ⟨8878125133419074326252741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11837500177892099101670321 8878125133419074326252741)
          ·
            refine ⟨1664648462516076436172389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8878125133419074326252741 1664648462516076436172389)
            ·
              refine ⟨312121586721764331782323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1664648462516076436172389 312121586721764331782323)
              ·
                refine ⟨468182380082646497673485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 312121586721764331782323 468182380082646497673485)
                ·
                  refine ⟨175568392530992436627557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 468182380082646497673485 175568392530992436627557)
                  ·
                    refine ⟨32919073599561081867667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 175568392530992436627557 32919073599561081867667)
                    ·
                      rfl

theorem cell23_192329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 4, 1, 3, 4].length) (baseStart_192329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_192329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_192329 prefixEnd_192329 := by exact prefixLift 192329
  have htrace : WordTrace (prefixWord ++ tailWord_192329) baseStart_192329 baseEnd_192329 := by
    simpa [prefixWord, tailWord_192329, baseEnd_192329] using wordTrace_append hprefix tailTrace_192329
  have hstable : (prefixWord ++ tailWord_192329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192329).length < 2 ^ (prefixWord ++ tailWord_192329).sum := by decide
  have hdescent : baseEnd_192329 < baseStart_192329 := by decide
  rcases family_descends (prefixWord ++ tailWord_192329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192409 : List Nat := [1, 2, 1, 2, 1, 3, 2, 1, 2, 6, 2]
def baseStart_192409 : Nat := 118140960795 + 192409 * 2 ^ 59
def prefixEnd_192409 : Nat := 4983230072969 + 3 ^ 40 * 192409 * 2
def baseEnd_192409 : Nat := 98798299251042932602633

theorem tailTrace_192409 : CollatzResearch.WordTrace tailWord_192409 prefixEnd_192409 98798299251042932602633 := by
  unfold tailWord_192409
  simp only [CollatzResearch.WordTrace]
  refine ⟨7017732759942528686124281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4678488506628352457416187 7017732759942528686124281)
  ·
    refine ⟨5263299569956896514593211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7017732759942528686124281 5263299569956896514593211)
    ·
      refine ⟨7894949354935344771889817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5263299569956896514593211 7894949354935344771889817)
      ·
        refine ⟨5921212016201508578917363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7894949354935344771889817 5921212016201508578917363)
        ·
          refine ⟨8881818024302262868376045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5921212016201508578917363 8881818024302262868376045)
          ·
            refine ⟨3330681759113348575641017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8881818024302262868376045 3330681759113348575641017)
            ·
              refine ⟨2498011319335011431730763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3330681759113348575641017 2498011319335011431730763)
              ·
                refine ⟨3747016979002517147596145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2498011319335011431730763 3747016979002517147596145)
                ·
                  refine ⟨2810262734251887860697109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3747016979002517147596145 2810262734251887860697109)
                  ·
                    refine ⟨131731065668057243470177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2810262734251887860697109 131731065668057243470177)
                    ·
                      refine ⟨98798299251042932602633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 131731065668057243470177 98798299251042932602633)
                      ·
                        rfl

theorem cell23_192409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 1, 2, 6, 2].length) (baseStart_192409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_192409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_192409 prefixEnd_192409 := by exact prefixLift 192409
  have htrace : WordTrace (prefixWord ++ tailWord_192409) baseStart_192409 baseEnd_192409 := by
    simpa [prefixWord, tailWord_192409, baseEnd_192409] using wordTrace_append hprefix tailTrace_192409
  have hstable : (prefixWord ++ tailWord_192409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192409).length < 2 ^ (prefixWord ++ tailWord_192409).sum := by decide
  have hdescent : baseEnd_192409 < baseStart_192409 := by decide
  rcases family_descends (prefixWord ++ tailWord_192409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192413 : List Nat := [1, 4, 2, 1, 2, 3, 2, 1, 2, 3, 2]
def baseStart_192413 : Nat := 118140960795 + 192413 * 2 ^ 59
def prefixEnd_192413 : Nat := 4983230072969 + 3 ^ 40 * 192413 * 2
def baseEnd_192413 : Nat := 98800353173660916952615

theorem tailTrace_192413 : CollatzResearch.WordTrace tailWord_192413 prefixEnd_192413 98800353173660916952615 := by
  unfold tailWord_192413
  simp only [CollatzResearch.WordTrace]
  refine ⟨7017878651928037369269893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4678585767952024912846595 7017878651928037369269893)
  ·
    refine ⟨1315852247236507006738105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7017878651928037369269893 1315852247236507006738105)
    ·
      refine ⟨986889185427380255053579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1315852247236507006738105 986889185427380255053579)
      ·
        refine ⟨1480333778141070382580369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 986889185427380255053579 1480333778141070382580369)
        ·
          refine ⟨1110250333605802786935277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1480333778141070382580369 1110250333605802786935277)
          ·
            refine ⟨416343875102176045100729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1110250333605802786935277 416343875102176045100729)
            ·
              refine ⟨312257906326632033825547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 416343875102176045100729 312257906326632033825547)
              ·
                refine ⟨468386859489948050738321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 312257906326632033825547 468386859489948050738321)
                ·
                  refine ⟨351290144617461038053741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 468386859489948050738321 351290144617461038053741)
                  ·
                    refine ⟨131733804231547889270153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 351290144617461038053741 131733804231547889270153)
                    ·
                      refine ⟨98800353173660916952615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 131733804231547889270153 98800353173660916952615)
                      ·
                        rfl

theorem cell23_192413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 2, 1, 2, 3, 2].length) (baseStart_192413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_192413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_192413 prefixEnd_192413 := by exact prefixLift 192413
  have htrace : WordTrace (prefixWord ++ tailWord_192413) baseStart_192413 baseEnd_192413 := by
    simpa [prefixWord, tailWord_192413, baseEnd_192413] using wordTrace_append hprefix tailTrace_192413
  have hstable : (prefixWord ++ tailWord_192413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192413).length < 2 ^ (prefixWord ++ tailWord_192413).sum := by decide
  have hdescent : baseEnd_192413 < baseStart_192413 := by decide
  rcases family_descends (prefixWord ++ tailWord_192413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192423 : List Nat := [1, 1, 6, 1, 2, 2, 3, 1, 1, 5]
def baseStart_192423 : Nat := 118140960795 + 192423 * 2 ^ 59
def prefixEnd_192423 : Nat := 4983230072969 + 3 ^ 40 * 192423 * 2
def baseEnd_192423 : Nat := 32935162660068625942523

theorem tailTrace_192423 : CollatzResearch.WordTrace tailWord_192423 prefixEnd_192423 32935162660068625942523 := by
  unfold tailWord_192423
  simp only [CollatzResearch.WordTrace]
  refine ⟨7018243381891809077133923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4678828921261206051422615 7018243381891809077133923)
  ·
    refine ⟨10527365072837713615700885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7018243381891809077133923 10527365072837713615700885)
    ·
      refine ⟨493470237789267825735979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 10527365072837713615700885 493470237789267825735979)
      ·
        refine ⟨740205356683901738603969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 493470237789267825735979 740205356683901738603969)
        ·
          refine ⟨555154017512926303952977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 740205356683901738603969 555154017512926303952977)
          ·
            refine ⟨416365513134694727964733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 555154017512926303952977 416365513134694727964733)
            ·
              refine ⟨156137067425510522986775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 416365513134694727964733 156137067425510522986775)
              ·
                refine ⟨234205601138265784480163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 156137067425510522986775 234205601138265784480163)
                ·
                  refine ⟨351308401707398676720245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 234205601138265784480163 351308401707398676720245)
                  ·
                    refine ⟨32935162660068625942523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 351308401707398676720245 32935162660068625942523)
                    ·
                      rfl

theorem cell23_192423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 3, 1, 1, 5].length) (baseStart_192423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_192423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_192423 prefixEnd_192423 := by exact prefixLift 192423
  have htrace : WordTrace (prefixWord ++ tailWord_192423) baseStart_192423 baseEnd_192423 := by
    simpa [prefixWord, tailWord_192423, baseEnd_192423] using wordTrace_append hprefix tailTrace_192423
  have hstable : (prefixWord ++ tailWord_192423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192423).length < 2 ^ (prefixWord ++ tailWord_192423).sum := by decide
  have hdescent : baseEnd_192423 < baseStart_192423 := by decide
  rcases family_descends (prefixWord ++ tailWord_192423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192437 : List Nat := [1, 3, 3, 2, 1, 4, 2, 2, 1, 1, 3]
def baseStart_192437 : Nat := 118140960795 + 192437 * 2 ^ 59
def prefixEnd_192437 : Nat := 4983230072969 + 3 ^ 40 * 192437 * 2
def baseEnd_192437 : Nat := 98812676709368823052505

theorem tailTrace_192437 : CollatzResearch.WordTrace tailWord_192437 prefixEnd_192437 98812676709368823052505 := by
  unfold tailWord_192437
  simp only [CollatzResearch.WordTrace]
  refine ⟨7018754003841089468143565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4679169335894059645429043 7018754003841089468143565)
  ·
    refine ⟨2632032751440408550553837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7018754003841089468143565 2632032751440408550553837)
    ·
      refine ⟨987012281790153206457689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2632032751440408550553837 987012281790153206457689)
      ·
        refine ⟨740259211342614904843267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 987012281790153206457689 740259211342614904843267)
        ·
          refine ⟨1110388817013922357264901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 740259211342614904843267 1110388817013922357264901)
          ·
            refine ⟨208197903190110441987169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1110388817013922357264901 208197903190110441987169)
            ·
              refine ⟨156148427392582831490377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 208197903190110441987169 156148427392582831490377)
              ·
                refine ⟨117111320544437123617783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 156148427392582831490377 117111320544437123617783)
                ·
                  refine ⟨175666980816655685426675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 117111320544437123617783 175666980816655685426675)
                  ·
                    refine ⟨263500471224983528140013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 175666980816655685426675 263500471224983528140013)
                    ·
                      refine ⟨98812676709368823052505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 263500471224983528140013 98812676709368823052505)
                      ·
                        rfl

theorem cell23_192437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 2, 2, 1, 1, 3].length) (baseStart_192437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_192437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_192437 prefixEnd_192437 := by exact prefixLift 192437
  have htrace : WordTrace (prefixWord ++ tailWord_192437) baseStart_192437 baseEnd_192437 := by
    simpa [prefixWord, tailWord_192437, baseEnd_192437] using wordTrace_append hprefix tailTrace_192437
  have hstable : (prefixWord ++ tailWord_192437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192437).length < 2 ^ (prefixWord ++ tailWord_192437).sum := by decide
  have hdescent : baseEnd_192437 < baseStart_192437 := by decide
  rcases family_descends (prefixWord ++ tailWord_192437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192442 : List Nat := [3, 1, 1, 1, 2, 1, 2, 1, 2, 2, 7]
def baseStart_192442 : Nat := 118140960795 + 192442 * 2 ^ 59
def prefixEnd_192442 : Nat := 4983230072969 + 3 ^ 40 * 192442 * 2
def baseEnd_192442 : Nat := 98815244112641303489981

theorem tailTrace_192442 : CollatzResearch.WordTrace tailWord_192442 prefixEnd_192442 98815244112641303489981 := by
  unfold tailWord_192442
  simp only [CollatzResearch.WordTrace]
  refine ⟨1754734092205743830518895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4679290912548650214717053 1754734092205743830518895)
  ·
    refine ⟨2632101138308615745778343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1754734092205743830518895 2632101138308615745778343)
    ·
      refine ⟨3948151707462923618667515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2632101138308615745778343 3948151707462923618667515)
      ·
        refine ⟨5922227561194385428001273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3948151707462923618667515 5922227561194385428001273)
        ·
          refine ⟨4441670670895789071000955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5922227561194385428001273 4441670670895789071000955)
          ·
            refine ⟨6662506006343683606501433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4441670670895789071000955 6662506006343683606501433)
            ·
              refine ⟨4996879504757762704876075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6662506006343683606501433 4996879504757762704876075)
              ·
                refine ⟨7495319257136644057314113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4996879504757762704876075 7495319257136644057314113)
                ·
                  refine ⟨5621489442852483042985585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7495319257136644057314113 5621489442852483042985585)
                  ·
                    refine ⟨4216117082139362282239189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5621489442852483042985585 4216117082139362282239189)
                    ·
                      refine ⟨98815244112641303489981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 4216117082139362282239189 98815244112641303489981)
                      ·
                        rfl

theorem cell23_192442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 2, 2, 7].length) (baseStart_192442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_192442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_192442 prefixEnd_192442 := by exact prefixLift 192442
  have htrace : WordTrace (prefixWord ++ tailWord_192442) baseStart_192442 baseEnd_192442 := by
    simpa [prefixWord, tailWord_192442, baseEnd_192442] using wordTrace_append hprefix tailTrace_192442
  have hstable : (prefixWord ++ tailWord_192442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192442).length < 2 ^ (prefixWord ++ tailWord_192442).sum := by decide
  have hdescent : baseEnd_192442 < baseStart_192442 := by decide
  rcases family_descends (prefixWord ++ tailWord_192442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192446 : List Nat := [4, 2, 1, 1, 1, 3, 1, 2, 3, 2, 3]
def baseStart_192446 : Nat := 118140960795 + 192446 * 2 ^ 59
def prefixEnd_192446 : Nat := 4983230072969 + 3 ^ 40 * 192446 * 2
def baseEnd_192446 : Nat := 98817298035259287839963

theorem tailTrace_192446 : CollatzResearch.WordTrace tailWord_192446 prefixEnd_192446 98817298035259287839963 := by
  unfold tailWord_192446
  simp only [CollatzResearch.WordTrace]
  refine ⟨877385282601060500652649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4679388173872322670147461 877385282601060500652649)
  ·
    refine ⟨658038961950795375489487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 877385282601060500652649 658038961950795375489487)
    ·
      refine ⟨987058442926193063234231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 658038961950795375489487 987058442926193063234231)
      ·
        refine ⟨1480587664389289594851347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 987058442926193063234231 1480587664389289594851347)
        ·
          refine ⟨2220881496583934392277021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1480587664389289594851347 2220881496583934392277021)
          ·
            refine ⟨832830561218975397103883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2220881496583934392277021 832830561218975397103883)
            ·
              refine ⟨1249245841828463095655825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 832830561218975397103883 1249245841828463095655825)
              ·
                refine ⟨936934381371347321741869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1249245841828463095655825 936934381371347321741869)
                ·
                  refine ⟨351350393014255245653201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 936934381371347321741869 351350393014255245653201)
                  ·
                    refine ⟨263512794760691434239901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 351350393014255245653201 263512794760691434239901)
                    ·
                      refine ⟨98817298035259287839963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 263512794760691434239901 98817298035259287839963)
                      ·
                        rfl

theorem cell23_192446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 2, 3, 2, 3].length) (baseStart_192446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_192446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_192446 prefixEnd_192446 := by exact prefixLift 192446
  have htrace : WordTrace (prefixWord ++ tailWord_192446) baseStart_192446 baseEnd_192446 := by
    simpa [prefixWord, tailWord_192446, baseEnd_192446] using wordTrace_append hprefix tailTrace_192446
  have hstable : (prefixWord ++ tailWord_192446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192446).length < 2 ^ (prefixWord ++ tailWord_192446).sum := by decide
  have hdescent : baseEnd_192446 < baseStart_192446 := by decide
  rcases family_descends (prefixWord ++ tailWord_192446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192456 : List Nat := [2, 1, 3, 1, 4, 2, 2, 1, 1, 2, 4]
def baseStart_192456 : Nat := 118140960795 + 192456 * 2 ^ 59
def prefixEnd_192456 : Nat := 4983230072969 + 3 ^ 40 * 192456 * 2
def baseEnd_192456 : Nat := 98822432841804248714917

theorem tailTrace_192456 : CollatzResearch.WordTrace tailWord_192456 prefixEnd_192456 98822432841804248714917 := by
  unfold tailWord_192456
  simp only [CollatzResearch.WordTrace]
  refine ⟨3509723495386127856542611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4679631327181503808723481 3509723495386127856542611)
  ·
    refine ⟨5264585243079191784813917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3509723495386127856542611 5264585243079191784813917)
    ·
      refine ⟨1974219466154696919305219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5264585243079191784813917 1974219466154696919305219)
      ·
        refine ⟨2961329199232045378957829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1974219466154696919305219 2961329199232045378957829)
        ·
          refine ⟨555249224856008508554593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2961329199232045378957829 555249224856008508554593)
          ·
            refine ⟨416436918642006381415945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 555249224856008508554593 416436918642006381415945)
            ·
              refine ⟨312327688981504786061959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 416436918642006381415945 312327688981504786061959)
              ·
                refine ⟨468491533472257179092939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 312327688981504786061959 468491533472257179092939)
                ·
                  refine ⟨702737300208385768639409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 468491533472257179092939 702737300208385768639409)
                  ·
                    refine ⟨527052975156289326479557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 702737300208385768639409 527052975156289326479557)
                    ·
                      refine ⟨98822432841804248714917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 527052975156289326479557 98822432841804248714917)
                      ·
                        rfl

theorem cell23_192456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 2, 1, 1, 2, 4].length) (baseStart_192456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_192456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_192456 prefixEnd_192456 := by exact prefixLift 192456
  have htrace : WordTrace (prefixWord ++ tailWord_192456) baseStart_192456 baseEnd_192456 := by
    simpa [prefixWord, tailWord_192456, baseEnd_192456] using wordTrace_append hprefix tailTrace_192456
  have hstable : (prefixWord ++ tailWord_192456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192456).length < 2 ^ (prefixWord ++ tailWord_192456).sum := by decide
  have hdescent : baseEnd_192456 < baseStart_192456 := by decide
  rcases family_descends (prefixWord ++ tailWord_192456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192477 : List Nat := [1, 4, 3, 1, 4, 1, 2, 1, 1, 1, 4]
def baseStart_192477 : Nat := 118140960795 + 192477 * 2 ^ 59
def prefixEnd_192477 : Nat := 4983230072969 + 3 ^ 40 * 192477 * 2
def baseEnd_192477 : Nat := 98833215935548666552321

theorem tailTrace_192477 : CollatzResearch.WordTrace tailWord_192477 prefixEnd_192477 98833215935548666552321 := by
  unfold tailWord_192477
  simp only [CollatzResearch.WordTrace]
  refine ⟨7020212923696176299599685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4680141949130784199733123 7020212923696176299599685)
  ·
    refine ⟨1316289923193033056174941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7020212923696176299599685 1316289923193033056174941)
    ·
      refine ⟨493608721197387396065603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1316289923193033056174941 493608721197387396065603)
      ·
        refine ⟨740413081796081094098405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 493608721197387396065603 740413081796081094098405)
        ·
          refine ⟨138827452836765205143451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 740413081796081094098405 138827452836765205143451)
          ·
            refine ⟨208241179255147807715177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138827452836765205143451 208241179255147807715177)
            ·
              refine ⟨156180884441360855786383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 208241179255147807715177 156180884441360855786383)
              ·
                refine ⟨234271326662041283679575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 156180884441360855786383 234271326662041283679575)
                ·
                  refine ⟨351406989993061925519363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 234271326662041283679575 351406989993061925519363)
                  ·
                    refine ⟨527110484989592888279045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 351406989993061925519363 527110484989592888279045)
                    ·
                      refine ⟨98833215935548666552321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 527110484989592888279045 98833215935548666552321)
                      ·
                        rfl

theorem cell23_192477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 2, 1, 1, 1, 4].length) (baseStart_192477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_192477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_192477 prefixEnd_192477 := by exact prefixLift 192477
  have htrace : WordTrace (prefixWord ++ tailWord_192477) baseStart_192477 baseEnd_192477 := by
    simpa [prefixWord, tailWord_192477, baseEnd_192477] using wordTrace_append hprefix tailTrace_192477
  have hstable : (prefixWord ++ tailWord_192477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192477).length < 2 ^ (prefixWord ++ tailWord_192477).sum := by decide
  have hdescent : baseEnd_192477 < baseStart_192477 := by decide
  rcases family_descends (prefixWord ++ tailWord_192477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192509 : List Nat := [1, 4, 1, 1, 1, 2, 4, 1, 2, 6]
def baseStart_192509 : Nat := 118140960795 + 192509 * 2 ^ 59
def prefixEnd_192509 : Nat := 4983230072969 + 3 ^ 40 * 192509 * 2
def baseEnd_192509 : Nat := 32949882438830847117391

theorem tailTrace_192509 : CollatzResearch.WordTrace tailWord_192509 prefixEnd_192509 32949882438830847117391 := by
  unfold tailWord_192509
  simp only [CollatzResearch.WordTrace]
  refine ⟨7021380059580245764764581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4680920039720163843176387 7021380059580245764764581)
  ·
    refine ⟨1316508761171296080893359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7021380059580245764764581 1316508761171296080893359)
    ·
      refine ⟨1974763141756944121340039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1316508761171296080893359 1974763141756944121340039)
      ·
        refine ⟨2962144712635416182010059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1974763141756944121340039 2962144712635416182010059)
        ·
          refine ⟨4443217068953124273015089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2962144712635416182010059 4443217068953124273015089)
          ·
            refine ⟨3332412801714843204761317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4443217068953124273015089 3332412801714843204761317)
            ·
              refine ⟨624827400321533100892747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3332412801714843204761317 624827400321533100892747)
              ·
                refine ⟨937241100482299651339121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 624827400321533100892747 937241100482299651339121)
                ·
                  refine ⟨702930825361724738504341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 937241100482299651339121 702930825361724738504341)
                  ·
                    refine ⟨32949882438830847117391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 702930825361724738504341 32949882438830847117391)
                    ·
                      rfl

theorem cell23_192509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 1, 2, 6].length) (baseStart_192509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_192509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_192509 prefixEnd_192509 := by exact prefixLift 192509
  have htrace : WordTrace (prefixWord ++ tailWord_192509) baseStart_192509 baseEnd_192509 := by
    simpa [prefixWord, tailWord_192509, baseEnd_192509] using wordTrace_append hprefix tailTrace_192509
  have hstable : (prefixWord ++ tailWord_192509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192509).length < 2 ^ (prefixWord ++ tailWord_192509).sum := by decide
  have hdescent : baseEnd_192509 < baseStart_192509 := by decide
  rcases family_descends (prefixWord ++ tailWord_192509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192510 : List Nat := [4, 2, 2, 2, 1, 3, 1, 1, 1, 3, 3]
def baseStart_192510 : Nat := 118140960795 + 192510 * 2 ^ 59
def prefixEnd_192510 : Nat := 4983230072969 + 3 ^ 40 * 192510 * 2
def baseEnd_192510 : Nat := 98850160797147037439669

theorem tailTrace_192510 : CollatzResearch.WordTrace tailWord_192510 prefixEnd_192510 98850160797147037439669 := by
  unfold tailWord_192510
  simp only [CollatzResearch.WordTrace]
  refine ⟨877677066572077866943873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4680944355051081957033989 877677066572077866943873)
  ·
    refine ⟨658257799929058400207905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 877677066572077866943873 658257799929058400207905)
    ·
      refine ⟨493693349946793800155929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 658257799929058400207905 493693349946793800155929)
      ·
        refine ⟨370270012460095350116947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 493693349946793800155929 370270012460095350116947)
        ·
          refine ⟨555405018690143025175421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 370270012460095350116947 555405018690143025175421)
          ·
            refine ⟨208276882008803634440783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 555405018690143025175421 208276882008803634440783)
            ·
              refine ⟨312415323013205451661175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 208276882008803634440783 312415323013205451661175)
              ·
                refine ⟨468622984519808177491763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 312415323013205451661175 468622984519808177491763)
                ·
                  refine ⟨702934476779712266237645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 468622984519808177491763 702934476779712266237645)
                  ·
                    refine ⟨263600428792392099839117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 702934476779712266237645 263600428792392099839117)
                    ·
                      refine ⟨98850160797147037439669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 263600428792392099839117 98850160797147037439669)
                      ·
                        rfl

theorem cell23_192510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_192510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_192510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_192510 prefixEnd_192510 := by exact prefixLift 192510
  have htrace : WordTrace (prefixWord ++ tailWord_192510) baseStart_192510 baseEnd_192510 := by
    simpa [prefixWord, tailWord_192510, baseEnd_192510] using wordTrace_append hprefix tailTrace_192510
  have hstable : (prefixWord ++ tailWord_192510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192510).length < 2 ^ (prefixWord ++ tailWord_192510).sum := by decide
  have hdescent : baseEnd_192510 < baseStart_192510 := by decide
  rcases family_descends (prefixWord ++ tailWord_192510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192609 : List Nat := [1, 2, 3, 1, 1, 2, 1, 1, 1, 5, 5]
def baseStart_192609 : Nat := 118140960795 + 192609 * 2 ^ 59
def prefixEnd_192609 : Nat := 4983230072969 + 3 ^ 40 * 192609 * 2
def baseEnd_192609 : Nat := 98900995381942150101713

theorem tailTrace_192609 : CollatzResearch.WordTrace tailWord_192609 prefixEnd_192609 98900995381942150101713 := by
  unfold tailWord_192609
  simp only [CollatzResearch.WordTrace]
  refine ⟨7025027359217962843404881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4683351572811975228936587 7025027359217962843404881)
  ·
    refine ⟨5268770519413472132553661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7025027359217962843404881 5268770519413472132553661)
    ·
      refine ⟨1975788944780052049707623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5268770519413472132553661 1975788944780052049707623)
      ·
        refine ⟨2963683417170078074561435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1975788944780052049707623 2963683417170078074561435)
        ·
          refine ⟨4445525125755117111842153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2963683417170078074561435 4445525125755117111842153)
          ·
            refine ⟨3334143844316337833881615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4445525125755117111842153 3334143844316337833881615)
            ·
              refine ⟨5001215766474506750822423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3334143844316337833881615 5001215766474506750822423)
              ·
                refine ⟨7501823649711760126233635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5001215766474506750822423 7501823649711760126233635)
                ·
                  refine ⟨11252735474567640189350453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7501823649711760126233635 11252735474567640189350453)
                  ·
                    refine ⟨1054943950740716267751605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11252735474567640189350453 1054943950740716267751605)
                    ·
                      refine ⟨98900995381942150101713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1054943950740716267751605 98900995381942150101713)
                      ·
                        rfl

theorem cell23_192609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 5, 5].length) (baseStart_192609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_192609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_192609 prefixEnd_192609 := by exact prefixLift 192609
  have htrace : WordTrace (prefixWord ++ tailWord_192609) baseStart_192609 baseEnd_192609 := by
    simpa [prefixWord, tailWord_192609, baseEnd_192609] using wordTrace_append hprefix tailTrace_192609
  have hstable : (prefixWord ++ tailWord_192609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192609).length < 2 ^ (prefixWord ++ tailWord_192609).sum := by decide
  have hdescent : baseEnd_192609 < baseStart_192609 := by decide
  rcases family_descends (prefixWord ++ tailWord_192609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192623 : List Nat := [1, 1, 2, 1, 3, 5, 1, 1, 2, 4, 2]
def baseStart_192623 : Nat := 118140960795 + 192623 * 2 ^ 59
def prefixEnd_192623 : Nat := 4983230072969 + 3 ^ 40 * 192623 * 2
def baseEnd_192623 : Nat := 98908184111105095326649

theorem tailTrace_192623 : CollatzResearch.WordTrace tailWord_192623 prefixEnd_192623 98908184111105095326649 := by
  unfold tailWord_192623
  simp only [CollatzResearch.WordTrace]
  refine ⟨7025537981167243234414523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4683691987444828822943015 7025537981167243234414523)
  ·
    refine ⟨10538306971750864851621785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7025537981167243234414523 10538306971750864851621785)
    ·
      refine ⟨7903730228813148638716339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10538306971750864851621785 7903730228813148638716339)
      ·
        refine ⟨11855595343219722958074509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7903730228813148638716339 11855595343219722958074509)
        ·
          refine ⟨4445848253707396109277941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11855595343219722958074509 4445848253707396109277941)
          ·
            refine ⟨416798273785068385244807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4445848253707396109277941 416798273785068385244807)
            ·
              refine ⟨625197410677602577867211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 416798273785068385244807 625197410677602577867211)
              ·
                refine ⟨937796116016403866800817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 625197410677602577867211 937796116016403866800817)
                ·
                  refine ⟨703347087012302900100613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 937796116016403866800817 703347087012302900100613)
                  ·
                    refine ⟨131877578814806793768865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 703347087012302900100613 131877578814806793768865)
                    ·
                      refine ⟨98908184111105095326649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 131877578814806793768865 98908184111105095326649)
                      ·
                        rfl

theorem cell23_192623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 1, 2, 4, 2].length) (baseStart_192623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_192623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_192623 prefixEnd_192623 := by exact prefixLift 192623
  have htrace : WordTrace (prefixWord ++ tailWord_192623) baseStart_192623 baseEnd_192623 := by
    simpa [prefixWord, tailWord_192623, baseEnd_192623] using wordTrace_append hprefix tailTrace_192623
  have hstable : (prefixWord ++ tailWord_192623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192623).length < 2 ^ (prefixWord ++ tailWord_192623).sum := by decide
  have hdescent : baseEnd_192623 < baseStart_192623 := by decide
  rcases family_descends (prefixWord ++ tailWord_192623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192633 : List Nat := [1, 2, 1, 3, 4, 2, 1, 2, 3, 4]
def baseStart_192633 : Nat := 118140960795 + 192633 * 2 ^ 59
def prefixEnd_192633 : Nat := 4983230072969 + 3 ^ 40 * 192633 * 2
def baseEnd_192633 : Nat := 32971106305883352067201

theorem tailTrace_192633 : CollatzResearch.WordTrace tailWord_192633 prefixEnd_192633 32971106305883352067201 := by
  unfold tailWord_192633
  simp only [CollatzResearch.WordTrace]
  refine ⟨7025902711131014942278553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4683935140754009961519035 7025902711131014942278553)
  ·
    refine ⟨5269427033348261206708915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7025902711131014942278553 5269427033348261206708915)
    ·
      refine ⟨7904140550022391810063373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5269427033348261206708915 7904140550022391810063373)
      ·
        refine ⟨2964052706258396928773765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7904140550022391810063373 2964052706258396928773765)
        ·
          refine ⟨555759882423449424145081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2964052706258396928773765 555759882423449424145081)
          ·
            refine ⟨416819911817587068108811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 555759882423449424145081 416819911817587068108811)
            ·
              refine ⟨625229867726380602163217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 416819911817587068108811 625229867726380602163217)
              ·
                refine ⟨468922400794785451622413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 625229867726380602163217 468922400794785451622413)
                ·
                  refine ⟨175845900298044544358405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 468922400794785451622413 175845900298044544358405)
                  ·
                    refine ⟨32971106305883352067201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 175845900298044544358405 32971106305883352067201)
                    ·
                      rfl

theorem cell23_192633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 2, 3, 4].length) (baseStart_192633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_192633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_192633 prefixEnd_192633 := by exact prefixLift 192633
  have htrace : WordTrace (prefixWord ++ tailWord_192633) baseStart_192633 baseEnd_192633 := by
    simpa [prefixWord, tailWord_192633, baseEnd_192633] using wordTrace_append hprefix tailTrace_192633
  have hstable : (prefixWord ++ tailWord_192633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192633).length < 2 ^ (prefixWord ++ tailWord_192633).sum := by decide
  have hdescent : baseEnd_192633 < baseStart_192633 := by decide
  rcases family_descends (prefixWord ++ tailWord_192633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192643 : List Nat := [1, 1, 1, 3, 3, 3, 3, 1, 2, 2, 3]
def baseStart_192643 : Nat := 118140960795 + 192643 * 2 ^ 59
def prefixEnd_192643 : Nat := 4983230072969 + 3 ^ 40 * 192643 * 2
def baseEnd_192643 : Nat := 98918453724195017076557

theorem tailTrace_192643 : CollatzResearch.WordTrace tailWord_192643 prefixEnd_192643 98918453724195017076557 := by
  unfold tailWord_192643
  simp only [CollatzResearch.WordTrace]
  refine ⟨7026267441094786650142583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4684178294063191100095055 7026267441094786650142583)
  ·
    refine ⟨10539401161642179975213875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7026267441094786650142583 10539401161642179975213875)
    ·
      refine ⟨15809101742463269962820813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10539401161642179975213875 15809101742463269962820813)
      ·
        refine ⟨5928413153423726236057805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15809101742463269962820813 5928413153423726236057805)
        ·
          refine ⟨2223154932533897338521677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5928413153423726236057805 2223154932533897338521677)
          ·
            refine ⟨833683099700211501945629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2223154932533897338521677 833683099700211501945629)
            ·
              refine ⟨312631162387579313229611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 833683099700211501945629 312631162387579313229611)
              ·
                refine ⟨468946743581368969844417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 312631162387579313229611 468946743581368969844417)
                ·
                  refine ⟨351710057686026727383313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 468946743581368969844417 351710057686026727383313)
                  ·
                    refine ⟨263782543264520045537485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 351710057686026727383313 263782543264520045537485)
                    ·
                      refine ⟨98918453724195017076557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 263782543264520045537485 98918453724195017076557)
                      ·
                        rfl

theorem cell23_192643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 3, 1, 2, 2, 3].length) (baseStart_192643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_192643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_192643 prefixEnd_192643 := by exact prefixLift 192643
  have htrace : WordTrace (prefixWord ++ tailWord_192643) baseStart_192643 baseEnd_192643 := by
    simpa [prefixWord, tailWord_192643, baseEnd_192643] using wordTrace_append hprefix tailTrace_192643
  have hstable : (prefixWord ++ tailWord_192643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192643).length < 2 ^ (prefixWord ++ tailWord_192643).sum := by decide
  have hdescent : baseEnd_192643 < baseStart_192643 := by decide
  rcases family_descends (prefixWord ++ tailWord_192643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192650 : List Nat := [3, 1, 2, 3, 1, 2, 1, 5, 1, 4]
def baseStart_192650 : Nat := 118140960795 + 192650 * 2 ^ 59
def prefixEnd_192650 : Nat := 4983230072969 + 3 ^ 40 * 192650 * 2
def baseEnd_192650 : Nat := 32974016029592163229675

theorem tailTrace_192650 : CollatzResearch.WordTrace tailWord_192650 prefixEnd_192650 32974016029592163229675 := by
  unfold tailWord_192650
  simp only [CollatzResearch.WordTrace]
  refine ⟨1756630688017356711411851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4684348501379617897098269 1756630688017356711411851)
  ·
    refine ⟨2634946032026035067117777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1756630688017356711411851 2634946032026035067117777)
    ·
      refine ⟨1976209524019526300338333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2634946032026035067117777 1976209524019526300338333)
      ·
        refine ⟨741078571507322362626875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1976209524019526300338333 741078571507322362626875)
        ·
          refine ⟨1111617857260983543940313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 741078571507322362626875 1111617857260983543940313)
          ·
            refine ⟨833713392945737657955235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1111617857260983543940313 833713392945737657955235)
            ·
              refine ⟨1250570089418606486932853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 833713392945737657955235 1250570089418606486932853)
              ·
                refine ⟨117240945882994358149955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1250570089418606486932853 117240945882994358149955)
                ·
                  refine ⟨175861418824491537224933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 117240945882994358149955 175861418824491537224933)
                  ·
                    refine ⟨32974016029592163229675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 175861418824491537224933 32974016029592163229675)
                    ·
                      rfl

theorem cell23_192650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 5, 1, 4].length) (baseStart_192650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_192650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_192650 prefixEnd_192650 := by exact prefixLift 192650
  have htrace : WordTrace (prefixWord ++ tailWord_192650) baseStart_192650 baseEnd_192650 := by
    simpa [prefixWord, tailWord_192650, baseEnd_192650] using wordTrace_append hprefix tailTrace_192650
  have hstable : (prefixWord ++ tailWord_192650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192650).length < 2 ^ (prefixWord ++ tailWord_192650).sum := by decide
  have hdescent : baseEnd_192650 < baseStart_192650 := by decide
  rcases family_descends (prefixWord ++ tailWord_192650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192736 : List Nat := [2, 1, 1, 3, 1, 3, 4, 8]
def baseStart_192736 : Nat := 118140960795 + 192736 * 2 ^ 59
def prefixEnd_192736 : Nat := 4983230072969 + 3 ^ 40 * 192736 * 2
def baseEnd_192736 : Nat := 3665415089817153822727

theorem tailTrace_192736 : CollatzResearch.WordTrace tailWord_192736 prefixEnd_192736 3665415089817153822727 := by
  unfold tailWord_192736
  simp only [CollatzResearch.WordTrace]
  refine ⟨3514829714878931766639031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4686439619838575688852041 3514829714878931766639031)
  ·
    refine ⟨5272244572318397649958547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3514829714878931766639031 5272244572318397649958547)
    ·
      refine ⟨7908366858477596474937821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5272244572318397649958547 7908366858477596474937821)
      ·
        refine ⟨2965637571929098678101683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7908366858477596474937821 2965637571929098678101683)
        ·
          refine ⟨4448456357893648017152525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2965637571929098678101683 4448456357893648017152525)
          ·
            refine ⟨1668171134210118006432197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4448456357893648017152525 1668171134210118006432197)
            ·
              refine ⟨312782087664397126206037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1668171134210118006432197 312782087664397126206037)
              ·
                refine ⟨3665415089817153822727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 312782087664397126206037 3665415089817153822727)
                ·
                  rfl

theorem cell23_192736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 4, 8].length) (baseStart_192736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_192736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_192736 prefixEnd_192736 := by exact prefixLift 192736
  have htrace : WordTrace (prefixWord ++ tailWord_192736) baseStart_192736 baseEnd_192736 := by
    simpa [prefixWord, tailWord_192736, baseEnd_192736] using wordTrace_append hprefix tailTrace_192736
  have hstable : (prefixWord ++ tailWord_192736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192736).length < 2 ^ (prefixWord ++ tailWord_192736).sum := by decide
  have hdescent : baseEnd_192736 < baseStart_192736 := by decide
  rcases family_descends (prefixWord ++ tailWord_192736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192743 : List Nat := [1, 1, 5, 3, 1, 1, 2, 1, 1, 1, 6]
def baseStart_192743 : Nat := 118140960795 + 192743 * 2 ^ 59
def prefixEnd_192743 : Nat := 4983230072969 + 3 ^ 40 * 192743 * 2
def baseEnd_192743 : Nat := 98969801789644625826097

theorem tailTrace_192743 : CollatzResearch.WordTrace tailWord_192743 prefixEnd_192743 98969801789644625826097 := by
  unfold tailWord_192743
  simp only [CollatzResearch.WordTrace]
  refine ⟨7029914740732503728782883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4686609827155002485855255 7029914740732503728782883)
  ·
    refine ⟨10544872111098755593174325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7029914740732503728782883 10544872111098755593174325)
    ·
      refine ⟨988581760415508336860093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10544872111098755593174325 988581760415508336860093)
      ·
        refine ⟨370718160155815626322535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 988581760415508336860093 370718160155815626322535)
        ·
          refine ⟨556077240233723439483803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 370718160155815626322535 556077240233723439483803)
          ·
            refine ⟨834115860350585159225705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 556077240233723439483803 834115860350585159225705)
            ·
              refine ⟨625586895262938869419279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 834115860350585159225705 625586895262938869419279)
              ·
                refine ⟨938380342894408304128919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 625586895262938869419279 938380342894408304128919)
                ·
                  refine ⟨1407570514341612456193379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 938380342894408304128919 1407570514341612456193379)
                  ·
                    refine ⟨2111355771512418684290069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1407570514341612456193379 2111355771512418684290069)
                    ·
                      refine ⟨98969801789644625826097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2111355771512418684290069 98969801789644625826097)
                      ·
                        rfl

theorem cell23_192743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_192743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_192743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_192743 prefixEnd_192743 := by exact prefixLift 192743
  have htrace : WordTrace (prefixWord ++ tailWord_192743) baseStart_192743 baseEnd_192743 := by
    simpa [prefixWord, tailWord_192743, baseEnd_192743] using wordTrace_append hprefix tailTrace_192743
  have hstable : (prefixWord ++ tailWord_192743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192743).length < 2 ^ (prefixWord ++ tailWord_192743).sum := by decide
  have hdescent : baseEnd_192743 < baseStart_192743 := by decide
  rcases family_descends (prefixWord ++ tailWord_192743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192797 : List Nat := [1, 4, 2, 3, 2, 1, 2, 1, 1, 3, 3]
def baseStart_192797 : Nat := 118140960795 + 192797 * 2 ^ 59
def prefixEnd_192797 : Nat := 4983230072969 + 3 ^ 40 * 192797 * 2
def baseEnd_192797 : Nat := 98997529744987414550849

theorem tailTrace_192797 : CollatzResearch.WordTrace tailWord_192797 prefixEnd_192797 98997529744987414550849 := by
  unfold tailWord_192797
  simp only [CollatzResearch.WordTrace]
  refine ⟨7031884282536870951248645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4687922855024580634165763 7031884282536870951248645)
  ·
    refine ⟨1318478302975663303359121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7031884282536870951248645 1318478302975663303359121)
    ·
      refine ⟨988858727231747477519341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1318478302975663303359121 988858727231747477519341)
      ·
        refine ⟨370822022711905304069753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 988858727231747477519341 370822022711905304069753)
        ·
          refine ⟨278116517033928978052315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 370822022711905304069753 278116517033928978052315)
          ·
            refine ⟨417174775550893467078473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 278116517033928978052315 417174775550893467078473)
            ·
              refine ⟨312881081663170100308855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 417174775550893467078473 312881081663170100308855)
              ·
                refine ⟨469321622494755150463283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 312881081663170100308855 469321622494755150463283)
                ·
                  refine ⟨703982433742132725694925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 469321622494755150463283 703982433742132725694925)
                  ·
                    refine ⟨263993412653299772135597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 703982433742132725694925 263993412653299772135597)
                    ·
                      refine ⟨98997529744987414550849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 263993412653299772135597 98997529744987414550849)
                      ·
                        rfl

theorem cell23_192797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_192797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_192797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_192797 prefixEnd_192797 := by exact prefixLift 192797
  have htrace : WordTrace (prefixWord ++ tailWord_192797) baseStart_192797 baseEnd_192797 := by
    simpa [prefixWord, tailWord_192797, baseEnd_192797] using wordTrace_append hprefix tailTrace_192797
  have hstable : (prefixWord ++ tailWord_192797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192797).length < 2 ^ (prefixWord ++ tailWord_192797).sum := by decide
  have hdescent : baseEnd_192797 < baseStart_192797 := by decide
  rcases family_descends (prefixWord ++ tailWord_192797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_192873 : List Nat := [1, 2, 1, 1, 1, 3, 4, 3, 2, 5]
def baseStart_192873 : Nat := 118140960795 + 192873 * 2 ^ 59
def prefixEnd_192873 : Nat := 4983230072969 + 3 ^ 40 * 192873 * 2
def baseEnd_192873 : Nat := 33012184758243039066833

theorem tailTrace_192873 : CollatzResearch.WordTrace tailWord_192873 prefixEnd_192873 33012184758243039066833 := by
  unfold tailWord_192873
  simp only [CollatzResearch.WordTrace]
  refine ⟨7034656230261535931015273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4689770820174357287343515 7034656230261535931015273)
  ·
    refine ⟨5275992172696151948261455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7034656230261535931015273 5275992172696151948261455)
    ·
      refine ⟨7913988259044227922392183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5275992172696151948261455 7913988259044227922392183)
      ·
        refine ⟨11870982388566341883588275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7913988259044227922392183 11870982388566341883588275)
        ·
          refine ⟨17806473582849512825382413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11870982388566341883588275 17806473582849512825382413)
          ·
            refine ⟨6677427593568567309518405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17806473582849512825382413 6677427593568567309518405)
            ·
              refine ⟨1252017673794106370534701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6677427593568567309518405 1252017673794106370534701)
              ·
                refine ⟨469506627672789888950513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1252017673794106370534701 469506627672789888950513)
                ·
                  refine ⟨352129970754592416712885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 469506627672789888950513 352129970754592416712885)
                  ·
                    refine ⟨33012184758243039066833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 352129970754592416712885 33012184758243039066833)
                    ·
                      rfl

theorem cell23_192873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 3, 2, 5].length) (baseStart_192873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_192873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_192873 prefixEnd_192873 := by exact prefixLift 192873
  have htrace : WordTrace (prefixWord ++ tailWord_192873) baseStart_192873 baseEnd_192873 := by
    simpa [prefixWord, tailWord_192873, baseEnd_192873] using wordTrace_append hprefix tailTrace_192873
  have hstable : (prefixWord ++ tailWord_192873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_192873).length < 2 ^ (prefixWord ++ tailWord_192873).sum := by decide
  have hdescent : baseEnd_192873 < baseStart_192873 := by decide
  rcases family_descends (prefixWord ++ tailWord_192873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193023 : List Nat := [1, 1, 2, 2, 1, 2, 4, 10]
def baseStart_193023 : Nat := 118140960795 + 193023 * 2 ^ 59
def prefixEnd_193023 : Nat := 4983230072969 + 3 ^ 40 * 193023 * 2
def baseEnd_193023 : Nat := 3670873198996427049067

theorem tailTrace_193023 : CollatzResearch.WordTrace tailWord_193023 prefixEnd_193023 3670873198996427049067 := by
  unfold tailWord_193023
  simp only [CollatzResearch.WordTrace]
  refine ⟨7040127179718111548975723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4693418119812074365983815 7040127179718111548975723)
  ·
    refine ⟨10560190769577167323463585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7040127179718111548975723 10560190769577167323463585)
    ·
      refine ⟨7920143077182875492597689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10560190769577167323463585 7920143077182875492597689)
      ·
        refine ⟨5940107307887156619448267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7920143077182875492597689 5940107307887156619448267)
        ·
          refine ⟨8910160961830734929172401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5940107307887156619448267 8910160961830734929172401)
          ·
            refine ⟨6682620721373051196879301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8910160961830734929172401 6682620721373051196879301)
            ·
              refine ⟨1252991385257447099414869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6682620721373051196879301 1252991385257447099414869)
              ·
                refine ⟨3670873198996427049067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 1252991385257447099414869 3670873198996427049067)
                ·
                  rfl

theorem cell23_193023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 10].length) (baseStart_193023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_193023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_193023 prefixEnd_193023 := by exact prefixLift 193023
  have htrace : WordTrace (prefixWord ++ tailWord_193023) baseStart_193023 baseEnd_193023 := by
    simpa [prefixWord, tailWord_193023, baseEnd_193023] using wordTrace_append hprefix tailTrace_193023
  have hstable : (prefixWord ++ tailWord_193023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193023).length < 2 ^ (prefixWord ++ tailWord_193023).sum := by decide
  have hdescent : baseEnd_193023 < baseStart_193023 := by decide
  rcases family_descends (prefixWord ++ tailWord_193023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193034 : List Nat := [3, 1, 2, 2, 2, 1, 1, 4, 3, 2, 2]
def baseStart_193034 : Nat := 118140960795 + 193034 * 2 ^ 59
def prefixEnd_193034 : Nat := 4983230072969 + 3 ^ 40 * 193034 * 2
def baseEnd_193034 : Nat := 99119224660102987287259

theorem tailTrace_193034 : CollatzResearch.WordTrace tailWord_193034 prefixEnd_193034 99119224660102987287259 := by
  unfold tailWord_193034
  simp only [CollatzResearch.WordTrace]
  refine ⟨1760132095669565106906539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4693685588452173618417437 1760132095669565106906539)
  ·
    refine ⟨2640198143504347660359809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1760132095669565106906539 2640198143504347660359809)
    ·
      refine ⟨1980148607628260745269857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2640198143504347660359809 1980148607628260745269857)
      ·
        refine ⟨1485111455721195558952393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1980148607628260745269857 1485111455721195558952393)
        ·
          refine ⟨1113833591790896669214295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1485111455721195558952393 1113833591790896669214295)
          ·
            refine ⟨1670750387686345003821443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1113833591790896669214295 1670750387686345003821443)
            ·
              refine ⟨2506125581529517505732165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1670750387686345003821443 2506125581529517505732165)
              ·
                refine ⟨469898546536784532324781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2506125581529517505732165 469898546536784532324781)
                ·
                  refine ⟨176211954951294199621793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 469898546536784532324781 176211954951294199621793)
                  ·
                    refine ⟨132158966213470649716345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 176211954951294199621793 132158966213470649716345)
                    ·
                      refine ⟨99119224660102987287259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 132158966213470649716345 99119224660102987287259)
                      ·
                        rfl

theorem cell23_193034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 4, 3, 2, 2].length) (baseStart_193034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_193034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_193034 prefixEnd_193034 := by exact prefixLift 193034
  have htrace : WordTrace (prefixWord ++ tailWord_193034) baseStart_193034 baseEnd_193034 := by
    simpa [prefixWord, tailWord_193034, baseEnd_193034] using wordTrace_append hprefix tailTrace_193034
  have hstable : (prefixWord ++ tailWord_193034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193034).length < 2 ^ (prefixWord ++ tailWord_193034).sum := by decide
  have hdescent : baseEnd_193034 < baseStart_193034 := by decide
  rcases family_descends (prefixWord ++ tailWord_193034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193044 : List Nat := [2, 4, 3, 1, 1, 1, 1, 2, 4, 4]
def baseStart_193044 : Nat := 118140960795 + 193044 * 2 ^ 59
def prefixEnd_193044 : Nat := 4983230072969 + 3 ^ 40 * 193044 * 2
def baseEnd_193044 : Nat := 33041453155549316054071

theorem tailTrace_193044 : CollatzResearch.WordTrace tailWord_193044 prefixEnd_193044 33041453155549316054071 := by
  unfold tailWord_193044
  simp only [CollatzResearch.WordTrace]
  refine ⟨3520446556321016067745093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4693928741761354756993457 3520446556321016067745093)
  ·
    refine ⟨660083729310190512702205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3520446556321016067745093 660083729310190512702205)
    ·
      refine ⟨247531398491321442263327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 660083729310190512702205 247531398491321442263327)
      ·
        refine ⟨371297097736982163394991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247531398491321442263327 371297097736982163394991)
        ·
          refine ⟨556945646605473245092487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 371297097736982163394991 556945646605473245092487)
          ·
            refine ⟨835418469908209867638731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 556945646605473245092487 835418469908209867638731)
            ·
              refine ⟨1253127704862314801458097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 835418469908209867638731 1253127704862314801458097)
              ·
                refine ⟨939845778646736101093573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1253127704862314801458097 939845778646736101093573)
                ·
                  refine ⟨176221083496263018955045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 939845778646736101093573 176221083496263018955045)
                  ·
                    refine ⟨33041453155549316054071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 176221083496263018955045 33041453155549316054071)
                    ·
                      rfl

theorem cell23_193044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_193044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_193044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_193044 prefixEnd_193044 := by exact prefixLift 193044
  have htrace : WordTrace (prefixWord ++ tailWord_193044) baseStart_193044 baseEnd_193044 := by
    simpa [prefixWord, tailWord_193044, baseEnd_193044] using wordTrace_append hprefix tailTrace_193044
  have hstable : (prefixWord ++ tailWord_193044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193044).length < 2 ^ (prefixWord ++ tailWord_193044).sum := by decide
  have hdescent : baseEnd_193044 < baseStart_193044 := by decide
  rcases family_descends (prefixWord ++ tailWord_193044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193078 : List Nat := [5, 1, 2, 1, 2, 3, 2, 1, 2, 4]
def baseStart_193078 : Nat := 118140960795 + 193078 * 2 ^ 59
def prefixEnd_193078 : Nat := 4983230072969 + 3 ^ 40 * 193078 * 2
def baseEnd_193078 : Nat := 33047272602966938379019

theorem tailTrace_193078 : CollatzResearch.WordTrace tailWord_193078 prefixEnd_193078 33047272602966938379019 := by
  unfold tailWord_193078
  simp only [CollatzResearch.WordTrace]
  refine ⟨440133324657428496389243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4694755463012570628151925 440133324657428496389243)
  ·
    refine ⟨660199986986142744583865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 440133324657428496389243 660199986986142744583865)
    ·
      refine ⟨495149990239607058437899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 660199986986142744583865 495149990239607058437899)
      ·
        refine ⟨742724985359410587656849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 495149990239607058437899 742724985359410587656849)
        ·
          refine ⟨557043739019557940742637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 742724985359410587656849 557043739019557940742637)
          ·
            refine ⟨208891402132334227778489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 557043739019557940742637 208891402132334227778489)
            ·
              refine ⟨156668551599250670833867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 208891402132334227778489 156668551599250670833867)
              ·
                refine ⟨235002827398876006250801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 156668551599250670833867 235002827398876006250801)
                ·
                  refine ⟨176252120549157004688101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 235002827398876006250801 176252120549157004688101)
                  ·
                    refine ⟨33047272602966938379019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 176252120549157004688101 33047272602966938379019)
                    ·
                      rfl

theorem cell23_193078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 2, 1, 2, 4].length) (baseStart_193078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_193078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_193078 prefixEnd_193078 := by exact prefixLift 193078
  have htrace : WordTrace (prefixWord ++ tailWord_193078) baseStart_193078 baseEnd_193078 := by
    simpa [prefixWord, tailWord_193078, baseEnd_193078] using wordTrace_append hprefix tailTrace_193078
  have hstable : (prefixWord ++ tailWord_193078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193078).length < 2 ^ (prefixWord ++ tailWord_193078).sum := by decide
  have hdescent : baseEnd_193078 < baseStart_193078 := by decide
  rcases family_descends (prefixWord ++ tailWord_193078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193111 : List Nat := [1, 1, 3, 2, 2, 2, 5, 1, 1, 3, 2]
def baseStart_193111 : Nat := 118140960795 + 193111 * 2 ^ 59
def prefixEnd_193111 : Nat := 4983230072969 + 3 ^ 40 * 193111 * 2
def baseEnd_193111 : Nat := 99158762670499186024405

theorem tailTrace_193111 : CollatzResearch.WordTrace tailWord_193111 prefixEnd_193111 99158762670499186024405 := by
  unfold tailWord_193111
  simp only [CollatzResearch.WordTrace]
  refine ⟨7043336803399302578179187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4695557868932868385452791 7043336803399302578179187)
  ·
    refine ⟨10565005205098953867268781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7043336803399302578179187 10565005205098953867268781)
    ·
      refine ⟨3961876951912107700225793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10565005205098953867268781 3961876951912107700225793)
      ·
        refine ⟨2971407713934080775169345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3961876951912107700225793 2971407713934080775169345)
        ·
          refine ⟨2228555785450560581377009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2971407713934080775169345 2228555785450560581377009)
          ·
            refine ⟨1671416839087920436032757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2228555785450560581377009 1671416839087920436032757)
            ·
              refine ⟨156695328664492540878071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1671416839087920436032757 156695328664492540878071)
              ·
                refine ⟨235042992996738811317107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 156695328664492540878071 235042992996738811317107)
                ·
                  refine ⟨352564489495108216975661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 235042992996738811317107 352564489495108216975661)
                  ·
                    refine ⟨132211683560665581365873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 352564489495108216975661 132211683560665581365873)
                    ·
                      refine ⟨99158762670499186024405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 132211683560665581365873 99158762670499186024405)
                      ·
                        rfl

theorem cell23_193111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 5, 1, 1, 3, 2].length) (baseStart_193111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_193111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_193111 prefixEnd_193111 := by exact prefixLift 193111
  have htrace : WordTrace (prefixWord ++ tailWord_193111) baseStart_193111 baseEnd_193111 := by
    simpa [prefixWord, tailWord_193111, baseEnd_193111] using wordTrace_append hprefix tailTrace_193111
  have hstable : (prefixWord ++ tailWord_193111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193111).length < 2 ^ (prefixWord ++ tailWord_193111).sum := by decide
  have hdescent : baseEnd_193111 < baseStart_193111 := by decide
  rcases family_descends (prefixWord ++ tailWord_193111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193167 : List Nat := [1, 1, 2, 1, 1, 1, 1, 4, 4, 5, 2]
def baseStart_193167 : Nat := 118140960795 + 193167 * 2 ^ 59
def prefixEnd_193167 : Nat := 4983230072969 + 3 ^ 40 * 193167 * 2
def baseEnd_193167 : Nat := 99187517587150966924147

theorem tailTrace_193167 : CollatzResearch.WordTrace tailWord_193167 prefixEnd_193167 99187517587150966924147 := by
  unfold tailWord_193167
  simp only [CollatzResearch.WordTrace]
  refine ⟨7045379291196424142217755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4696919527464282761478503 7045379291196424142217755)
  ·
    refine ⟨10568068936794636213326633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7045379291196424142217755 10568068936794636213326633)
    ·
      refine ⟨7926051702595977159994975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10568068936794636213326633 7926051702595977159994975)
      ·
        refine ⟨11889077553893965739992463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7926051702595977159994975 11889077553893965739992463)
        ·
          refine ⟨17833616330840948609988695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11889077553893965739992463 17833616330840948609988695)
          ·
            refine ⟨26750424496261422914983043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17833616330840948609988695 26750424496261422914983043)
            ·
              refine ⟨40125636744392134372474565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26750424496261422914983043 40125636744392134372474565)
              ·
                refine ⟨7523556889573525194838981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40125636744392134372474565 7523556889573525194838981)
                ·
                  refine ⟨1410666916795035974032309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7523556889573525194838981 1410666916795035974032309)
                  ·
                    refine ⟨132250023449534622565529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1410666916795035974032309 132250023449534622565529)
                    ·
                      refine ⟨99187517587150966924147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 132250023449534622565529 99187517587150966924147)
                      ·
                        rfl

theorem cell23_193167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 4, 5, 2].length) (baseStart_193167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_193167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_193167 prefixEnd_193167 := by exact prefixLift 193167
  have htrace : WordTrace (prefixWord ++ tailWord_193167) baseStart_193167 baseEnd_193167 := by
    simpa [prefixWord, tailWord_193167, baseEnd_193167] using wordTrace_append hprefix tailTrace_193167
  have hstable : (prefixWord ++ tailWord_193167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193167).length < 2 ^ (prefixWord ++ tailWord_193167).sum := by decide
  have hdescent : baseEnd_193167 < baseStart_193167 := by decide
  rcases family_descends (prefixWord ++ tailWord_193167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193214 : List Nat := [4, 2, 1, 1, 2, 1, 2, 3, 2, 1, 4]
def baseStart_193214 : Nat := 118140960795 + 193214 * 2 ^ 59
def prefixEnd_193214 : Nat := 4983230072969 + 3 ^ 40 * 193214 * 2
def baseEnd_193214 : Nat := 99211651177912283036431

theorem tailTrace_193214 : CollatzResearch.WordTrace tailWord_193214 prefixEnd_193214 99211651177912283036431 := by
  unfold tailWord_193214
  simp only [CollatzResearch.WordTrace]
  refine ⟨880886690253268896147337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4698062348017434112785797 880886690253268896147337)
  ·
    refine ⟨660665017689951672110503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 880886690253268896147337 660665017689951672110503)
    ·
      refine ⟨990997526534927508165755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 660665017689951672110503 990997526534927508165755)
      ·
        refine ⟨1486496289802391262248633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 990997526534927508165755 1486496289802391262248633)
        ·
          refine ⟨1114872217351793446686475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1486496289802391262248633 1114872217351793446686475)
          ·
            refine ⟨1672308326027690170029713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1114872217351793446686475 1672308326027690170029713)
            ·
              refine ⟨1254231244520767627522285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1672308326027690170029713 1254231244520767627522285)
              ·
                refine ⟨470336716695287860320857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1254231244520767627522285 470336716695287860320857)
                ·
                  refine ⟨352752537521465895240643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 470336716695287860320857 352752537521465895240643)
                  ·
                    refine ⟨529128806282198842860965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 352752537521465895240643 529128806282198842860965)
                    ·
                      refine ⟨99211651177912283036431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 529128806282198842860965 99211651177912283036431)
                      ·
                        rfl

theorem cell23_193214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 3, 2, 1, 4].length) (baseStart_193214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_193214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_193214 prefixEnd_193214 := by exact prefixLift 193214
  have htrace : WordTrace (prefixWord ++ tailWord_193214) baseStart_193214 baseEnd_193214 := by
    simpa [prefixWord, tailWord_193214, baseEnd_193214] using wordTrace_append hprefix tailTrace_193214
  have hstable : (prefixWord ++ tailWord_193214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193214).length < 2 ^ (prefixWord ++ tailWord_193214).sum := by decide
  have hdescent : baseEnd_193214 < baseStart_193214 := by decide
  rcases family_descends (prefixWord ++ tailWord_193214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193264 : List Nat := [2, 1, 1, 1, 3, 1, 4, 1, 5, 1, 3]
def baseStart_193264 : Nat := 118140960795 + 193264 * 2 ^ 59
def prefixEnd_193264 : Nat := 4983230072969 + 3 ^ 40 * 193264 * 2
def baseEnd_193264 : Nat := 99237325210637087411201

theorem tailTrace_193264 : CollatzResearch.WordTrace tailWord_193264 prefixEnd_193264 99237325210637087411201 := by
  unfold tailWord_193264
  simp only [CollatzResearch.WordTrace]
  refine ⟨3524458585922504854249423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4699278114563339805665897 3524458585922504854249423)
  ·
    refine ⟨5286687878883757281374135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3524458585922504854249423 5286687878883757281374135)
    ·
      refine ⟨7930031818325635922061203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5286687878883757281374135 7930031818325635922061203)
      ·
        refine ⟨11895047727488453883091805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7930031818325635922061203 11895047727488453883091805)
        ·
          refine ⟨4460642897808170206159427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11895047727488453883091805 4460642897808170206159427)
          ·
            refine ⟨6690964346712255309239141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4460642897808170206159427 6690964346712255309239141)
            ·
              refine ⟨1254555815008547870482339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6690964346712255309239141 1254555815008547870482339)
              ·
                refine ⟨1881833722512821805723509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1254555815008547870482339 1881833722512821805723509)
                ·
                  refine ⟨176421911485577044286579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1881833722512821805723509 176421911485577044286579)
                  ·
                    refine ⟨264632867228365566429869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 176421911485577044286579 264632867228365566429869)
                    ·
                      refine ⟨99237325210637087411201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 264632867228365566429869 99237325210637087411201)
                      ·
                        rfl

theorem cell23_193264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 1, 5, 1, 3].length) (baseStart_193264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_193264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_193264 prefixEnd_193264 := by exact prefixLift 193264
  have htrace : WordTrace (prefixWord ++ tailWord_193264) baseStart_193264 baseEnd_193264 := by
    simpa [prefixWord, tailWord_193264, baseEnd_193264] using wordTrace_append hprefix tailTrace_193264
  have hstable : (prefixWord ++ tailWord_193264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193264).length < 2 ^ (prefixWord ++ tailWord_193264).sum := by decide
  have hdescent : baseEnd_193264 < baseStart_193264 := by decide
  rcases family_descends (prefixWord ++ tailWord_193264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193274 : List Nat := [3, 1, 1, 1, 1, 3, 2, 3, 1, 5, 2]
def baseStart_193274 : Nat := 118140960795 + 193274 * 2 ^ 59
def prefixEnd_193274 : Nat := 4983230072969 + 3 ^ 40 * 193274 * 2
def baseEnd_193274 : Nat := 99242460017182048286155

theorem tailTrace_193274 : CollatzResearch.WordTrace tailWord_193274 prefixEnd_193274 99242460017182048286155 := by
  unfold tailWord_193274
  simp only [CollatzResearch.WordTrace]
  refine ⟨1762320475452195354090719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4699521267872520944241917 1762320475452195354090719)
  ·
    refine ⟨2643480713178293031136079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1762320475452195354090719 2643480713178293031136079)
    ·
      refine ⟨3965221069767439546704119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2643480713178293031136079 3965221069767439546704119)
      ·
        refine ⟨5947831604651159320056179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3965221069767439546704119 5947831604651159320056179)
        ·
          refine ⟨8921747406976738980084269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5947831604651159320056179 8921747406976738980084269)
          ·
            refine ⟨3345655277616277117531601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8921747406976738980084269 3345655277616277117531601)
            ·
              refine ⟨2509241458212207838148701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3345655277616277117531601 2509241458212207838148701)
              ·
                refine ⟨940965546829577939305763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2509241458212207838148701 940965546829577939305763)
                ·
                  refine ⟨1411448320244366908958645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 940965546829577939305763 1411448320244366908958645)
                  ·
                    refine ⟨132323280022909397714873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1411448320244366908958645 132323280022909397714873)
                    ·
                      refine ⟨99242460017182048286155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 132323280022909397714873 99242460017182048286155)
                      ·
                        rfl

theorem cell23_193274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 3, 1, 5, 2].length) (baseStart_193274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_193274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_193274 prefixEnd_193274 := by exact prefixLift 193274
  have htrace : WordTrace (prefixWord ++ tailWord_193274) baseStart_193274 baseEnd_193274 := by
    simpa [prefixWord, tailWord_193274, baseEnd_193274] using wordTrace_append hprefix tailTrace_193274
  have hstable : (prefixWord ++ tailWord_193274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193274).length < 2 ^ (prefixWord ++ tailWord_193274).sum := by decide
  have hdescent : baseEnd_193274 < baseStart_193274 := by decide
  rcases family_descends (prefixWord ++ tailWord_193274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193304 : List Nat := [2, 1, 2, 3, 1, 1, 1, 2, 2, 6, 2]
def baseStart_193304 : Nat := 118140960795 + 193304 * 2 ^ 59
def prefixEnd_193304 : Nat := 4983230072969 + 3 ^ 40 * 193304 * 2
def baseEnd_193304 : Nat := 99257864436816930911017

theorem tailTrace_193304 : CollatzResearch.WordTrace tailWord_193304 prefixEnd_193304 99257864436816930911017 := by
  unfold tailWord_193304
  simp only [CollatzResearch.WordTrace]
  refine ⟨3525188045850048269977483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4700250727800064359969977 3525188045850048269977483)
  ·
    refine ⟨5287782068775072404966225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3525188045850048269977483 5287782068775072404966225)
    ·
      refine ⟨3965836551581304303724669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5287782068775072404966225 3965836551581304303724669)
      ·
        refine ⟨1487188706842989113896751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3965836551581304303724669 1487188706842989113896751)
        ·
          refine ⟨2230783060264483670845127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1487188706842989113896751 2230783060264483670845127)
          ·
            refine ⟨3346174590396725506267691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2230783060264483670845127 3346174590396725506267691)
            ·
              refine ⟨5019261885595088259401537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3346174590396725506267691 5019261885595088259401537)
              ·
                refine ⟨3764446414196316194551153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5019261885595088259401537 3764446414196316194551153)
                ·
                  refine ⟨2823334810647237145913365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3764446414196316194551153 2823334810647237145913365)
                  ·
                    refine ⟨132343819249089241214689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2823334810647237145913365 132343819249089241214689)
                    ·
                      refine ⟨99257864436816930911017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 132343819249089241214689 99257864436816930911017)
                      ·
                        rfl

theorem cell23_193304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 2, 2, 6, 2].length) (baseStart_193304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_193304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_193304 prefixEnd_193304 := by exact prefixLift 193304
  have htrace : WordTrace (prefixWord ++ tailWord_193304) baseStart_193304 baseEnd_193304 := by
    simpa [prefixWord, tailWord_193304, baseEnd_193304] using wordTrace_append hprefix tailTrace_193304
  have hstable : (prefixWord ++ tailWord_193304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193304).length < 2 ^ (prefixWord ++ tailWord_193304).sum := by decide
  have hdescent : baseEnd_193304 < baseStart_193304 := by decide
  rcases family_descends (prefixWord ++ tailWord_193304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193307 : List Nat := [1, 1, 1, 1, 1, 1, 4, 1, 1, 8, 3]
def baseStart_193307 : Nat := 118140960795 + 193307 * 2 ^ 59
def prefixEnd_193307 : Nat := 4983230072969 + 3 ^ 40 * 193307 * 2
def baseEnd_193307 : Nat := 99259404878780419173503

theorem tailTrace_193307 : CollatzResearch.WordTrace tailWord_193307 prefixEnd_193307 99259404878780419173503 := by
  unfold tailWord_193307
  simp only [CollatzResearch.WordTrace]
  refine ⟨7050485510689228052314175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4700323673792818701542783 7050485510689228052314175)
  ·
    refine ⟨10575728266033842078471263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7050485510689228052314175 10575728266033842078471263)
    ·
      refine ⟨15863592399050763117706895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10575728266033842078471263 15863592399050763117706895)
      ·
        refine ⟨23795388598576144676560343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15863592399050763117706895 23795388598576144676560343)
        ·
          refine ⟨35693082897864217014840515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23795388598576144676560343 35693082897864217014840515)
          ·
            refine ⟨53539624346796325522260773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35693082897864217014840515 53539624346796325522260773)
            ·
              refine ⟨10038679565024311035423895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53539624346796325522260773 10038679565024311035423895)
              ·
                refine ⟨15058019347536466553135843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10038679565024311035423895 15058019347536466553135843)
                ·
                  refine ⟨22587029021304699829703765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15058019347536466553135843 22587029021304699829703765)
                  ·
                    refine ⟨264691746343414451129341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 22587029021304699829703765 264691746343414451129341)
                    ·
                      refine ⟨99259404878780419173503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 264691746343414451129341 99259404878780419173503)
                      ·
                        rfl

theorem cell23_193307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 8, 3].length) (baseStart_193307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_193307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_193307 prefixEnd_193307 := by exact prefixLift 193307
  have htrace : WordTrace (prefixWord ++ tailWord_193307) baseStart_193307 baseEnd_193307 := by
    simpa [prefixWord, tailWord_193307, baseEnd_193307] using wordTrace_append hprefix tailTrace_193307
  have hstable : (prefixWord ++ tailWord_193307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193307).length < 2 ^ (prefixWord ++ tailWord_193307).sum := by decide
  have hdescent : baseEnd_193307 < baseStart_193307 := by decide
  rcases family_descends (prefixWord ++ tailWord_193307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193314 : List Nat := [3, 3, 1, 1, 2, 2, 1, 3, 1, 6]
def baseStart_193314 : Nat := 118140960795 + 193314 * 2 ^ 59
def prefixEnd_193314 : Nat := 4983230072969 + 3 ^ 40 * 193314 * 2
def baseEnd_193314 : Nat := 33087666414453963928657

theorem tailTrace_193314 : CollatzResearch.WordTrace tailWord_193314 prefixEnd_193314 33087666414453963928657 := by
  unfold tailWord_193314
  simp only [CollatzResearch.WordTrace]
  refine ⟨1762685205415967061954749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4700493881109245498545997 1762685205415967061954749)
  ·
    refine ⟨661006952030987648233031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1762685205415967061954749 661006952030987648233031)
    ·
      refine ⟨991510428046481472349547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 661006952030987648233031 991510428046481472349547)
      ·
        refine ⟨1487265642069722208524321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 991510428046481472349547 1487265642069722208524321)
        ·
          refine ⟨1115449231552291656393241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1487265642069722208524321 1115449231552291656393241)
          ·
            refine ⟨836586923664218742294931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1115449231552291656393241 836586923664218742294931)
            ·
              refine ⟨1254880385496328113442397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 836586923664218742294931 1254880385496328113442397)
              ·
                refine ⟨470580144561123042540899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1254880385496328113442397 470580144561123042540899)
                ·
                  refine ⟨705870216841684563811349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 470580144561123042540899 705870216841684563811349)
                  ·
                    refine ⟨33087666414453963928657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 705870216841684563811349 33087666414453963928657)
                    ·
                      rfl

theorem cell23_193314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 3, 1, 6].length) (baseStart_193314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_193314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_193314 prefixEnd_193314 := by exact prefixLift 193314
  have htrace : WordTrace (prefixWord ++ tailWord_193314) baseStart_193314 baseEnd_193314 := by
    simpa [prefixWord, tailWord_193314, baseEnd_193314] using wordTrace_append hprefix tailTrace_193314
  have hstable : (prefixWord ++ tailWord_193314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193314).length < 2 ^ (prefixWord ++ tailWord_193314).sum := by decide
  have hdescent : baseEnd_193314 < baseStart_193314 := by decide
  rcases family_descends (prefixWord ++ tailWord_193314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193321 : List Nat := [1, 2, 1, 1, 1, 1, 1, 8, 3, 2, 2]
def baseStart_193321 : Nat := 118140960795 + 193321 * 2 ^ 59
def prefixEnd_193321 : Nat := 4983230072969 + 3 ^ 40 * 193321 * 2
def baseEnd_193321 : Nat := 99266593607943364398439

theorem tailTrace_193321 : CollatzResearch.WordTrace tailWord_193321 prefixEnd_193321 99266593607943364398439 := by
  unfold tailWord_193321
  simp only [CollatzResearch.WordTrace]
  refine ⟨7050996132638508443323817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4700664088425672295549211 7050996132638508443323817)
  ·
    refine ⟨5288247099478881332492863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7050996132638508443323817 5288247099478881332492863)
    ·
      refine ⟨7932370649218321998739295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5288247099478881332492863 7932370649218321998739295)
      ·
        refine ⟨11898555973827482998108943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7932370649218321998739295 11898555973827482998108943)
        ·
          refine ⟨17847833960741224497163415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11898555973827482998108943 17847833960741224497163415)
          ·
            refine ⟨26771750941111836745745123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17847833960741224497163415 26771750941111836745745123)
            ·
              refine ⟨40157626411667755118617685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26771750941111836745745123 40157626411667755118617685)
              ·
                refine ⟨470597184511731505296301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 40157626411667755118617685 470597184511731505296301)
                ·
                  refine ⟨176473944191899314486113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 470597184511731505296301 176473944191899314486113)
                  ·
                    refine ⟨132355458143924485864585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 176473944191899314486113 132355458143924485864585)
                    ·
                      refine ⟨99266593607943364398439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 132355458143924485864585 99266593607943364398439)
                      ·
                        rfl

theorem cell23_193321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 8, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 8, 3, 2, 2].length) (baseStart_193321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_193321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_193321 prefixEnd_193321 := by exact prefixLift 193321
  have htrace : WordTrace (prefixWord ++ tailWord_193321) baseStart_193321 baseEnd_193321 := by
    simpa [prefixWord, tailWord_193321, baseEnd_193321] using wordTrace_append hprefix tailTrace_193321
  have hstable : (prefixWord ++ tailWord_193321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193321).length < 2 ^ (prefixWord ++ tailWord_193321).sum := by decide
  have hdescent : baseEnd_193321 < baseStart_193321 := by decide
  rcases family_descends (prefixWord ++ tailWord_193321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193324 : List Nat := [2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 3]
def baseStart_193324 : Nat := 118140960795 + 193324 * 2 ^ 59
def prefixEnd_193324 : Nat := 4983230072969 + 3 ^ 40 * 193324 * 2
def baseEnd_193324 : Nat := 99268134049906852660925

theorem tailTrace_193324 : CollatzResearch.WordTrace tailWord_193324 prefixEnd_193324 99268134049906852660925 := by
  unfold tailWord_193324
  simp only [CollatzResearch.WordTrace]
  refine ⟨3525552775813819977841513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4700737034418426637122017 3525552775813819977841513)
  ·
    refine ⟨2644164581860364983381135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3525552775813819977841513 2644164581860364983381135)
    ·
      refine ⟨3966246872790547475071703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2644164581860364983381135 3966246872790547475071703)
      ·
        refine ⟨5949370309185821212607555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3966246872790547475071703 5949370309185821212607555)
        ·
          refine ⟨8924055463778731818911333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5949370309185821212607555 8924055463778731818911333)
          ·
            refine ⟨1673260399458512216045875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8924055463778731818911333 1673260399458512216045875)
            ·
              refine ⟨2509890599187768324068813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1673260399458512216045875 2509890599187768324068813)
              ·
                refine ⟨941208974695413121525805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2509890599187768324068813 941208974695413121525805)
                ·
                  refine ⟨352953365510779920572177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 941208974695413121525805 352953365510779920572177)
                  ·
                    refine ⟨264715024133084940429133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 352953365510779920572177 264715024133084940429133)
                    ·
                      refine ⟨99268134049906852660925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 264715024133084940429133 99268134049906852660925)
                      ·
                        rfl

theorem cell23_193324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 3].length) (baseStart_193324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_193324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_193324 prefixEnd_193324 := by exact prefixLift 193324
  have htrace : WordTrace (prefixWord ++ tailWord_193324) baseStart_193324 baseEnd_193324 := by
    simpa [prefixWord, tailWord_193324, baseEnd_193324] using wordTrace_append hprefix tailTrace_193324
  have hstable : (prefixWord ++ tailWord_193324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193324).length < 2 ^ (prefixWord ++ tailWord_193324).sum := by decide
  have hdescent : baseEnd_193324 < baseStart_193324 := by decide
  rcases family_descends (prefixWord ++ tailWord_193324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193325 : List Nat := [1, 5, 3, 2, 1, 1, 1, 1, 1, 5, 2]
def baseStart_193325 : Nat := 118140960795 + 193325 * 2 ^ 59
def prefixEnd_193325 : Nat := 4983230072969 + 3 ^ 40 * 193325 * 2
def baseEnd_193325 : Nat := 99268647530561348748421

theorem tailTrace_193325 : CollatzResearch.WordTrace tailWord_193325 prefixEnd_193325 99268647530561348748421 := by
  unfold tailWord_193325
  simp only [CollatzResearch.WordTrace]
  refine ⟨7051142024624017126469429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4700761349749344750979619 7051142024624017126469429)
  ·
    refine ⟨661044564808501605606509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7051142024624017126469429 661044564808501605606509)
    ·
      refine ⟨247891711803188102102441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 661044564808501605606509 247891711803188102102441)
      ·
        refine ⟨185918783852391076576831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 247891711803188102102441 185918783852391076576831)
        ·
          refine ⟨278878175778586614865247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185918783852391076576831 278878175778586614865247)
          ·
            refine ⟨418317263667879922297871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 278878175778586614865247 418317263667879922297871)
            ·
              refine ⟨627475895501819883446807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 418317263667879922297871 627475895501819883446807)
              ·
                refine ⟨941213843252729825170211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 627475895501819883446807 941213843252729825170211)
                ·
                  refine ⟨1411820764879094737755317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 941213843252729825170211 1411820764879094737755317)
                  ·
                    refine ⟨132358196707415131664561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1411820764879094737755317 132358196707415131664561)
                    ·
                      refine ⟨99268647530561348748421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 132358196707415131664561 99268647530561348748421)
                      ·
                        rfl

theorem cell23_193325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_193325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_193325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_193325 prefixEnd_193325 := by exact prefixLift 193325
  have htrace : WordTrace (prefixWord ++ tailWord_193325) baseStart_193325 baseEnd_193325 := by
    simpa [prefixWord, tailWord_193325, baseEnd_193325] using wordTrace_append hprefix tailTrace_193325
  have hstable : (prefixWord ++ tailWord_193325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193325).length < 2 ^ (prefixWord ++ tailWord_193325).sum := by decide
  have hdescent : baseEnd_193325 < baseStart_193325 := by decide
  rcases family_descends (prefixWord ++ tailWord_193325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193332 : List Nat := [2, 5, 1, 1, 3, 1, 2, 3, 1, 1, 3]
def baseStart_193332 : Nat := 118140960795 + 193332 * 2 ^ 59
def prefixEnd_193332 : Nat := 4983230072969 + 3 ^ 40 * 193332 * 2
def baseEnd_193332 : Nat := 99272241895142821360889

theorem tailTrace_193332 : CollatzResearch.WordTrace tailWord_193332 prefixEnd_193332 99272241895142821360889 := by
  unfold tailWord_193332
  simp only [CollatzResearch.WordTrace]
  refine ⟨3525698667799328660987125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4700931557065771547982833 3525698667799328660987125)
  ·
    refine ⟨330534250106187061967543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3525698667799328660987125 330534250106187061967543)
    ·
      refine ⟨495801375159280592951315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 330534250106187061967543 495801375159280592951315)
      ·
        refine ⟨743702062738920889426973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 495801375159280592951315 743702062738920889426973)
        ·
          refine ⟨278888273527095333535115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 743702062738920889426973 278888273527095333535115)
          ·
            refine ⟨418332410290643000302673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 278888273527095333535115 418332410290643000302673)
            ·
              refine ⟨313749307717982250227005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 418332410290643000302673 313749307717982250227005)
              ·
                refine ⟨117655990394243343835127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 313749307717982250227005 117655990394243343835127)
                ·
                  refine ⟨176483985591365015752691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 117655990394243343835127 176483985591365015752691)
                  ·
                    refine ⟨264725978387047523629037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 176483985591365015752691 264725978387047523629037)
                    ·
                      refine ⟨99272241895142821360889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 264725978387047523629037 99272241895142821360889)
                      ·
                        rfl

theorem cell23_193332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 2, 3, 1, 1, 3].length) (baseStart_193332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_193332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_193332 prefixEnd_193332 := by exact prefixLift 193332
  have htrace : WordTrace (prefixWord ++ tailWord_193332) baseStart_193332 baseEnd_193332 := by
    simpa [prefixWord, tailWord_193332, baseEnd_193332] using wordTrace_append hprefix tailTrace_193332
  have hstable : (prefixWord ++ tailWord_193332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193332).length < 2 ^ (prefixWord ++ tailWord_193332).sum := by decide
  have hdescent : baseEnd_193332 < baseStart_193332 := by decide
  rcases family_descends (prefixWord ++ tailWord_193332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193377 : List Nat := [1, 2, 3, 1, 1, 1, 2, 1, 1, 2, 8]
def baseStart_193377 : Nat := 118140960795 + 193377 * 2 ^ 59
def prefixEnd_193377 : Nat := 4983230072969 + 3 ^ 40 * 193377 * 2
def baseEnd_193377 : Nat := 99295348524595145298181

theorem tailTrace_193377 : CollatzResearch.WordTrace tailWord_193377 prefixEnd_193377 99295348524595145298181 := by
  unfold tailWord_193377
  simp only [CollatzResearch.WordTrace]
  refine ⟨7053038620435630007362385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4702025746957086671574923 7053038620435630007362385)
  ·
    refine ⟨5289778965326722505521789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7053038620435630007362385 5289778965326722505521789)
    ·
      refine ⟨1983667111997520939570671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5289778965326722505521789 1983667111997520939570671)
      ·
        refine ⟨2975500667996281409356007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1983667111997520939570671 2975500667996281409356007)
        ·
          refine ⟨4463251001994422114034011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2975500667996281409356007 4463251001994422114034011)
          ·
            refine ⟨6694876502991633171051017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4463251001994422114034011 6694876502991633171051017)
            ·
              refine ⟨5021157377243724878288263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6694876502991633171051017 5021157377243724878288263)
              ·
                refine ⟨7531736065865587317432395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5021157377243724878288263 7531736065865587317432395)
                ·
                  refine ⟨11297604098798380976148593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7531736065865587317432395 11297604098798380976148593)
                  ·
                    refine ⟨8473203074098785732111445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11297604098798380976148593 8473203074098785732111445)
                    ·
                      refine ⟨99295348524595145298181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 8473203074098785732111445 99295348524595145298181)
                      ·
                        rfl

theorem cell23_193377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 2, 8].length) (baseStart_193377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_193377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_193377 prefixEnd_193377 := by exact prefixLift 193377
  have htrace : WordTrace (prefixWord ++ tailWord_193377) baseStart_193377 baseEnd_193377 := by
    simpa [prefixWord, tailWord_193377, baseEnd_193377] using wordTrace_append hprefix tailTrace_193377
  have hstable : (prefixWord ++ tailWord_193377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193377).length < 2 ^ (prefixWord ++ tailWord_193377).sum := by decide
  have hdescent : baseEnd_193377 < baseStart_193377 := by decide
  rcases family_descends (prefixWord ++ tailWord_193377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193378 : List Nat := [3, 3, 2, 1, 3, 2, 2, 7]
def baseStart_193378 : Nat := 118140960795 + 193378 * 2 ^ 59
def prefixEnd_193378 : Nat := 4983230072969 + 3 ^ 40 * 193378 * 2
def baseEnd_193378 : Nat := 3677624518712949680951

theorem tailTrace_193378 : CollatzResearch.WordTrace tailWord_193378 prefixEnd_193378 3677624518712949680951 := by
  unfold tailWord_193378
  simp only [CollatzResearch.WordTrace]
  refine ⟨1763268773358001794537197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4702050062288004785432525 1763268773358001794537197)
  ·
    refine ⟨661225790009250672951449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1763268773358001794537197 661225790009250672951449)
    ·
      refine ⟨495919342506938004713587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 661225790009250672951449 495919342506938004713587)
      ·
        refine ⟨743879013760407007070381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 495919342506938004713587 743879013760407007070381)
        ·
          refine ⟨278954630160152627651393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 743879013760407007070381 278954630160152627651393)
          ·
            refine ⟨209215972620114470738545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 278954630160152627651393 209215972620114470738545)
            ·
              refine ⟨156911979465085853053909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 209215972620114470738545 156911979465085853053909)
              ·
                refine ⟨3677624518712949680951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 156911979465085853053909 3677624518712949680951)
                ·
                  rfl

theorem cell23_193378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 2, 7].length) (baseStart_193378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_193378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_193378 prefixEnd_193378 := by exact prefixLift 193378
  have htrace : WordTrace (prefixWord ++ tailWord_193378) baseStart_193378 baseEnd_193378 := by
    simpa [prefixWord, tailWord_193378, baseEnd_193378] using wordTrace_append hprefix tailTrace_193378
  have hstable : (prefixWord ++ tailWord_193378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193378).length < 2 ^ (prefixWord ++ tailWord_193378).sum := by decide
  have hdescent : baseEnd_193378 < baseStart_193378 := by decide
  rcases family_descends (prefixWord ++ tailWord_193378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193381 : List Nat := [1, 3, 1, 3, 1, 1, 2, 3, 3, 3, 2]
def baseStart_193381 : Nat := 118140960795 + 193381 * 2 ^ 59
def prefixEnd_193381 : Nat := 4983230072969 + 3 ^ 40 * 193381 * 2
def baseEnd_193381 : Nat := 99297402447213129648163

theorem tailTrace_193381 : CollatzResearch.WordTrace tailWord_193381 prefixEnd_193381 99297402447213129648163 := by
  unfold tailWord_193381
  simp only [CollatzResearch.WordTrace]
  refine ⟨7053184512421138690507997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4702123008280759127005331 7053184512421138690507997)
  ·
    refine ⟨2644944192157927008940499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7053184512421138690507997 2644944192157927008940499)
    ·
      refine ⟨3967416288236890513410749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2644944192157927008940499 3967416288236890513410749)
      ·
        refine ⟨1487781108088833942529031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3967416288236890513410749 1487781108088833942529031)
        ·
          refine ⟨2231671662133250913793547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1487781108088833942529031 2231671662133250913793547)
          ·
            refine ⟨3347507493199876370690321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2231671662133250913793547 3347507493199876370690321)
            ·
              refine ⟨2510630619899907278017741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3347507493199876370690321 2510630619899907278017741)
              ·
                refine ⟨941486482462465229256653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2510630619899907278017741 941486482462465229256653)
                ·
                  refine ⟨353057430923424460971245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 941486482462465229256653 353057430923424460971245)
                  ·
                    refine ⟨132396536596284172864217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 353057430923424460971245 132396536596284172864217)
                    ·
                      refine ⟨99297402447213129648163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 132396536596284172864217 99297402447213129648163)
                      ·
                        rfl

theorem cell23_193381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 3, 3, 3, 2].length) (baseStart_193381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_193381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_193381 prefixEnd_193381 := by exact prefixLift 193381
  have htrace : WordTrace (prefixWord ++ tailWord_193381) baseStart_193381 baseEnd_193381 := by
    simpa [prefixWord, tailWord_193381, baseEnd_193381] using wordTrace_append hprefix tailTrace_193381
  have hstable : (prefixWord ++ tailWord_193381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193381).length < 2 ^ (prefixWord ++ tailWord_193381).sum := by decide
  have hdescent : baseEnd_193381 < baseStart_193381 := by decide
  rcases family_descends (prefixWord ++ tailWord_193381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193384 : List Nat := [2, 1, 4, 2, 1, 2, 1, 1, 2, 2, 5]
def baseStart_193384 : Nat := 118140960795 + 193384 * 2 ^ 59
def prefixEnd_193384 : Nat := 4983230072969 + 3 ^ 40 * 193384 * 2
def baseEnd_193384 : Nat := 99298942889176617910649

theorem tailTrace_193384 : CollatzResearch.WordTrace tailWord_193384 prefixEnd_193384 99298942889176617910649 := by
  unfold tailWord_193384
  simp only [CollatzResearch.WordTrace]
  refine ⟨3526646965705135101433603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4702195954273513468578137 3526646965705135101433603)
  ·
    refine ⟨5289970448557702652150405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3526646965705135101433603 5289970448557702652150405)
    ·
      refine ⟨991869459104569247278201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5289970448557702652150405 991869459104569247278201)
      ·
        refine ⟨743902094328426935458651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 991869459104569247278201 743902094328426935458651)
        ·
          refine ⟨1115853141492640403187977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 743902094328426935458651 1115853141492640403187977)
          ·
            refine ⟨836889856119480302390983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1115853141492640403187977 836889856119480302390983)
            ·
              refine ⟨1255334784179220453586475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 836889856119480302390983 1255334784179220453586475)
              ·
                refine ⟨1883002176268830680379713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1255334784179220453586475 1883002176268830680379713)
                ·
                  refine ⟨1412251632201623010284785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1883002176268830680379713 1412251632201623010284785)
                  ·
                    refine ⟨1059188724151217257713589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1412251632201623010284785 1059188724151217257713589)
                    ·
                      refine ⟨99298942889176617910649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1059188724151217257713589 99298942889176617910649)
                      ·
                        rfl

theorem cell23_193384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_193384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_193384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_193384 prefixEnd_193384 := by exact prefixLift 193384
  have htrace : WordTrace (prefixWord ++ tailWord_193384) baseStart_193384 baseEnd_193384 := by
    simpa [prefixWord, tailWord_193384, baseEnd_193384] using wordTrace_append hprefix tailTrace_193384
  have hstable : (prefixWord ++ tailWord_193384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193384).length < 2 ^ (prefixWord ++ tailWord_193384).sum := by decide
  have hdescent : baseEnd_193384 < baseStart_193384 := by decide
  rcases family_descends (prefixWord ++ tailWord_193384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193387 : List Nat := [1, 1, 1, 1, 2, 2, 4, 2, 1, 8]
def baseStart_193387 : Nat := 118140960795 + 193387 * 2 ^ 59
def prefixEnd_193387 : Nat := 4983230072969 + 3 ^ 40 * 193387 * 2
def baseEnd_193387 : Nat := 33100161110380035391045

theorem tailTrace_193387 : CollatzResearch.WordTrace tailWord_193387 prefixEnd_193387 33100161110380035391045 := by
  unfold tailWord_193387
  simp only [CollatzResearch.WordTrace]
  refine ⟨7053403350399401715226415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4702268900266267810150943 7053403350399401715226415)
  ·
    refine ⟨10580105025599102572839623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7053403350399401715226415 10580105025599102572839623)
    ·
      refine ⟨15870157538398653859259435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10580105025599102572839623 15870157538398653859259435)
      ·
        refine ⟨23805236307597980788889153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15870157538398653859259435 23805236307597980788889153)
        ·
          refine ⟨17853927230698485591666865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23805236307597980788889153 17853927230698485591666865)
          ·
            refine ⟨13390445423023864193750149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17853927230698485591666865 13390445423023864193750149)
            ·
              refine ⟨2510708516816974536328153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13390445423023864193750149 2510708516816974536328153)
              ·
                refine ⟨1883031387612730902246115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2510708516816974536328153 1883031387612730902246115)
                ·
                  refine ⟨2824547081419096353369173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1883031387612730902246115 2824547081419096353369173)
                  ·
                    refine ⟨33100161110380035391045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 2824547081419096353369173 33100161110380035391045)
                    ·
                      rfl

theorem cell23_193387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 2, 1, 8].length) (baseStart_193387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_193387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_193387 prefixEnd_193387 := by exact prefixLift 193387
  have htrace : WordTrace (prefixWord ++ tailWord_193387) baseStart_193387 baseEnd_193387 := by
    simpa [prefixWord, tailWord_193387, baseEnd_193387] using wordTrace_append hprefix tailTrace_193387
  have hstable : (prefixWord ++ tailWord_193387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193387).length < 2 ^ (prefixWord ++ tailWord_193387).sum := by decide
  have hdescent : baseEnd_193387 < baseStart_193387 := by decide
  rcases family_descends (prefixWord ++ tailWord_193387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193406 : List Nat := [4, 2, 3, 1, 2, 1, 3, 2, 1, 2, 2]
def baseStart_193406 : Nat := 118140960795 + 193406 * 2 ^ 59
def prefixEnd_193406 : Nat := 4983230072969 + 3 ^ 40 * 193406 * 2
def baseEnd_193406 : Nat := 99310239463575531835549

theorem tailTrace_193406 : CollatzResearch.WordTrace tailWord_193406 prefixEnd_193406 99310239463575531835549 := by
  unfold tailWord_193406
  simp only [CollatzResearch.WordTrace]
  refine ⟨881762042166320995021009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4702730891553711973445381 881762042166320995021009)
  ·
    refine ⟨661321531624740746265757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 881762042166320995021009 661321531624740746265757)
    ·
      refine ⟨247995574359277779849659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 661321531624740746265757 247995574359277779849659)
      ·
        refine ⟨371993361538916669774489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247995574359277779849659 371993361538916669774489)
        ·
          refine ⟨278995021154187502330867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 371993361538916669774489 278995021154187502330867)
          ·
            refine ⟨418492531731281253496301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 278995021154187502330867 418492531731281253496301)
            ·
              refine ⟨156934699399230470061113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 418492531731281253496301 156934699399230470061113)
              ·
                refine ⟨117701024549422852545835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 156934699399230470061113 117701024549422852545835)
                ·
                  refine ⟨176551536824134278818753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 117701024549422852545835 176551536824134278818753)
                  ·
                    refine ⟨132413652618100709114065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 176551536824134278818753 132413652618100709114065)
                    ·
                      refine ⟨99310239463575531835549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 132413652618100709114065 99310239463575531835549)
                      ·
                        rfl

theorem cell23_193406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 3, 2, 1, 2, 2].length) (baseStart_193406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_193406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_193406 prefixEnd_193406 := by exact prefixLift 193406
  have htrace : WordTrace (prefixWord ++ tailWord_193406) baseStart_193406 baseEnd_193406 := by
    simpa [prefixWord, tailWord_193406, baseEnd_193406] using wordTrace_append hprefix tailTrace_193406
  have hstable : (prefixWord ++ tailWord_193406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193406).length < 2 ^ (prefixWord ++ tailWord_193406).sum := by decide
  have hdescent : baseEnd_193406 < baseStart_193406 := by decide
  rcases family_descends (prefixWord ++ tailWord_193406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193428 : List Nat := [2, 4, 2, 1, 1, 1, 2, 3, 1, 4, 2]
def baseStart_193428 : Nat := 118140960795 + 193428 * 2 ^ 59
def prefixEnd_193428 : Nat := 4983230072969 + 3 ^ 40 * 193428 * 2
def baseEnd_193428 : Nat := 99321536037974445760447

theorem tailTrace_193428 : CollatzResearch.WordTrace tailWord_193428 prefixEnd_193428 99321536037974445760447 := by
  unfold tailWord_193428
  simp only [CollatzResearch.WordTrace]
  refine ⟨3527449371625432858734469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4703265828833910478312625 3527449371625432858734469)
  ·
    refine ⟨661396757179768661012713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3527449371625432858734469 661396757179768661012713)
    ·
      refine ⟨496047567884826495759535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 661396757179768661012713 496047567884826495759535)
      ·
        refine ⟨744071351827239743639303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 496047567884826495759535 744071351827239743639303)
        ·
          refine ⟨1116107027740859615458955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 744071351827239743639303 1116107027740859615458955)
          ·
            refine ⟨1674160541611289423188433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1116107027740859615458955 1674160541611289423188433)
            ·
              refine ⟨1255620406208467067391325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1674160541611289423188433 1255620406208467067391325)
              ·
                refine ⟨470857652328175150271747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1255620406208467067391325 470857652328175150271747)
                ·
                  refine ⟨706286478492262725407621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 470857652328175150271747 706286478492262725407621)
                  ·
                    refine ⟨132428714717299261013929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 706286478492262725407621 132428714717299261013929)
                    ·
                      refine ⟨99321536037974445760447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 132428714717299261013929 99321536037974445760447)
                      ·
                        rfl

theorem cell23_193428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 3, 1, 4, 2].length) (baseStart_193428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_193428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_193428 prefixEnd_193428 := by exact prefixLift 193428
  have htrace : WordTrace (prefixWord ++ tailWord_193428) baseStart_193428 baseEnd_193428 := by
    simpa [prefixWord, tailWord_193428, baseEnd_193428] using wordTrace_append hprefix tailTrace_193428
  have hstable : (prefixWord ++ tailWord_193428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193428).length < 2 ^ (prefixWord ++ tailWord_193428).sum := by decide
  have hdescent : baseEnd_193428 < baseStart_193428 := by decide
  rcases family_descends (prefixWord ++ tailWord_193428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193461 : List Nat := [1, 3, 3, 2, 1, 1, 2, 2, 2, 3, 3]
def baseStart_193461 : Nat := 118140960795 + 193461 * 2 ^ 59
def prefixEnd_193461 : Nat := 4983230072969 + 3 ^ 40 * 193461 * 2
def baseEnd_193461 : Nat := 99338480899572816647795

theorem tailTrace_193461 : CollatzResearch.WordTrace tailWord_193461 prefixEnd_193461 99338480899572816647795 := by
  unfold tailWord_193461
  simp only [CollatzResearch.WordTrace]
  refine ⟨7056102352131312353420237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4704068234754208235613491 7056102352131312353420237)
  ·
    refine ⟨2646038382049242132532589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7056102352131312353420237 2646038382049242132532589)
    ·
      refine ⟨992264393268465799699721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2646038382049242132532589 992264393268465799699721)
      ·
        refine ⟨744198294951349349774791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 992264393268465799699721 744198294951349349774791)
        ·
          refine ⟨1116297442427024024662187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 744198294951349349774791 1116297442427024024662187)
          ·
            refine ⟨1674446163640536036993281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1116297442427024024662187 1674446163640536036993281)
            ·
              refine ⟨1255834622730402027744961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1674446163640536036993281 1255834622730402027744961)
              ·
                refine ⟨941875967047801520808721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1255834622730402027744961 941875967047801520808721)
                ·
                  refine ⟨706406975285851140606541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 941875967047801520808721 706406975285851140606541)
                  ·
                    refine ⟨264902615732194177727453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 706406975285851140606541 264902615732194177727453)
                    ·
                      refine ⟨99338480899572816647795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 264902615732194177727453 99338480899572816647795)
                      ·
                        rfl

theorem cell23_193461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 2, 2, 3, 3].length) (baseStart_193461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_193461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_193461 prefixEnd_193461 := by exact prefixLift 193461
  have htrace : WordTrace (prefixWord ++ tailWord_193461) baseStart_193461 baseEnd_193461 := by
    simpa [prefixWord, tailWord_193461, baseEnd_193461] using wordTrace_append hprefix tailTrace_193461
  have hstable : (prefixWord ++ tailWord_193461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193461).length < 2 ^ (prefixWord ++ tailWord_193461).sum := by decide
  have hdescent : baseEnd_193461 < baseStart_193461 := by decide
  rcases family_descends (prefixWord ++ tailWord_193461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193498 : List Nat := [3, 1, 1, 2, 4, 3, 1, 1, 2, 5]
def baseStart_193498 : Nat := 118140960795 + 193498 * 2 ^ 59
def prefixEnd_193498 : Nat := 4983230072969 + 3 ^ 40 * 193498 * 2
def baseEnd_193498 : Nat := 33119159894596390628375

theorem tailTrace_193498 : CollatzResearch.WordTrace tailWord_193498 prefixEnd_193498 33119159894596390628375 := by
  unfold tailWord_193498
  simp only [CollatzResearch.WordTrace]
  refine ⟨1764362963249316918129287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4704967901998178448344765 1764362963249316918129287)
  ·
    refine ⟨2646544444873975377193931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1764362963249316918129287 2646544444873975377193931)
    ·
      refine ⟨3969816667310963065790897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2646544444873975377193931 3969816667310963065790897)
      ·
        refine ⟨2977362500483222299343173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3969816667310963065790897 2977362500483222299343173)
        ·
          refine ⟨558255468840604181126845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2977362500483222299343173 558255468840604181126845)
          ·
            refine ⟨209345800815226567922567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 558255468840604181126845 209345800815226567922567)
            ·
              refine ⟨314018701222839851883851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 209345800815226567922567 314018701222839851883851)
              ·
                refine ⟨471028051834259777825777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 314018701222839851883851 471028051834259777825777)
                ·
                  refine ⟨353271038875694833369333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 471028051834259777825777 353271038875694833369333)
                  ·
                    refine ⟨33119159894596390628375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 353271038875694833369333 33119159894596390628375)
                    ·
                      rfl

theorem cell23_193498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 5].length) (baseStart_193498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_193498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_193498 prefixEnd_193498 := by exact prefixLift 193498
  have htrace : WordTrace (prefixWord ++ tailWord_193498) baseStart_193498 baseEnd_193498 := by
    simpa [prefixWord, tailWord_193498, baseEnd_193498] using wordTrace_append hprefix tailTrace_193498
  have hstable : (prefixWord ++ tailWord_193498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193498).length < 2 ^ (prefixWord ++ tailWord_193498).sum := by decide
  have hdescent : baseEnd_193498 < baseStart_193498 := by decide
  rcases family_descends (prefixWord ++ tailWord_193498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193591 : List Nat := [1, 1, 3, 1, 2, 2, 1, 4, 3, 1, 4]
def baseStart_193591 : Nat := 118140960795 + 193591 * 2 ^ 59
def prefixEnd_193591 : Nat := 4983230072969 + 3 ^ 40 * 193591 * 2
def baseEnd_193591 : Nat := 99405233384657308022197

theorem tailTrace_193591 : CollatzResearch.WordTrace tailWord_193591 prefixEnd_193591 99405233384657308022197 := by
  unfold tailWord_193591
  simp only [CollatzResearch.WordTrace]
  refine ⟨7060843841660344555652627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4707229227773563037101751 7060843841660344555652627)
  ·
    refine ⟨10591265762490516833478941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7060843841660344555652627 10591265762490516833478941)
    ·
      refine ⟨3971724660933943812554603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10591265762490516833478941 3971724660933943812554603)
      ·
        refine ⟨5957586991400915718831905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3971724660933943812554603 5957586991400915718831905)
        ·
          refine ⟨4468190243550686789123929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5957586991400915718831905 4468190243550686789123929)
          ·
            refine ⟨3351142682663015091842947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4468190243550686789123929 3351142682663015091842947)
            ·
              refine ⟨5026714023994522637764421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3351142682663015091842947 5026714023994522637764421)
              ·
                refine ⟨942508879498972994580829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5026714023994522637764421 942508879498972994580829)
                ·
                  refine ⟨353440829812114872967811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 942508879498972994580829 353440829812114872967811)
                  ·
                    refine ⟨530161244718172309451717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 353440829812114872967811 530161244718172309451717)
                    ·
                      refine ⟨99405233384657308022197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 530161244718172309451717 99405233384657308022197)
                      ·
                        rfl

theorem cell23_193591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 4, 3, 1, 4].length) (baseStart_193591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_193591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_193591 prefixEnd_193591 := by exact prefixLift 193591
  have htrace : WordTrace (prefixWord ++ tailWord_193591) baseStart_193591 baseEnd_193591 := by
    simpa [prefixWord, tailWord_193591, baseEnd_193591] using wordTrace_append hprefix tailTrace_193591
  have hstable : (prefixWord ++ tailWord_193591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193591).length < 2 ^ (prefixWord ++ tailWord_193591).sum := by decide
  have hdescent : baseEnd_193591 < baseStart_193591 := by decide
  rcases family_descends (prefixWord ++ tailWord_193591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193618 : List Nat := [3, 2, 2, 1, 3, 2, 1, 2, 1, 6]
def baseStart_193618 : Nat := 118140960795 + 193618 * 2 ^ 59
def prefixEnd_193618 : Nat := 4983230072969 + 3 ^ 40 * 193618 * 2
def baseEnd_193618 : Nat := 33139699120776234128191

theorem tailTrace_193618 : CollatzResearch.WordTrace tailWord_193618 prefixEnd_193618 33139699120776234128191 := by
  unfold tailWord_193618
  simp only [CollatzResearch.WordTrace]
  refine ⟨1765457153140632041721377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4707885741708352111257005 1765457153140632041721377)
  ·
    refine ⟨1324092864855474031291033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1765457153140632041721377 1324092864855474031291033)
    ·
      refine ⟨993069648641605523468275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1324092864855474031291033 993069648641605523468275)
      ·
        refine ⟨1489604472962408285202413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 993069648641605523468275 1489604472962408285202413)
        ·
          refine ⟨558601677360903106950905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1489604472962408285202413 558601677360903106950905)
          ·
            refine ⟨418951258020677330213179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 558601677360903106950905 418951258020677330213179)
            ·
              refine ⟨628426887031015995319769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 418951258020677330213179 628426887031015995319769)
              ·
                refine ⟨471320165273261996489827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 628426887031015995319769 471320165273261996489827)
                ·
                  refine ⟨706980247909892994734741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 471320165273261996489827 706980247909892994734741)
                  ·
                    refine ⟨33139699120776234128191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 706980247909892994734741 33139699120776234128191)
                    ·
                      rfl

theorem cell23_193618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 2, 1, 6].length) (baseStart_193618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_193618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_193618 prefixEnd_193618 := by exact prefixLift 193618
  have htrace : WordTrace (prefixWord ++ tailWord_193618) baseStart_193618 baseEnd_193618 := by
    simpa [prefixWord, tailWord_193618, baseEnd_193618] using wordTrace_append hprefix tailTrace_193618
  have hstable : (prefixWord ++ tailWord_193618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193618).length < 2 ^ (prefixWord ++ tailWord_193618).sum := by decide
  have hdescent : baseEnd_193618 < baseStart_193618 := by decide
  rcases family_descends (prefixWord ++ tailWord_193618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193661 : List Nat := [1, 4, 1, 1, 3, 1, 1, 2, 2, 7]
def baseStart_193661 : Nat := 118140960795 + 193661 * 2 ^ 59
def prefixEnd_193661 : Nat := 4983230072969 + 3 ^ 40 * 193661 * 2
def baseEnd_193661 : Nat := 33147059010157344715625

theorem tailTrace_193661 : CollatzResearch.WordTrace tailWord_193661 prefixEnd_193661 33147059010157344715625 := by
  unfold tailWord_193661
  simp only [CollatzResearch.WordTrace]
  refine ⟨7063396951406746510700837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4708931300937831007133891 7063396951406746510700837)
  ·
    refine ⟨1324386928388764970756407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7063396951406746510700837 1324386928388764970756407)
    ·
      refine ⟨1986580392583147456134611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1324386928388764970756407 1986580392583147456134611)
      ·
        refine ⟨2979870588874721184201917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1986580392583147456134611 2979870588874721184201917)
        ·
          refine ⟨1117451470828020444075719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2979870588874721184201917 1117451470828020444075719)
          ·
            refine ⟨1676177206242030666113579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1117451470828020444075719 1676177206242030666113579)
            ·
              refine ⟨2514265809363045999170369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1676177206242030666113579 2514265809363045999170369)
              ·
                refine ⟨1885699357022284499377777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2514265809363045999170369 1885699357022284499377777)
                ·
                  refine ⟨1414274517766713374533333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1885699357022284499377777 1414274517766713374533333)
                  ·
                    refine ⟨33147059010157344715625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1414274517766713374533333 33147059010157344715625)
                    ·
                      rfl

theorem cell23_193661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 2, 2, 7].length) (baseStart_193661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_193661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_193661 prefixEnd_193661 := by exact prefixLift 193661
  have htrace : WordTrace (prefixWord ++ tailWord_193661) baseStart_193661 baseEnd_193661 := by
    simpa [prefixWord, tailWord_193661, baseEnd_193661] using wordTrace_append hprefix tailTrace_193661
  have hstable : (prefixWord ++ tailWord_193661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193661).length < 2 ^ (prefixWord ++ tailWord_193661).sum := by decide
  have hdescent : baseEnd_193661 < baseStart_193661 := by decide
  rcases family_descends (prefixWord ++ tailWord_193661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193671 : List Nat := [1, 1, 4, 2, 1, 1, 1, 3, 2, 2, 5]
def baseStart_193671 : Nat := 118140960795 + 193671 * 2 ^ 59
def prefixEnd_193671 : Nat := 4983230072969 + 3 ^ 40 * 193671 * 2
def baseEnd_193671 : Nat := 99446311837016995021829

theorem tailTrace_193671 : CollatzResearch.WordTrace tailWord_193671 prefixEnd_193671 99446311837016995021829 := by
  unfold tailWord_193671
  simp only [CollatzResearch.WordTrace]
  refine ⟨7063761681370518218564867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4709174454247012145709911 7063761681370518218564867)
  ·
    refine ⟨10595642522055777327847301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7063761681370518218564867 10595642522055777327847301)
    ·
      refine ⟨1986682972885458248971369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10595642522055777327847301 1986682972885458248971369)
      ·
        refine ⟨1490012229664093686728527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1986682972885458248971369 1490012229664093686728527)
        ·
          refine ⟨2235018344496140530092791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1490012229664093686728527 2235018344496140530092791)
          ·
            refine ⟨3352527516744210795139187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2235018344496140530092791 3352527516744210795139187)
            ·
              refine ⟨5028791275116316192708781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3352527516744210795139187 5028791275116316192708781)
              ·
                refine ⟨1885796728168618572265793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5028791275116316192708781 1885796728168618572265793)
                ·
                  refine ⟨1414347546126463929199345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1885796728168618572265793 1414347546126463929199345)
                  ·
                    refine ⟨1060760659594847946899509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1414347546126463929199345 1060760659594847946899509)
                    ·
                      refine ⟨99446311837016995021829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1060760659594847946899509 99446311837016995021829)
                      ·
                        rfl

theorem cell23_193671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 3, 2, 2, 5].length) (baseStart_193671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_193671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_193671 prefixEnd_193671 := by exact prefixLift 193671
  have htrace : WordTrace (prefixWord ++ tailWord_193671) baseStart_193671 baseEnd_193671 := by
    simpa [prefixWord, tailWord_193671, baseEnd_193671] using wordTrace_append hprefix tailTrace_193671
  have hstable : (prefixWord ++ tailWord_193671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193671).length < 2 ^ (prefixWord ++ tailWord_193671).sum := by decide
  have hdescent : baseEnd_193671 < baseStart_193671 := by decide
  rcases family_descends (prefixWord ++ tailWord_193671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193692 : List Nat := [2, 2, 3, 2, 1, 2, 3, 2, 2, 1, 3]
def baseStart_193692 : Nat := 118140960795 + 193692 * 2 ^ 59
def prefixEnd_193692 : Nat := 4983230072969 + 3 ^ 40 * 193692 * 2
def baseEnd_193692 : Nat := 99457094930761412859233

theorem tailTrace_193692 : CollatzResearch.WordTrace tailWord_193692 prefixEnd_193692 99457094930761412859233 := by
  unfold tailWord_193692
  simp only [CollatzResearch.WordTrace]
  refine ⟨3532263807147219402539665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4709685076196292536719553 3532263807147219402539665)
  ·
    refine ⟨2649197855360414551904749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3532263807147219402539665 2649197855360414551904749)
    ·
      refine ⟨993449195760155456964281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2649197855360414551904749 993449195760155456964281)
      ·
        refine ⟨745086896820116592723211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 993449195760155456964281 745086896820116592723211)
        ·
          refine ⟨1117630345230174889084817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 745086896820116592723211 1117630345230174889084817)
          ·
            refine ⟨838222758922631166813613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1117630345230174889084817 838222758922631166813613)
            ·
              refine ⟨314333534595986687555105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 838222758922631166813613 314333534595986687555105)
              ·
                refine ⟨235750150946990015666329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 314333534595986687555105 235750150946990015666329)
                ·
                  refine ⟨176812613210242511749747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 235750150946990015666329 176812613210242511749747)
                  ·
                    refine ⟨265218919815363767624621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 176812613210242511749747 265218919815363767624621)
                    ·
                      refine ⟨99457094930761412859233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 265218919815363767624621 99457094930761412859233)
                      ·
                        rfl

theorem cell23_193692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 3, 2, 2, 1, 3].length) (baseStart_193692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_193692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_193692 prefixEnd_193692 := by exact prefixLift 193692
  have htrace : WordTrace (prefixWord ++ tailWord_193692) baseStart_193692 baseEnd_193692 := by
    simpa [prefixWord, tailWord_193692, baseEnd_193692] using wordTrace_append hprefix tailTrace_193692
  have hstable : (prefixWord ++ tailWord_193692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193692).length < 2 ^ (prefixWord ++ tailWord_193692).sum := by decide
  have hdescent : baseEnd_193692 < baseStart_193692 := by decide
  rcases family_descends (prefixWord ++ tailWord_193692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193709 : List Nat := [1, 5, 2, 1, 4, 1, 1, 1, 1, 3, 3]
def baseStart_193709 : Nat := 118140960795 + 193709 * 2 ^ 59
def prefixEnd_193709 : Nat := 4983230072969 + 3 ^ 40 * 193709 * 2
def baseEnd_193709 : Nat := 99465824101887846346655

theorem tailTrace_193709 : CollatzResearch.WordTrace tailWord_193709 prefixEnd_193709 99465824101887846346655 := by
  unfold tailWord_193709
  simp only [CollatzResearch.WordTrace]
  refine ⟨7065147655232850708448181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4710098436821900472298787 7065147655232850708448181)
  ·
    refine ⟨662357592678079753917017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7065147655232850708448181 662357592678079753917017)
    ·
      refine ⟨496768194508559815437763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 662357592678079753917017 496768194508559815437763)
      ·
        refine ⟨745152291762839723156645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 496768194508559815437763 745152291762839723156645)
        ·
          refine ⟨139716054705532448091871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 745152291762839723156645 139716054705532448091871)
          ·
            refine ⟨209574082058298672137807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139716054705532448091871 209574082058298672137807)
            ·
              refine ⟨314361123087448008206711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 209574082058298672137807 314361123087448008206711)
              ·
                refine ⟨471541684631172012310067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 314361123087448008206711 471541684631172012310067)
                ·
                  refine ⟨707312526946758018465101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 471541684631172012310067 707312526946758018465101)
                  ·
                    refine ⟨265242197605034256924413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 707312526946758018465101 265242197605034256924413)
                    ·
                      refine ⟨99465824101887846346655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 265242197605034256924413 99465824101887846346655)
                      ·
                        rfl

theorem cell23_193709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 1, 1, 1, 3, 3].length) (baseStart_193709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_193709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_193709 prefixEnd_193709 := by exact prefixLift 193709
  have htrace : WordTrace (prefixWord ++ tailWord_193709) baseStart_193709 baseEnd_193709 := by
    simpa [prefixWord, tailWord_193709, baseEnd_193709] using wordTrace_append hprefix tailTrace_193709
  have hstable : (prefixWord ++ tailWord_193709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193709).length < 2 ^ (prefixWord ++ tailWord_193709).sum := by decide
  have hdescent : baseEnd_193709 < baseStart_193709 := by decide
  rcases family_descends (prefixWord ++ tailWord_193709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193715 : List Nat := [1, 1, 1, 2, 3, 2, 5, 1, 1, 4, 2]
def baseStart_193715 : Nat := 118140960795 + 193715 * 2 ^ 59
def prefixEnd_193715 : Nat := 4983230072969 + 3 ^ 40 * 193715 * 2
def baseEnd_193715 : Nat := 99468904985814822871627

theorem tailTrace_193715 : CollatzResearch.WordTrace tailWord_193715 prefixEnd_193715 99468904985814822871627 := by
  unfold tailWord_193715
  simp only [CollatzResearch.WordTrace]
  refine ⟨7065366493211113733166599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4710244328807409155444399 7065366493211113733166599)
  ·
    refine ⟨10598049739816670599749899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7065366493211113733166599 10598049739816670599749899)
    ·
      refine ⟨15897074609725005899624849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10598049739816670599749899 15897074609725005899624849)
      ·
        refine ⟨11922805957293754424718637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15897074609725005899624849 11922805957293754424718637)
        ·
          refine ⟨4471052233985157909269489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11922805957293754424718637 4471052233985157909269489)
          ·
            refine ⟨3353289175488868431952117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4471052233985157909269489 3353289175488868431952117)
            ·
              refine ⟨314370860202081415495511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3353289175488868431952117 314370860202081415495511)
              ·
                refine ⟨471556290303122123243267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 314370860202081415495511 471556290303122123243267)
                ·
                  refine ⟨707334435454683184864901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 471556290303122123243267 707334435454683184864901)
                  ·
                    refine ⟨132625206647753097162169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 707334435454683184864901 132625206647753097162169)
                    ·
                      refine ⟨99468904985814822871627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 132625206647753097162169 99468904985814822871627)
                      ·
                        rfl

theorem cell23_193715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 5, 1, 1, 4, 2].length) (baseStart_193715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_193715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_193715 prefixEnd_193715 := by exact prefixLift 193715
  have htrace : WordTrace (prefixWord ++ tailWord_193715) baseStart_193715 baseEnd_193715 := by
    simpa [prefixWord, tailWord_193715, baseEnd_193715] using wordTrace_append hprefix tailTrace_193715
  have hstable : (prefixWord ++ tailWord_193715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193715).length < 2 ^ (prefixWord ++ tailWord_193715).sum := by decide
  have hdescent : baseEnd_193715 < baseStart_193715 := by decide
  rcases family_descends (prefixWord ++ tailWord_193715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193768 : List Nat := [2, 1, 4, 1, 2, 1, 1, 2, 4, 5]
def baseStart_193768 : Nat := 118140960795 + 193768 * 2 ^ 59
def prefixEnd_193768 : Nat := 4983230072969 + 3 ^ 40 * 193768 * 2
def baseEnd_193768 : Nat := 33165373153501038502961

theorem tailTrace_193768 : CollatzResearch.WordTrace tailWord_193768 prefixEnd_193768 33165373153501038502961 := by
  unfold tailWord_193768
  simp only [CollatzResearch.WordTrace]
  refine ⟨3533649781009551892422979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4711533041346069189897305 3533649781009551892422979)
  ·
    refine ⟨5300474671514327838634469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3533649781009551892422979 5300474671514327838634469)
    ·
      refine ⟨993839000908936469743963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5300474671514327838634469 993839000908936469743963)
      ·
        refine ⟨1490758501363404704615945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 993839000908936469743963 1490758501363404704615945)
        ·
          refine ⟨1118068876022553528461959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1490758501363404704615945 1118068876022553528461959)
          ·
            refine ⟨1677103314033830292692939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1118068876022553528461959 1677103314033830292692939)
            ·
              refine ⟨2515654971050745439039409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1677103314033830292692939 2515654971050745439039409)
              ·
                refine ⟨1886741228288059079279557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2515654971050745439039409 1886741228288059079279557)
                ·
                  refine ⟨353763980304011077364917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1886741228288059079279557 353763980304011077364917)
                  ·
                    refine ⟨33165373153501038502961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 353763980304011077364917 33165373153501038502961)
                    ·
                      rfl

theorem cell23_193768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 2, 4, 5].length) (baseStart_193768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_193768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_193768 prefixEnd_193768 := by exact prefixLift 193768
  have htrace : WordTrace (prefixWord ++ tailWord_193768) baseStart_193768 baseEnd_193768 := by
    simpa [prefixWord, tailWord_193768, baseEnd_193768] using wordTrace_append hprefix tailTrace_193768
  have hstable : (prefixWord ++ tailWord_193768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193768).length < 2 ^ (prefixWord ++ tailWord_193768).sum := by decide
  have hdescent : baseEnd_193768 < baseStart_193768 := by decide
  rcases family_descends (prefixWord ++ tailWord_193768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193815 : List Nat := [1, 1, 3, 4, 1, 1, 2, 3, 3, 4]
def baseStart_193815 : Nat := 118140960795 + 193815 * 2 ^ 59
def prefixEnd_193815 : Nat := 4983230072969 + 3 ^ 40 * 193815 * 2
def baseEnd_193815 : Nat := 33173417683754810540389

theorem tailTrace_193815 : CollatzResearch.WordTrace tailWord_193815 prefixEnd_193815 33173417683754810540389 := by
  unfold tailWord_193815
  simp only [CollatzResearch.WordTrace]
  refine ⟨7069013792848830811806899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4712675861899220541204599 7069013792848830811806899)
  ·
    refine ⟨10603520689273246217710349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7069013792848830811806899 10603520689273246217710349)
    ·
      refine ⟨3976320258477467331641381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10603520689273246217710349 3976320258477467331641381)
      ·
        refine ⟨745560048464525124682759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3976320258477467331641381 745560048464525124682759)
        ·
          refine ⟨1118340072696787687024139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 745560048464525124682759 1118340072696787687024139)
          ·
            refine ⟨1677510109045181530536209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1118340072696787687024139 1677510109045181530536209)
            ·
              refine ⟨1258132581783886147902157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1677510109045181530536209 1258132581783886147902157)
              ·
                refine ⟨471799718168957305463309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1258132581783886147902157 471799718168957305463309)
                ·
                  refine ⟨176924894313358989548741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 471799718168957305463309 176924894313358989548741)
                  ·
                    refine ⟨33173417683754810540389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 176924894313358989548741 33173417683754810540389)
                    ·
                      rfl

theorem cell23_193815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 3, 3, 4].length) (baseStart_193815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_193815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_193815 prefixEnd_193815 := by exact prefixLift 193815
  have htrace : WordTrace (prefixWord ++ tailWord_193815) baseStart_193815 baseEnd_193815 := by
    simpa [prefixWord, tailWord_193815, baseEnd_193815] using wordTrace_append hprefix tailTrace_193815
  have hstable : (prefixWord ++ tailWord_193815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193815).length < 2 ^ (prefixWord ++ tailWord_193815).sum := by decide
  have hdescent : baseEnd_193815 < baseStart_193815 := by decide
  rcases family_descends (prefixWord ++ tailWord_193815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193832 : List Nat := [2, 1, 5, 1, 2, 2, 1, 2, 3, 4]
def baseStart_193832 : Nat := 118140960795 + 193832 * 2 ^ 59
def prefixEnd_193832 : Nat := 4983230072969 + 3 ^ 40 * 193832 * 2
def baseEnd_193832 : Nat := 33176327407463621702863

theorem tailTrace_193832 : CollatzResearch.WordTrace tailWord_193832 prefixEnd_193832 33176327407463621702863 := by
  unfold tailWord_193832
  simp only [CollatzResearch.WordTrace]
  refine ⟨3534816916893621357587875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4713089222524828476783833 3534816916893621357587875)
  ·
    refine ⟨5302225375340432036381813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3534816916893621357587875 5302225375340432036381813)
    ·
      refine ⟨497083628938165503410795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5302225375340432036381813 497083628938165503410795)
      ·
        refine ⟨745625443407248255116193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 497083628938165503410795 745625443407248255116193)
        ·
          refine ⟨559219082555436191337145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 745625443407248255116193 559219082555436191337145)
          ·
            refine ⟨419414311916577143502859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 559219082555436191337145 419414311916577143502859)
            ·
              refine ⟨629121467874865715254289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 419414311916577143502859 629121467874865715254289)
              ·
                refine ⟨471841100906149286440717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 629121467874865715254289 471841100906149286440717)
                ·
                  refine ⟨176940412839805982415269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 471841100906149286440717 176940412839805982415269)
                  ·
                    refine ⟨33176327407463621702863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 176940412839805982415269 33176327407463621702863)
                    ·
                      rfl

theorem cell23_193832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 2, 3, 4].length) (baseStart_193832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_193832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_193832 prefixEnd_193832 := by exact prefixLift 193832
  have htrace : WordTrace (prefixWord ++ tailWord_193832) baseStart_193832 baseEnd_193832 := by
    simpa [prefixWord, tailWord_193832, baseEnd_193832] using wordTrace_append hprefix tailTrace_193832
  have hstable : (prefixWord ++ tailWord_193832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193832).length < 2 ^ (prefixWord ++ tailWord_193832).sum := by decide
  have hdescent : baseEnd_193832 < baseStart_193832 := by decide
  rcases family_descends (prefixWord ++ tailWord_193832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193842 : List Nat := [3, 2, 1, 1, 4, 1, 3, 1, 2, 2, 3]
def baseStart_193842 : Nat := 118140960795 + 193842 * 2 ^ 59
def prefixEnd_193842 : Nat := 4983230072969 + 3 ^ 40 * 193842 * 2
def baseEnd_193842 : Nat := 99534117028935825983543

theorem tailTrace_193842 : CollatzResearch.WordTrace tailWord_193842 prefixEnd_193842 99534117028935825983543 := by
  unfold tailWord_193842
  simp only [CollatzResearch.WordTrace]
  refine ⟨1767499640937753605759945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4713332375834009615359853 1767499640937753605759945)
  ·
    refine ⟨1325624730703315204319959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1767499640937753605759945 1325624730703315204319959)
    ·
      refine ⟨1988437096054972806479939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1325624730703315204319959 1988437096054972806479939)
      ·
        refine ⟨2982655644082459209719909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1988437096054972806479939 2982655644082459209719909)
        ·
          refine ⟨559247933265461101822483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2982655644082459209719909 559247933265461101822483)
          ·
            refine ⟨838871899898191652733725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 559247933265461101822483 838871899898191652733725)
            ·
              refine ⟨314576962461821869775147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 838871899898191652733725 314576962461821869775147)
              ·
                refine ⟨471865443692732804662721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 314576962461821869775147 471865443692732804662721)
                ·
                  refine ⟨353899082769549603497041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 471865443692732804662721 353899082769549603497041)
                  ·
                    refine ⟨265424312077162202622781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 353899082769549603497041 265424312077162202622781)
                    ·
                      refine ⟨99534117028935825983543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 265424312077162202622781 99534117028935825983543)
                      ·
                        rfl

theorem cell23_193842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 3, 1, 2, 2, 3].length) (baseStart_193842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_193842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_193842 prefixEnd_193842 := by exact prefixLift 193842
  have htrace : WordTrace (prefixWord ++ tailWord_193842) baseStart_193842 baseEnd_193842 := by
    simpa [prefixWord, tailWord_193842, baseEnd_193842] using wordTrace_append hprefix tailTrace_193842
  have hstable : (prefixWord ++ tailWord_193842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193842).length < 2 ^ (prefixWord ++ tailWord_193842).sum := by decide
  have hdescent : baseEnd_193842 < baseStart_193842 := by decide
  rcases family_descends (prefixWord ++ tailWord_193842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193872 : List Nat := [2, 1, 1, 1, 1, 5, 4, 1, 3, 1, 3]
def baseStart_193872 : Nat := 118140960795 + 193872 * 2 ^ 59
def prefixEnd_193872 : Nat := 4983230072969 + 3 ^ 40 * 193872 * 2
def baseEnd_193872 : Nat := 99549521448570708608405

theorem tailTrace_193872 : CollatzResearch.WordTrace tailWord_193872 prefixEnd_193872 99549521448570708608405 := by
  unfold tailWord_193872
  simp only [CollatzResearch.WordTrace]
  refine ⟨3535546376821164773315935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4714061835761553031087913 3535546376821164773315935)
  ·
    refine ⟨5303319565231747159973903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3535546376821164773315935 5303319565231747159973903)
    ·
      refine ⟨7954979347847620739960855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5303319565231747159973903 7954979347847620739960855)
      ·
        refine ⟨11932469021771431109941283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7954979347847620739960855 11932469021771431109941283)
        ·
          refine ⟨17898703532657146664911925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11932469021771431109941283 17898703532657146664911925)
          ·
            refine ⟨1678003456186607499835493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17898703532657146664911925 1678003456186607499835493)
            ·
              refine ⟨314625648034988906219155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1678003456186607499835493 314625648034988906219155)
              ·
                refine ⟨471938472052483359328733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 314625648034988906219155 471938472052483359328733)
                ·
                  refine ⟨176976927019681259748275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 471938472052483359328733 176976927019681259748275)
                  ·
                    refine ⟨265465390529521889622413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 176976927019681259748275 265465390529521889622413)
                    ·
                      refine ⟨99549521448570708608405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 265465390529521889622413 99549521448570708608405)
                      ·
                        rfl

theorem cell23_193872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 4, 1, 3, 1, 3].length) (baseStart_193872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_193872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_193872 prefixEnd_193872 := by exact prefixLift 193872
  have htrace : WordTrace (prefixWord ++ tailWord_193872) baseStart_193872 baseEnd_193872 := by
    simpa [prefixWord, tailWord_193872, baseEnd_193872] using wordTrace_append hprefix tailTrace_193872
  have hstable : (prefixWord ++ tailWord_193872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193872).length < 2 ^ (prefixWord ++ tailWord_193872).sum := by decide
  have hdescent : baseEnd_193872 < baseStart_193872 := by decide
  rcases family_descends (prefixWord ++ tailWord_193872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193892 : List Nat := [2, 3, 1, 1, 3, 3, 2, 2, 1, 5]
def baseStart_193892 : Nat := 118140960795 + 193892 * 2 ^ 59
def prefixEnd_193892 : Nat := 4983230072969 + 3 ^ 40 * 193892 * 2
def baseEnd_193892 : Nat := 33186597020553543452771

theorem tailTrace_193892 : CollatzResearch.WordTrace tailWord_193892 prefixEnd_193892 33186597020553543452771 := by
  unfold tailWord_193892
  simp only [CollatzResearch.WordTrace]
  refine ⟨3535911106784936481179965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4714548142379915308239953 3535911106784936481179965)
  ·
    refine ⟨1325966665044351180442487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3535911106784936481179965 1325966665044351180442487)
    ·
      refine ⟨1988949997566526770663731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1325966665044351180442487 1988949997566526770663731)
      ·
        refine ⟨2983424996349790155995597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1988949997566526770663731 2983424996349790155995597)
        ·
          refine ⟨1118784373631171308498349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2983424996349790155995597 1118784373631171308498349)
          ·
            refine ⟨419544140111689240686881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1118784373631171308498349 419544140111689240686881)
            ·
              refine ⟨314658105083766930515161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 419544140111689240686881 314658105083766930515161)
              ·
                refine ⟨235993578812825197886371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 314658105083766930515161 235993578812825197886371)
                ·
                  refine ⟨353990368219237796829557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 235993578812825197886371 353990368219237796829557)
                  ·
                    refine ⟨33186597020553543452771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 353990368219237796829557 33186597020553543452771)
                    ·
                      rfl

theorem cell23_193892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 2, 2, 1, 5].length) (baseStart_193892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_193892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_193892 prefixEnd_193892 := by exact prefixLift 193892
  have htrace : WordTrace (prefixWord ++ tailWord_193892) baseStart_193892 baseEnd_193892 := by
    simpa [prefixWord, tailWord_193892, baseEnd_193892] using wordTrace_append hprefix tailTrace_193892
  have hstable : (prefixWord ++ tailWord_193892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193892).length < 2 ^ (prefixWord ++ tailWord_193892).sum := by decide
  have hdescent : baseEnd_193892 < baseStart_193892 := by decide
  rcases family_descends (prefixWord ++ tailWord_193892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193905 : List Nat := [1, 2, 2, 2, 1, 2, 3, 2, 4, 4]
def baseStart_193905 : Nat := 118140960795 + 193905 * 2 ^ 59
def prefixEnd_193905 : Nat := 4983230072969 + 3 ^ 40 * 193905 * 2
def baseEnd_193905 : Nat := 33188822103389693165251

theorem tailTrace_193905 : CollatzResearch.WordTrace tailWord_193905 prefixEnd_193905 33188822103389693165251 := by
  unfold tailWord_193905
  simp only [CollatzResearch.WordTrace]
  refine ⟨7072296362522776182583169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4714864241681850788388779 7072296362522776182583169)
  ·
    refine ⟨5304222271892082136937377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7072296362522776182583169 5304222271892082136937377)
    ·
      refine ⟨3978166703919061602703033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5304222271892082136937377 3978166703919061602703033)
      ·
        refine ⟨2983625027939296202027275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3978166703919061602703033 2983625027939296202027275)
        ·
          refine ⟨4475437541908944303040913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2983625027939296202027275 4475437541908944303040913)
          ·
            refine ⟨3356578156431708227280685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4475437541908944303040913 3356578156431708227280685)
            ·
              refine ⟨1258716808661890585230257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3356578156431708227280685 1258716808661890585230257)
              ·
                refine ⟨944037606496417938922693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1258716808661890585230257 944037606496417938922693)
                ·
                  refine ⟨177007051218078363548005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 944037606496417938922693 177007051218078363548005)
                  ·
                    refine ⟨33188822103389693165251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 177007051218078363548005 33188822103389693165251)
                    ·
                      rfl

theorem cell23_193905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 2, 4, 4].length) (baseStart_193905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_193905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_193905 prefixEnd_193905 := by exact prefixLift 193905
  have htrace : WordTrace (prefixWord ++ tailWord_193905) baseStart_193905 baseEnd_193905 := by
    simpa [prefixWord, tailWord_193905, baseEnd_193905] using wordTrace_append hprefix tailTrace_193905
  have hstable : (prefixWord ++ tailWord_193905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193905).length < 2 ^ (prefixWord ++ tailWord_193905).sum := by decide
  have hdescent : baseEnd_193905 < baseStart_193905 := by decide
  rcases family_descends (prefixWord ++ tailWord_193905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193915 : List Nat := [1, 1, 1, 1, 1, 6, 4, 1, 1, 1, 5]
def baseStart_193915 : Nat := 118140960795 + 193915 * 2 ^ 59
def prefixEnd_193915 : Nat := 4983230072969 + 3 ^ 40 * 193915 * 2
def baseEnd_193915 : Nat := 99571601116714040370707

theorem tailTrace_193915 : CollatzResearch.WordTrace tailWord_193915 prefixEnd_193915 99571601116714040370707 := by
  unfold tailWord_193915
  simp only [CollatzResearch.WordTrace]
  refine ⟨7072661092486547890447199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4715107394991031926964799 7072661092486547890447199)
  ·
    refine ⟨10608991638729821835670799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7072661092486547890447199 10608991638729821835670799)
    ·
      refine ⟨15913487458094732753506199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10608991638729821835670799 15913487458094732753506199)
      ·
        refine ⟨23870231187142099130259299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15913487458094732753506199 23870231187142099130259299)
        ·
          refine ⟨35805346780713148695388949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23870231187142099130259299 35805346780713148695388949)
          ·
            refine ⟨1678375630345928845096357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 35805346780713148695388949 1678375630345928845096357)
            ·
              refine ⟨314695430689861658455567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1678375630345928845096357 314695430689861658455567)
              ·
                refine ⟨472043146034792487683351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 314695430689861658455567 472043146034792487683351)
                ·
                  refine ⟨708064719052188731525027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 472043146034792487683351 708064719052188731525027)
                  ·
                    refine ⟨1062097078578283097287541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 708064719052188731525027 1062097078578283097287541)
                    ·
                      refine ⟨99571601116714040370707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1062097078578283097287541 99571601116714040370707)
                      ·
                        rfl

theorem cell23_193915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 4, 1, 1, 1, 5].length) (baseStart_193915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_193915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_193915 prefixEnd_193915 := by exact prefixLift 193915
  have htrace : WordTrace (prefixWord ++ tailWord_193915) baseStart_193915 baseEnd_193915 := by
    simpa [prefixWord, tailWord_193915, baseEnd_193915] using wordTrace_append hprefix tailTrace_193915
  have hstable : (prefixWord ++ tailWord_193915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193915).length < 2 ^ (prefixWord ++ tailWord_193915).sum := by decide
  have hdescent : baseEnd_193915 < baseStart_193915 := by decide
  rcases family_descends (prefixWord ++ tailWord_193915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_193949 : List Nat := [1, 4, 2, 1, 3, 1, 3, 2, 1, 2, 3]
def baseStart_193949 : Nat := 118140960795 + 193949 * 2 ^ 59
def prefixEnd_193949 : Nat := 4983230072969 + 3 ^ 40 * 193949 * 2
def baseEnd_193949 : Nat := 99589059458966907345551

theorem tailTrace_193949 : CollatzResearch.WordTrace tailWord_193949 prefixEnd_193949 99589059458966907345551 := by
  unfold tailWord_193949
  simp only [CollatzResearch.WordTrace]
  refine ⟨7073901174363371697184901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4715934116242247798123267 7073901174363371697184901)
  ·
    refine ⟨1326356470193132193222169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7073901174363371697184901 1326356470193132193222169)
    ·
      refine ⟨994767352644849144916627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1326356470193132193222169 994767352644849144916627)
      ·
        refine ⟨1492151028967273717374941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 994767352644849144916627 1492151028967273717374941)
        ·
          refine ⟨559556635862727644015603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1492151028967273717374941 559556635862727644015603)
          ·
            refine ⟨839334953794091466023405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 559556635862727644015603 839334953794091466023405)
            ·
              refine ⟨314750607672784299758777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 839334953794091466023405 314750607672784299758777)
              ·
                refine ⟨236062955754588224819083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 314750607672784299758777 236062955754588224819083)
                ·
                  refine ⟨354094433631882337228625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 236062955754588224819083 354094433631882337228625)
                  ·
                    refine ⟨265570825223911752921469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 354094433631882337228625 265570825223911752921469)
                    ·
                      refine ⟨99589059458966907345551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 265570825223911752921469 99589059458966907345551)
                      ·
                        rfl

theorem cell23_193949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 3, 2, 1, 2, 3].length) (baseStart_193949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_193949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_193949 prefixEnd_193949 := by exact prefixLift 193949
  have htrace : WordTrace (prefixWord ++ tailWord_193949) baseStart_193949 baseEnd_193949 := by
    simpa [prefixWord, tailWord_193949, baseEnd_193949] using wordTrace_append hprefix tailTrace_193949
  have hstable : (prefixWord ++ tailWord_193949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_193949).length < 2 ^ (prefixWord ++ tailWord_193949).sum := by decide
  have hdescent : baseEnd_193949 < baseStart_193949 := by decide
  rcases family_descends (prefixWord ++ tailWord_193949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194006 : List Nat := [5, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2]
def baseStart_194006 : Nat := 118140960795 + 194006 * 2 ^ 59
def prefixEnd_194006 : Nat := 4983230072969 + 3 ^ 40 * 194006 * 2
def baseEnd_194006 : Nat := 99618327856273184332789

theorem tailTrace_194006 : CollatzResearch.WordTrace tailWord_194006 prefixEnd_194006 99618327856273184332789 := by
  unfold tailWord_194006
  simp only [CollatzResearch.WordTrace]
  refine ⟨442248758447304402000617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4717320090104580288006581 442248758447304402000617)
  ·
    refine ⟨331686568835478301500463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 442248758447304402000617 331686568835478301500463)
    ·
      refine ⟨497529853253217452250695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 331686568835478301500463 497529853253217452250695)
      ·
        refine ⟨746294779879826178376043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 497529853253217452250695 746294779879826178376043)
        ·
          refine ⟨1119442169819739267564065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 746294779879826178376043 1119442169819739267564065)
          ·
            refine ⟨839581627364804450673049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1119442169819739267564065 839581627364804450673049)
            ·
              refine ⟨629686220523603338004787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 839581627364804450673049 629686220523603338004787)
              ·
                refine ⟨944529330785405007007181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 629686220523603338004787 944529330785405007007181)
                ·
                  refine ⟨354198499044526877627693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 944529330785405007007181 354198499044526877627693)
                  ·
                    refine ⟨132824437141697579110385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 354198499044526877627693 132824437141697579110385)
                    ·
                      refine ⟨99618327856273184332789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 132824437141697579110385 99618327856273184332789)
                      ·
                        rfl

theorem cell23_194006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2].length) (baseStart_194006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_194006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_194006 prefixEnd_194006 := by exact prefixLift 194006
  have htrace : WordTrace (prefixWord ++ tailWord_194006) baseStart_194006 baseEnd_194006 := by
    simpa [prefixWord, tailWord_194006, baseEnd_194006] using wordTrace_append hprefix tailTrace_194006
  have hstable : (prefixWord ++ tailWord_194006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194006).length < 2 ^ (prefixWord ++ tailWord_194006).sum := by decide
  have hdescent : baseEnd_194006 < baseStart_194006 := by decide
  rcases family_descends (prefixWord ++ tailWord_194006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194015 : List Nat := [1, 1, 2, 3, 3, 1, 1, 2, 1, 4, 4]
def baseStart_194015 : Nat := 118140960795 + 194015 * 2 ^ 59
def prefixEnd_194015 : Nat := 4983230072969 + 3 ^ 40 * 194015 * 2
def baseEnd_194015 : Nat := 99622949182163649120247

theorem tailTrace_194015 : CollatzResearch.WordTrace tailWord_194015 prefixEnd_194015 99622949182163649120247 := by
  unfold tailWord_194015
  simp only [CollatzResearch.WordTrace]
  refine ⟨7076308392124264969087499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4717538928082843312724999 7076308392124264969087499)
  ·
    refine ⟨10614462588186397453631249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7076308392124264969087499 10614462588186397453631249)
    ·
      refine ⟨7960846941139798090223437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10614462588186397453631249 7960846941139798090223437)
      ·
        refine ⟨2985317602927424283833789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7960846941139798090223437 2985317602927424283833789)
        ·
          refine ⟨1119494101097784106437671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2985317602927424283833789 1119494101097784106437671)
          ·
            refine ⟨1679241151646676159656507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1119494101097784106437671 1679241151646676159656507)
            ·
              refine ⟨2518861727470014239484761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1679241151646676159656507 2518861727470014239484761)
              ·
                refine ⟨1889146295602510679613571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2518861727470014239484761 1889146295602510679613571)
                ·
                  refine ⟨2833719443403766019420357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1889146295602510679613571 2833719443403766019420357)
                  ·
                    refine ⟨531322395638206128641317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2833719443403766019420357 531322395638206128641317)
                    ·
                      refine ⟨99622949182163649120247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 531322395638206128641317 99622949182163649120247)
                      ·
                        rfl

theorem cell23_194015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 2, 1, 4, 4].length) (baseStart_194015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_194015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_194015 prefixEnd_194015 := by exact prefixLift 194015
  have htrace : WordTrace (prefixWord ++ tailWord_194015) baseStart_194015 baseEnd_194015 := by
    simpa [prefixWord, tailWord_194015, baseEnd_194015] using wordTrace_append hprefix tailTrace_194015
  have hstable : (prefixWord ++ tailWord_194015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194015).length < 2 ^ (prefixWord ++ tailWord_194015).sum := by decide
  have hdescent : baseEnd_194015 < baseStart_194015 := by decide
  rcases family_descends (prefixWord ++ tailWord_194015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194019 : List Nat := [1, 1, 1, 6, 2, 1, 2, 2, 1, 4, 2]
def baseStart_194019 : Nat := 118140960795 + 194019 * 2 ^ 59
def prefixEnd_194019 : Nat := 4983230072969 + 3 ^ 40 * 194019 * 2
def baseEnd_194019 : Nat := 99625003104781633470229

theorem tailTrace_194019 : CollatzResearch.WordTrace tailWord_194019 prefixEnd_194019 99625003104781633470229 := by
  unfold tailWord_194019
  simp only [CollatzResearch.WordTrace]
  refine ⟨7076454284109773652233111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4717636189406515768155407 7076454284109773652233111)
  ·
    refine ⟨10614681426164660478349667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7076454284109773652233111 10614681426164660478349667)
    ·
      refine ⟨15922022139246990717524501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10614681426164660478349667 15922022139246990717524501)
      ·
        refine ⟨746344787777202689883961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 15922022139246990717524501 746344787777202689883961)
        ·
          refine ⟨559758590832902017412971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 746344787777202689883961 559758590832902017412971)
          ·
            refine ⟨839637886249353026119457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 559758590832902017412971 839637886249353026119457)
            ·
              refine ⟨629728414687014769589593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 839637886249353026119457 629728414687014769589593)
              ·
                refine ⟨472296311015261077192195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 629728414687014769589593 472296311015261077192195)
                ·
                  refine ⟨708444466522891615788293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 472296311015261077192195 708444466522891615788293)
                  ·
                    refine ⟨132833337473042177960305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 708444466522891615788293 132833337473042177960305)
                    ·
                      refine ⟨99625003104781633470229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 132833337473042177960305 99625003104781633470229)
                      ·
                        rfl

theorem cell23_194019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 2, 1, 4, 2].length) (baseStart_194019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_194019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_194019 prefixEnd_194019 := by exact prefixLift 194019
  have htrace : WordTrace (prefixWord ++ tailWord_194019) baseStart_194019 baseEnd_194019 := by
    simpa [prefixWord, tailWord_194019, baseEnd_194019] using wordTrace_append hprefix tailTrace_194019
  have hstable : (prefixWord ++ tailWord_194019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194019).length < 2 ^ (prefixWord ++ tailWord_194019).sum := by decide
  have hdescent : baseEnd_194019 < baseStart_194019 := by decide
  rcases family_descends (prefixWord ++ tailWord_194019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194023 : List Nat := [1, 1, 5, 2, 1, 4, 2, 1, 1, 3, 2]
def baseStart_194023 : Nat := 118140960795 + 194023 * 2 ^ 59
def prefixEnd_194023 : Nat := 4983230072969 + 3 ^ 40 * 194023 * 2
def baseEnd_194023 : Nat := 99627057027399617820211

theorem tailTrace_194023 : CollatzResearch.WordTrace tailWord_194023 prefixEnd_194023 99627057027399617820211 := by
  unfold tailWord_194023
  simp only [CollatzResearch.WordTrace]
  refine ⟨7076600176095282335378723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4717733450730188223585815 7076600176095282335378723)
  ·
    refine ⟨10614900264142923503068085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7076600176095282335378723 10614900264142923503068085)
    ·
      refine ⟨995146899763399078412633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10614900264142923503068085 995146899763399078412633)
      ·
        refine ⟨746360174822549308809475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 995146899763399078412633 746360174822549308809475)
        ·
          refine ⟨1119540262233823963214213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 746360174822549308809475 1119540262233823963214213)
          ·
            refine ⟨209913799168841993102665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1119540262233823963214213 209913799168841993102665)
            ·
              refine ⟨157435349376631494826999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 209913799168841993102665 157435349376631494826999)
              ·
                refine ⟨236153024064947242240499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 157435349376631494826999 236153024064947242240499)
                ·
                  refine ⟨354229536097420863360749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 236153024064947242240499 354229536097420863360749)
                  ·
                    refine ⟨132836076036532823760281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 354229536097420863360749 132836076036532823760281)
                    ·
                      refine ⟨99627057027399617820211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 132836076036532823760281 99627057027399617820211)
                      ·
                        rfl

theorem cell23_194023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 2, 1, 1, 3, 2].length) (baseStart_194023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_194023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_194023 prefixEnd_194023 := by exact prefixLift 194023
  have htrace : WordTrace (prefixWord ++ tailWord_194023) baseStart_194023 baseEnd_194023 := by
    simpa [prefixWord, tailWord_194023, baseEnd_194023] using wordTrace_append hprefix tailTrace_194023
  have hstable : (prefixWord ++ tailWord_194023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194023).length < 2 ^ (prefixWord ++ tailWord_194023).sum := by decide
  have hdescent : baseEnd_194023 < baseStart_194023 := by decide
  rcases family_descends (prefixWord ++ tailWord_194023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194042 : List Nat := [3, 1, 1, 1, 1, 2, 3, 6, 5]
def baseStart_194042 : Nat := 118140960795 + 194042 * 2 ^ 59
def prefixEnd_194042 : Nat := 4983230072969 + 3 ^ 40 * 194042 * 2
def baseEnd_194042 : Nat := 11070757017759449275847

theorem tailTrace_194042 : CollatzResearch.WordTrace tailWord_194042 prefixEnd_194042 11070757017759449275847 := by
  unfold tailWord_194042
  simp only [CollatzResearch.WordTrace]
  refine ⟨1769323290756612145080095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4718195442017632386880253 1769323290756612145080095)
  ·
    refine ⟨2653984936134918217620143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1769323290756612145080095 2653984936134918217620143)
    ·
      refine ⟨3980977404202377326430215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2653984936134918217620143 3980977404202377326430215)
      ·
        refine ⟨5971466106303565989645323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3980977404202377326430215 5971466106303565989645323)
        ·
          refine ⟨8957199159455348984467985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5971466106303565989645323 8957199159455348984467985)
          ·
            refine ⟨6717899369591511738350989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8957199159455348984467985 6717899369591511738350989)
            ·
              refine ⟨2519212263596816901881621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6717899369591511738350989 2519212263596816901881621)
              ·
                refine ⟨118088074856100792275701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2519212263596816901881621 118088074856100792275701)
                ·
                  refine ⟨11070757017759449275847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 118088074856100792275701 11070757017759449275847)
                  ·
                    rfl

theorem cell23_194042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 6, 5].length) (baseStart_194042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_194042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_194042 prefixEnd_194042 := by exact prefixLift 194042
  have htrace : WordTrace (prefixWord ++ tailWord_194042) baseStart_194042 baseEnd_194042 := by
    simpa [prefixWord, tailWord_194042, baseEnd_194042] using wordTrace_append hprefix tailTrace_194042
  have hstable : (prefixWord ++ tailWord_194042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194042).length < 2 ^ (prefixWord ++ tailWord_194042).sum := by decide
  have hdescent : baseEnd_194042 < baseStart_194042 := by decide
  rcases family_descends (prefixWord ++ tailWord_194042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194112 : List Nat := [2, 1, 1, 2, 2, 2, 1, 1, 6, 2, 3]
def baseStart_194112 : Nat := 118140960795 + 194112 * 2 ^ 59
def prefixEnd_194112 : Nat := 4983230072969 + 3 ^ 40 * 194112 * 2
def baseEnd_194112 : Nat := 99672756805649769607301

theorem tailTrace_194112 : CollatzResearch.WordTrace tailWord_194112 prefixEnd_194112 99672756805649769607301 := by
  unfold tailWord_194112
  simp only [CollatzResearch.WordTrace]
  refine ⟨3539923136386425267684295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4719897515181900356912393 3539923136386425267684295)
  ·
    refine ⟨5309884704579637901526443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3539923136386425267684295 5309884704579637901526443)
    ·
      refine ⟨7964827056869456852289665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5309884704579637901526443 7964827056869456852289665)
      ·
        refine ⟨5973620292652092639217249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7964827056869456852289665 5973620292652092639217249)
        ·
          refine ⟨4480215219489069479412937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5973620292652092639217249 4480215219489069479412937)
          ·
            refine ⟨3360161414616802109559703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4480215219489069479412937 3360161414616802109559703)
            ·
              refine ⟨5040242121925203164339555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3360161414616802109559703 5040242121925203164339555)
              ·
                refine ⟨7560363182887804746509333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5040242121925203164339555 7560363182887804746509333)
                ·
                  refine ⟨354392024197865847492625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7560363182887804746509333 354392024197865847492625)
                  ·
                    refine ⟨265794018148399385619469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 354392024197865847492625 265794018148399385619469)
                    ·
                      refine ⟨99672756805649769607301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 265794018148399385619469 99672756805649769607301)
                      ·
                        rfl

theorem cell23_194112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 6, 2, 3].length) (baseStart_194112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_194112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_194112 prefixEnd_194112 := by exact prefixLift 194112
  have htrace : WordTrace (prefixWord ++ tailWord_194112) baseStart_194112 baseEnd_194112 := by
    simpa [prefixWord, tailWord_194112, baseEnd_194112] using wordTrace_append hprefix tailTrace_194112
  have hstable : (prefixWord ++ tailWord_194112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194112).length < 2 ^ (prefixWord ++ tailWord_194112).sum := by decide
  have hdescent : baseEnd_194112 < baseStart_194112 := by decide
  rcases family_descends (prefixWord ++ tailWord_194112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194129 : List Nat := [1, 2, 2, 1, 3, 2, 4, 1, 2, 2, 3]
def baseStart_194129 : Nat := 118140960795 + 194129 * 2 ^ 59
def prefixEnd_194129 : Nat := 4983230072969 + 3 ^ 40 * 194129 * 2
def baseEnd_194129 : Nat := 99681485976776203094723

theorem tailTrace_194129 : CollatzResearch.WordTrace tailWord_194129 prefixEnd_194129 99681485976776203094723 := by
  unfold tailWord_194129
  simp only [CollatzResearch.WordTrace]
  refine ⟨7080466313711262438737441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4720310875807508292491627 7080466313711262438737441)
  ·
    refine ⟨5310349735283446829053081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7080466313711262438737441 5310349735283446829053081)
    ·
      refine ⟨3982762301462585121789811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5310349735283446829053081 3982762301462585121789811)
      ·
        refine ⟨5974143452193877682684717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3982762301462585121789811 5974143452193877682684717)
        ·
          refine ⟨2240303794572704131006769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5974143452193877682684717 2240303794572704131006769)
          ·
            refine ⟨1680227845929528098255077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2240303794572704131006769 1680227845929528098255077)
            ·
              refine ⟨315042721111786518422827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1680227845929528098255077 315042721111786518422827)
              ·
                refine ⟨472564081667679777634241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 315042721111786518422827 472564081667679777634241)
                ·
                  refine ⟨354423061250759833225681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 472564081667679777634241 354423061250759833225681)
                  ·
                    refine ⟨265817295938069874919261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 354423061250759833225681 265817295938069874919261)
                    ·
                      refine ⟨99681485976776203094723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 265817295938069874919261 99681485976776203094723)
                      ·
                        rfl

theorem cell23_194129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 4, 1, 2, 2, 3].length) (baseStart_194129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_194129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_194129 prefixEnd_194129 := by exact prefixLift 194129
  have htrace : WordTrace (prefixWord ++ tailWord_194129) baseStart_194129 baseEnd_194129 := by
    simpa [prefixWord, tailWord_194129, baseEnd_194129] using wordTrace_append hprefix tailTrace_194129
  have hstable : (prefixWord ++ tailWord_194129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194129).length < 2 ^ (prefixWord ++ tailWord_194129).sum := by decide
  have hdescent : baseEnd_194129 < baseStart_194129 := by decide
  rcases family_descends (prefixWord ++ tailWord_194129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194149 : List Nat := [1, 3, 1, 3, 3, 2, 2, 2, 6]
def baseStart_194149 : Nat := 118140960795 + 194149 * 2 ^ 59
def prefixEnd_194149 : Nat := 4983230072969 + 3 ^ 40 * 194149 * 2
def baseEnd_194149 : Nat := 11076861732207347204959

theorem tailTrace_194149 : CollatzResearch.WordTrace tailWord_194149 prefixEnd_194149 11076861732207347204959 := by
  unfold tailWord_194149
  simp only [CollatzResearch.WordTrace]
  refine ⟨7081195773638805854465501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4720797182425870569643667 7081195773638805854465501)
  ·
    refine ⟨2655448415114552195424563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7081195773638805854465501 2655448415114552195424563)
    ·
      refine ⟨3983172622671828293136845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2655448415114552195424563 3983172622671828293136845)
      ·
        refine ⟨1493689733501935609926317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3983172622671828293136845 1493689733501935609926317)
        ·
          refine ⟨560133650063225853722369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1493689733501935609926317 560133650063225853722369)
          ·
            refine ⟨420100237547419390291777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 560133650063225853722369 420100237547419390291777)
            ·
              refine ⟨315075178160564542718833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 420100237547419390291777 315075178160564542718833)
              ·
                refine ⟨236306383620423407039125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 315075178160564542718833 236306383620423407039125)
                ·
                  refine ⟨11076861732207347204959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 236306383620423407039125 11076861732207347204959)
                  ·
                    rfl

theorem cell23_194149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 2, 2, 6].length) (baseStart_194149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_194149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_194149 prefixEnd_194149 := by exact prefixLift 194149
  have htrace : WordTrace (prefixWord ++ tailWord_194149) baseStart_194149 baseEnd_194149 := by
    simpa [prefixWord, tailWord_194149, baseEnd_194149] using wordTrace_append hprefix tailTrace_194149
  have hstable : (prefixWord ++ tailWord_194149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194149).length < 2 ^ (prefixWord ++ tailWord_194149).sum := by decide
  have hdescent : baseEnd_194149 < baseStart_194149 := by decide
  rcases family_descends (prefixWord ++ tailWord_194149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194159 : List Nat := [1, 1, 2, 1, 3, 2, 1, 5, 3, 1, 3]
def baseStart_194159 : Nat := 118140960795 + 194159 * 2 ^ 59
def prefixEnd_194159 : Nat := 4983230072969 + 3 ^ 40 * 194159 * 2
def baseEnd_194159 : Nat := 99696890396411085719585

theorem tailTrace_194159 : CollatzResearch.WordTrace tailWord_194159 prefixEnd_194159 99696890396411085719585 := by
  unfold tailWord_194159
  simp only [CollatzResearch.WordTrace]
  refine ⟨7081560503602577562329531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4721040335735051708219687 7081560503602577562329531)
  ·
    refine ⟨10622340755403866343494297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7081560503602577562329531 10622340755403866343494297)
    ·
      refine ⟨7966755566552899757620723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10622340755403866343494297 7966755566552899757620723)
      ·
        refine ⟨11950133349829349636431085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7966755566552899757620723 11950133349829349636431085)
        ·
          refine ⟨4481300006186006113661657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11950133349829349636431085 4481300006186006113661657)
          ·
            refine ⟨3360975004639504585246243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4481300006186006113661657 3360975004639504585246243)
            ·
              refine ⟨5041462506959256877869365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3360975004639504585246243 5041462506959256877869365)
              ·
                refine ⟨472637110027430332300253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5041462506959256877869365 472637110027430332300253)
                ·
                  refine ⟨177238916260286374612595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 472637110027430332300253 177238916260286374612595)
                  ·
                    refine ⟨265858374390429561918893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 177238916260286374612595 265858374390429561918893)
                    ·
                      refine ⟨99696890396411085719585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 265858374390429561918893 99696890396411085719585)
                      ·
                        rfl

theorem cell23_194159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 5, 3, 1, 3].length) (baseStart_194159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_194159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_194159 prefixEnd_194159 := by exact prefixLift 194159
  have htrace : WordTrace (prefixWord ++ tailWord_194159) baseStart_194159 baseEnd_194159 := by
    simpa [prefixWord, tailWord_194159, baseEnd_194159] using wordTrace_append hprefix tailTrace_194159
  have hstable : (prefixWord ++ tailWord_194159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194159).length < 2 ^ (prefixWord ++ tailWord_194159).sum := by decide
  have hdescent : baseEnd_194159 < baseStart_194159 := by decide
  rcases family_descends (prefixWord ++ tailWord_194159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194169 : List Nat := [1, 2, 1, 3, 3, 1, 2, 2, 1, 5, 2]
def baseStart_194169 : Nat := 118140960795 + 194169 * 2 ^ 59
def prefixEnd_194169 : Nat := 4983230072969 + 3 ^ 40 * 194169 * 2
def baseEnd_194169 : Nat := 99702025202956046594539

theorem tailTrace_194169 : CollatzResearch.WordTrace tailWord_194169 prefixEnd_194169 99702025202956046594539 := by
  unfold tailWord_194169
  simp only [CollatzResearch.WordTrace]
  refine ⟨7081925233566349270193561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4721283489044232846795707 7081925233566349270193561)
  ·
    refine ⟨5311443925174761952645171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7081925233566349270193561 5311443925174761952645171)
    ·
      refine ⟨7967165887762142928967757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5311443925174761952645171 7967165887762142928967757)
      ·
        refine ⟨2987687207910803598362909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7967165887762142928967757 2987687207910803598362909)
        ·
          refine ⟨1120382702966551349386091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2987687207910803598362909 1120382702966551349386091)
          ·
            refine ⟨1680574054449827024079137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1120382702966551349386091 1680574054449827024079137)
            ·
              refine ⟨1260430540837370268059353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1680574054449827024079137 1260430540837370268059353)
              ·
                refine ⟨945322905628027701044515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1260430540837370268059353 945322905628027701044515)
                ·
                  refine ⟨1417984358442041551566773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 945322905628027701044515 1417984358442041551566773)
                  ·
                    refine ⟨132936033603941395459385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1417984358442041551566773 132936033603941395459385)
                    ·
                      refine ⟨99702025202956046594539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 132936033603941395459385 99702025202956046594539)
                      ·
                        rfl

theorem cell23_194169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 2, 1, 5, 2].length) (baseStart_194169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_194169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_194169 prefixEnd_194169 := by exact prefixLift 194169
  have htrace : WordTrace (prefixWord ++ tailWord_194169) baseStart_194169 baseEnd_194169 := by
    simpa [prefixWord, tailWord_194169, baseEnd_194169] using wordTrace_append hprefix tailTrace_194169
  have hstable : (prefixWord ++ tailWord_194169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194169).length < 2 ^ (prefixWord ++ tailWord_194169).sum := by decide
  have hdescent : baseEnd_194169 < baseStart_194169 := by decide
  rcases family_descends (prefixWord ++ tailWord_194169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194186 : List Nat := [3, 1, 2, 3, 2, 2, 1, 1, 1, 5, 2]
def baseStart_194186 : Nat := 118140960795 + 194186 * 2 ^ 59
def prefixEnd_194186 : Nat := 4983230072969 + 3 ^ 40 * 194186 * 2
def baseEnd_194186 : Nat := 99710754374082480081961

theorem tailTrace_194186 : CollatzResearch.WordTrace tailWord_194186 prefixEnd_194186 99710754374082480081961 := by
  unfold tailWord_194186
  simp only [CollatzResearch.WordTrace]
  refine ⟨1770636318626190293390603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4721696849669840782374941 1770636318626190293390603)
  ·
    refine ⟨2655954477939285440085905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1770636318626190293390603 2655954477939285440085905)
    ·
      refine ⟨1991965858454464080064429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2655954477939285440085905 1991965858454464080064429)
      ·
        refine ⟨746987196920424030024161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1991965858454464080064429 746987196920424030024161)
        ·
          refine ⟨560240397690318022518121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 746987196920424030024161 560240397690318022518121)
          ·
            refine ⟨420180298267738516888591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 560240397690318022518121 420180298267738516888591)
            ·
              refine ⟨630270447401607775332887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 420180298267738516888591 630270447401607775332887)
              ·
                refine ⟨945405671102411662999331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 630270447401607775332887 945405671102411662999331)
                ·
                  refine ⟨1418108506653617494498997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 945405671102411662999331 1418108506653617494498997)
                  ·
                    refine ⟨132947672498776640109281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1418108506653617494498997 132947672498776640109281)
                    ·
                      refine ⟨99710754374082480081961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 132947672498776640109281 99710754374082480081961)
                      ·
                        rfl

theorem cell23_194186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 1, 1, 5, 2].length) (baseStart_194186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_194186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_194186 prefixEnd_194186 := by exact prefixLift 194186
  have htrace : WordTrace (prefixWord ++ tailWord_194186) baseStart_194186 baseEnd_194186 := by
    simpa [prefixWord, tailWord_194186, baseEnd_194186] using wordTrace_append hprefix tailTrace_194186
  have hstable : (prefixWord ++ tailWord_194186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194186).length < 2 ^ (prefixWord ++ tailWord_194186).sum := by decide
  have hdescent : baseEnd_194186 < baseStart_194186 := by decide
  rcases family_descends (prefixWord ++ tailWord_194186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194210 : List Nat := [3, 3, 1, 4, 1, 1, 2, 1, 3, 1, 3]
def baseStart_194210 : Nat := 118140960795 + 194210 * 2 ^ 59
def prefixEnd_194210 : Nat := 4983230072969 + 3 ^ 40 * 194210 * 2
def baseEnd_194210 : Nat := 99723077909790386181851

theorem tailTrace_194210 : CollatzResearch.WordTrace tailWord_194210 prefixEnd_194210 99723077909790386181851 := by
  unfold tailWord_194210
  simp only [CollatzResearch.WordTrace]
  refine ⟨1770855156604453318109021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4722280417611875514957389 1770855156604453318109021)
  ·
    refine ⟨664070683726669994290883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1770855156604453318109021 664070683726669994290883)
    ·
      refine ⟨996106025590004991436325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 664070683726669994290883 996106025590004991436325)
      ·
        refine ⟨186769879798125935894311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 996106025590004991436325 186769879798125935894311)
        ·
          refine ⟨280154819697188903841467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 186769879798125935894311 280154819697188903841467)
          ·
            refine ⟨420232229545783355762201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 280154819697188903841467 420232229545783355762201)
            ·
              refine ⟨315174172159337516821651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 420232229545783355762201 315174172159337516821651)
              ·
                refine ⟨472761258239006275232477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 315174172159337516821651 472761258239006275232477)
                ·
                  refine ⟨177285471839627353212179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 472761258239006275232477 177285471839627353212179)
                  ·
                    refine ⟨265928207759441029818269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 177285471839627353212179 265928207759441029818269)
                    ·
                      refine ⟨99723077909790386181851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 265928207759441029818269 99723077909790386181851)
                      ·
                        rfl

theorem cell23_194210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_194210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_194210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_194210 prefixEnd_194210 := by exact prefixLift 194210
  have htrace : WordTrace (prefixWord ++ tailWord_194210) baseStart_194210 baseEnd_194210 := by
    simpa [prefixWord, tailWord_194210, baseEnd_194210] using wordTrace_append hprefix tailTrace_194210
  have hstable : (prefixWord ++ tailWord_194210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194210).length < 2 ^ (prefixWord ++ tailWord_194210).sum := by decide
  have hdescent : baseEnd_194210 < baseStart_194210 := by decide
  rcases family_descends (prefixWord ++ tailWord_194210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194236 : List Nat := [2, 2, 2, 3, 1, 2, 1, 4, 1, 2, 3]
def baseStart_194236 : Nat := 118140960795 + 194236 * 2 ^ 59
def prefixEnd_194236 : Nat := 4983230072969 + 3 ^ 40 * 194236 * 2
def baseEnd_194236 : Nat := 99736428406807284456731

theorem tailTrace_194236 : CollatzResearch.WordTrace tailWord_194236 prefixEnd_194236 99736428406807284456731 := by
  unfold tailWord_194236
  simp only [CollatzResearch.WordTrace]
  refine ⟨3542184462161809856441281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4722912616215746475255041 3542184462161809856441281)
  ·
    refine ⟨2656638346621357392330961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3542184462161809856441281 2656638346621357392330961)
    ·
      refine ⟨1992478759966018044248221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2656638346621357392330961 1992478759966018044248221)
      ·
        refine ⟨747179534987256766593083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1992478759966018044248221 747179534987256766593083)
        ·
          refine ⟨1120769302480885149889625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 747179534987256766593083 1120769302480885149889625)
          ·
            refine ⟨840576976860663862417219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1120769302480885149889625 840576976860663862417219)
            ·
              refine ⟨1260865465290995793625829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 840576976860663862417219 1260865465290995793625829)
              ·
                refine ⟨236412274742061711304843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1260865465290995793625829 236412274742061711304843)
                ·
                  refine ⟨354618412113092566957265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 236412274742061711304843 354618412113092566957265)
                  ·
                    refine ⟨265963809084819425217949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 354618412113092566957265 265963809084819425217949)
                    ·
                      refine ⟨99736428406807284456731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 265963809084819425217949 99736428406807284456731)
                      ·
                        rfl

theorem cell23_194236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 4, 1, 2, 3].length) (baseStart_194236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_194236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_194236 prefixEnd_194236 := by exact prefixLift 194236
  have htrace : WordTrace (prefixWord ++ tailWord_194236) baseStart_194236 baseEnd_194236 := by
    simpa [prefixWord, tailWord_194236, baseEnd_194236] using wordTrace_append hprefix tailTrace_194236
  have hstable : (prefixWord ++ tailWord_194236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194236).length < 2 ^ (prefixWord ++ tailWord_194236).sum := by decide
  have hdescent : baseEnd_194236 < baseStart_194236 := by decide
  rcases family_descends (prefixWord ++ tailWord_194236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194253 : List Nat := [1, 6, 2, 1, 1, 2, 2, 1, 1, 1, 5]
def baseStart_194253 : Nat := 118140960795 + 194253 * 2 ^ 59
def prefixEnd_194253 : Nat := 4983230072969 + 3 ^ 40 * 194253 * 2
def baseEnd_194253 : Nat := 99745157577933717944153

theorem tailTrace_194253 : CollatzResearch.WordTrace tailWord_194253 prefixEnd_194253 99745157577933717944153 := by
  unfold tailWord_194253
  simp only [CollatzResearch.WordTrace]
  refine ⟨7084988965262031616251413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4723325976841354410834275 7084988965262031616251413)
  ·
    refine ⟨332108857746657732011785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 7084988965262031616251413 332108857746657732011785)
    ·
      refine ⟨249081643309993299008839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 332108857746657732011785 249081643309993299008839)
      ·
        refine ⟨373622464964989948513259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249081643309993299008839 373622464964989948513259)
        ·
          refine ⟨560433697447484922769889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 373622464964989948513259 560433697447484922769889)
          ·
            refine ⟨420325273085613692077417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 560433697447484922769889 420325273085613692077417)
            ·
              refine ⟨315243954814210269058063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 420325273085613692077417 315243954814210269058063)
              ·
                refine ⟨472865932221315403587095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 315243954814210269058063 472865932221315403587095)
                ·
                  refine ⟨709298898331973105380643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 472865932221315403587095 709298898331973105380643)
                  ·
                    refine ⟨1063948347497959658070965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 709298898331973105380643 1063948347497959658070965)
                    ·
                      refine ⟨99745157577933717944153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1063948347497959658070965 99745157577933717944153)
                      ·
                        rfl

theorem cell23_194253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_194253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_194253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_194253 prefixEnd_194253 := by exact prefixLift 194253
  have htrace : WordTrace (prefixWord ++ tailWord_194253) baseStart_194253 baseEnd_194253 := by
    simpa [prefixWord, tailWord_194253, baseEnd_194253] using wordTrace_append hprefix tailTrace_194253
  have hstable : (prefixWord ++ tailWord_194253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194253).length < 2 ^ (prefixWord ++ tailWord_194253).sum := by decide
  have hdescent : baseEnd_194253 < baseStart_194253 := by decide
  rcases family_descends (prefixWord ++ tailWord_194253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194266 : List Nat := [3, 1, 1, 2, 2, 3, 2, 1, 4, 1, 3]
def baseStart_194266 : Nat := 118140960795 + 194266 * 2 ^ 59
def prefixEnd_194266 : Nat := 4983230072969 + 3 ^ 40 * 194266 * 2
def baseEnd_194266 : Nat := 99751832826442167081593

theorem tailTrace_194266 : CollatzResearch.WordTrace tailWord_194266 prefixEnd_194266 99751832826442167081593 := by
  unfold tailWord_194266
  simp only [CollatzResearch.WordTrace]
  refine ⟨1771365778553733709118663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4723642076143289890983101 1771365778553733709118663)
  ·
    refine ⟨2657048667830600563677995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1771365778553733709118663 2657048667830600563677995)
    ·
      refine ⟨3985573001745900845516993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2657048667830600563677995 3985573001745900845516993)
      ·
        refine ⟨2989179751309425634137745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3985573001745900845516993 2989179751309425634137745)
        ·
          refine ⟨2241884813482069225603309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2989179751309425634137745 2241884813482069225603309)
          ·
            refine ⟨840706805055775959601241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2241884813482069225603309 840706805055775959601241)
            ·
              refine ⟨630530103791831969700931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 840706805055775959601241 630530103791831969700931)
              ·
                refine ⟨945795155687747954551397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 630530103791831969700931 945795155687747954551397)
                ·
                  refine ⟨177336591691452741478387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 945795155687747954551397 177336591691452741478387)
                  ·
                    refine ⟨266004887537179112217581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 177336591691452741478387 266004887537179112217581)
                    ·
                      refine ⟨99751832826442167081593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 266004887537179112217581 99751832826442167081593)
                      ·
                        rfl

theorem cell23_194266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 1, 4, 1, 3].length) (baseStart_194266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_194266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_194266 prefixEnd_194266 := by exact prefixLift 194266
  have htrace : WordTrace (prefixWord ++ tailWord_194266) baseStart_194266 baseEnd_194266 := by
    simpa [prefixWord, tailWord_194266, baseEnd_194266] using wordTrace_append hprefix tailTrace_194266
  have hstable : (prefixWord ++ tailWord_194266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194266).length < 2 ^ (prefixWord ++ tailWord_194266).sum := by decide
  have hdescent : baseEnd_194266 < baseStart_194266 := by decide
  rcases family_descends (prefixWord ++ tailWord_194266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194276 : List Nat := [2, 3, 1, 1, 1, 3, 2, 2, 3, 3, 2]
def baseStart_194276 : Nat := 118140960795 + 194276 * 2 ^ 59
def prefixEnd_194276 : Nat := 4983230072969 + 3 ^ 40 * 194276 * 2
def baseEnd_194276 : Nat := 99756967632987127956547

theorem tailTrace_194276 : CollatzResearch.WordTrace tailWord_194276 prefixEnd_194276 99756967632987127956547 := by
  unfold tailWord_194276
  simp only [CollatzResearch.WordTrace]
  refine ⟨3542913922089353272169341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4723885229452471029559121 3542913922089353272169341)
  ·
    refine ⟨1328592720783507477063503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3542913922089353272169341 1328592720783507477063503)
    ·
      refine ⟨1992889081175261215595255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1328592720783507477063503 1992889081175261215595255)
      ·
        refine ⟨2989333621762891823392883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1992889081175261215595255 2989333621762891823392883)
        ·
          refine ⟨4484000432644337735089325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2989333621762891823392883 4484000432644337735089325)
          ·
            refine ⟨1681500162241626650658497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4484000432644337735089325 1681500162241626650658497)
            ·
              refine ⟨1261125121681219987993873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1681500162241626650658497 1261125121681219987993873)
              ·
                refine ⟨945843841260914990995405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1261125121681219987993873 945843841260914990995405)
                ·
                  refine ⟨354691440472843121623277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 945843841260914990995405 354691440472843121623277)
                  ·
                    refine ⟨133009290177316170608729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 354691440472843121623277 133009290177316170608729)
                    ·
                      refine ⟨99756967632987127956547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 133009290177316170608729 99756967632987127956547)
                      ·
                        rfl

theorem cell23_194276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 2, 3, 3, 2].length) (baseStart_194276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_194276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_194276 prefixEnd_194276 := by exact prefixLift 194276
  have htrace : WordTrace (prefixWord ++ tailWord_194276) baseStart_194276 baseEnd_194276 := by
    simpa [prefixWord, tailWord_194276, baseEnd_194276] using wordTrace_append hprefix tailTrace_194276
  have hstable : (prefixWord ++ tailWord_194276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194276).length < 2 ^ (prefixWord ++ tailWord_194276).sum := by decide
  have hdescent : baseEnd_194276 < baseStart_194276 := by decide
  rcases family_descends (prefixWord ++ tailWord_194276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194283 : List Nat := [1, 1, 1, 1, 2, 4, 6, 1, 2, 1, 3]
def baseStart_194283 : Nat := 118140960795 + 194283 * 2 ^ 59
def prefixEnd_194283 : Nat := 4983230072969 + 3 ^ 40 * 194283 * 2
def baseEnd_194283 : Nat := 99760561997568600569015

theorem tailTrace_194283 : CollatzResearch.WordTrace tailWord_194283 prefixEnd_194283 99760561997568600569015 := by
  unfold tailWord_194283
  simp only [CollatzResearch.WordTrace]
  refine ⟨7086083155153346739843503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4724055436768897826562335 7086083155153346739843503)
  ·
    refine ⟨10629124732730020109765255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7086083155153346739843503 10629124732730020109765255)
    ·
      refine ⟨15943687099095030164647883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10629124732730020109765255 15943687099095030164647883)
      ·
        refine ⟨23915530648642545246971825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15943687099095030164647883 23915530648642545246971825)
        ·
          refine ⟨17936647986481908935228869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23915530648642545246971825 17936647986481908935228869)
          ·
            refine ⟨3363121497465357925355413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17936647986481908935228869 3363121497465357925355413)
            ·
              refine ⟨157646320193688652751035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 3363121497465357925355413 157646320193688652751035)
              ·
                refine ⟨236469480290532979126553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 157646320193688652751035 236469480290532979126553)
                ·
                  refine ⟨177352110217899734344915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 236469480290532979126553 177352110217899734344915)
                  ·
                    refine ⟨266028165326849601517373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 177352110217899734344915 266028165326849601517373)
                    ·
                      refine ⟨99760561997568600569015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 266028165326849601517373 99760561997568600569015)
                      ·
                        rfl

theorem cell23_194283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 6, 1, 2, 1, 3].length) (baseStart_194283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_194283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_194283 prefixEnd_194283 := by exact prefixLift 194283
  have htrace : WordTrace (prefixWord ++ tailWord_194283) baseStart_194283 baseEnd_194283 := by
    simpa [prefixWord, tailWord_194283, baseEnd_194283] using wordTrace_append hprefix tailTrace_194283
  have hstable : (prefixWord ++ tailWord_194283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194283).length < 2 ^ (prefixWord ++ tailWord_194283).sum := by decide
  have hdescent : baseEnd_194283 < baseStart_194283 := by decide
  rcases family_descends (prefixWord ++ tailWord_194283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194339 : List Nat := [1, 1, 1, 4, 2, 1, 3, 1, 1, 5, 3]
def baseStart_194339 : Nat := 118140960795 + 194339 * 2 ^ 59
def prefixEnd_194339 : Nat := 4983230072969 + 3 ^ 40 * 194339 * 2
def baseEnd_194339 : Nat := 99789316914220381468757

theorem tailTrace_194339 : CollatzResearch.WordTrace tailWord_194339 prefixEnd_194339 99789316914220381468757 := by
  unfold tailWord_194339
  simp only [CollatzResearch.WordTrace]
  refine ⟨7088125642950468303882071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4725417095300312202588047 7088125642950468303882071)
  ·
    refine ⟨10632188464425702455823107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7088125642950468303882071 10632188464425702455823107)
    ·
      refine ⟨15948282696638553683734661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10632188464425702455823107 15948282696638553683734661)
      ·
        refine ⟨2990303005619728815700249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15948282696638553683734661 2990303005619728815700249)
        ·
          refine ⟨2242727254214796611775187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2990303005619728815700249 2242727254214796611775187)
          ·
            refine ⟨3364090881322194917662781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2242727254214796611775187 3364090881322194917662781)
            ·
              refine ⟨1261534080495823094123543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3364090881322194917662781 1261534080495823094123543)
              ·
                refine ⟨1892301120743734641185315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1261534080495823094123543 1892301120743734641185315)
                ·
                  refine ⟨2838451681115601961777973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1892301120743734641185315 2838451681115601961777973)
                  ·
                    refine ⟨266104845104587683916685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2838451681115601961777973 266104845104587683916685)
                    ·
                      refine ⟨99789316914220381468757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 266104845104587683916685 99789316914220381468757)
                      ·
                        rfl

theorem cell23_194339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 1, 1, 5, 3].length) (baseStart_194339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_194339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_194339 prefixEnd_194339 := by exact prefixLift 194339
  have htrace : WordTrace (prefixWord ++ tailWord_194339) baseStart_194339 baseEnd_194339 := by
    simpa [prefixWord, tailWord_194339, baseEnd_194339] using wordTrace_append hprefix tailTrace_194339
  have hstable : (prefixWord ++ tailWord_194339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194339).length < 2 ^ (prefixWord ++ tailWord_194339).sum := by decide
  have hdescent : baseEnd_194339 < baseStart_194339 := by decide
  rcases family_descends (prefixWord ++ tailWord_194339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194340 : List Nat := [2, 3, 1, 3, 2, 1, 2, 3, 2, 2, 2]
def baseStart_194340 : Nat := 118140960795 + 194340 * 2 ^ 59
def prefixEnd_194340 : Nat := 4983230072969 + 3 ^ 40 * 194340 * 2
def baseEnd_194340 : Nat := 99789830394874877556253

theorem tailTrace_194340 : CollatzResearch.WordTrace tailWord_194340 prefixEnd_194340 99789830394874877556253 := by
  unfold tailWord_194340
  simp only [CollatzResearch.WordTrace]
  refine ⟨3544081057973422737334237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4725441410631230316445649 3544081057973422737334237)
  ·
    refine ⟨1329030396740033526500339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3544081057973422737334237 1329030396740033526500339)
    ·
      refine ⟨1993545595110050289750509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1329030396740033526500339 1993545595110050289750509)
      ·
        refine ⟨747579598166268858656441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1993545595110050289750509 747579598166268858656441)
        ·
          refine ⟨560684698624701643992331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 747579598166268858656441 560684698624701643992331)
          ·
            refine ⟨841027047937052465988497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 560684698624701643992331 841027047937052465988497)
            ·
              refine ⟨630770285952789349491373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 841027047937052465988497 630770285952789349491373)
              ·
                refine ⟨236538857232296006059265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 630770285952789349491373 236538857232296006059265)
                ·
                  refine ⟨177404142924222004544449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 236538857232296006059265 177404142924222004544449)
                  ·
                    refine ⟨133053107193166503408337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 177404142924222004544449 133053107193166503408337)
                    ·
                      refine ⟨99789830394874877556253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 133053107193166503408337 99789830394874877556253)
                      ·
                        rfl

theorem cell23_194340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 3, 2, 2, 2].length) (baseStart_194340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_194340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_194340 prefixEnd_194340 := by exact prefixLift 194340
  have htrace : WordTrace (prefixWord ++ tailWord_194340) baseStart_194340 baseEnd_194340 := by
    simpa [prefixWord, tailWord_194340, baseEnd_194340] using wordTrace_append hprefix tailTrace_194340
  have hstable : (prefixWord ++ tailWord_194340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194340).length < 2 ^ (prefixWord ++ tailWord_194340).sum := by decide
  have hdescent : baseEnd_194340 < baseStart_194340 := by decide
  rcases family_descends (prefixWord ++ tailWord_194340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194359 : List Nat := [1, 1, 3, 1, 2, 1, 2, 5, 2, 5]
def baseStart_194359 : Nat := 118140960795 + 194359 * 2 ^ 59
def prefixEnd_194359 : Nat := 4983230072969 + 3 ^ 40 * 194359 * 2
def baseEnd_194359 : Nat := 33266528842436767739555

theorem tailTrace_194359 : CollatzResearch.WordTrace tailWord_194359 prefixEnd_194359 33266528842436767739555 := by
  unfold tailWord_194359
  simp only [CollatzResearch.WordTrace]
  refine ⟨7088855102878011719610131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4725903401918674479740087 7088855102878011719610131)
  ·
    refine ⟨10633282654317017579415197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7088855102878011719610131 10633282654317017579415197)
    ·
      refine ⟨3987480995368881592280699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10633282654317017579415197 3987480995368881592280699)
      ·
        refine ⟨5981221493053322388421049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3987480995368881592280699 5981221493053322388421049)
        ·
          refine ⟨4485916119789991791315787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5981221493053322388421049 4485916119789991791315787)
          ·
            refine ⟨6728874179684987686973681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4485916119789991791315787 6728874179684987686973681)
            ·
              refine ⟨5046655634763740765230261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6728874179684987686973681 5046655634763740765230261)
              ·
                refine ⟨473123965759100696740337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5046655634763740765230261 473123965759100696740337)
                ·
                  refine ⟨354842974319325522555253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 473123965759100696740337 354842974319325522555253)
                  ·
                    refine ⟨33266528842436767739555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 354842974319325522555253 33266528842436767739555)
                    ·
                      rfl

theorem cell23_194359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 5, 2, 5].length) (baseStart_194359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_194359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_194359 prefixEnd_194359 := by exact prefixLift 194359
  have htrace : WordTrace (prefixWord ++ tailWord_194359) baseStart_194359 baseEnd_194359 := by
    simpa [prefixWord, tailWord_194359, baseEnd_194359] using wordTrace_append hprefix tailTrace_194359
  have hstable : (prefixWord ++ tailWord_194359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194359).length < 2 ^ (prefixWord ++ tailWord_194359).sum := by decide
  have hdescent : baseEnd_194359 < baseStart_194359 := by decide
  rcases family_descends (prefixWord ++ tailWord_194359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194374 : List Nat := [6, 1, 1, 2, 1, 1, 3, 2, 2, 2, 2]
def baseStart_194374 : Nat := 118140960795 + 194374 * 2 ^ 59
def prefixEnd_194374 : Nat := 4983230072969 + 3 ^ 40 * 194374 * 2
def baseEnd_194374 : Nat := 99807288737127744531097

theorem tailTrace_194374 : CollatzResearch.WordTrace tailWord_194374 prefixEnd_194374 99807288737127744531097 := by
  unfold tailWord_194374
  simp only [CollatzResearch.WordTrace]
  refine ⟨221543818681989665043943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 4726268131882446187604117 221543818681989665043943)
  ·
    refine ⟨332315728022984497565915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221543818681989665043943 332315728022984497565915)
    ·
      refine ⟨498473592034476746348873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 332315728022984497565915 498473592034476746348873)
      ·
        refine ⟨373855194025857559761655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 498473592034476746348873 373855194025857559761655)
        ·
          refine ⟨560782791038786339642483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 373855194025857559761655 560782791038786339642483)
          ·
            refine ⟨841174186558179509463725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 560782791038786339642483 841174186558179509463725)
            ·
              refine ⟨315440319959317316048897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 841174186558179509463725 315440319959317316048897)
              ·
                refine ⟨236580239969487987036673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 315440319959317316048897 236580239969487987036673)
                ·
                  refine ⟨177435179977115990277505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 236580239969487987036673 177435179977115990277505)
                  ·
                    refine ⟨133076384982836992708129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 177435179977115990277505 133076384982836992708129)
                    ·
                      refine ⟨99807288737127744531097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 133076384982836992708129 99807288737127744531097)
                      ·
                        rfl

theorem cell23_194374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 3, 2, 2, 2, 2].length) (baseStart_194374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_194374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_194374 prefixEnd_194374 := by exact prefixLift 194374
  have htrace : WordTrace (prefixWord ++ tailWord_194374) baseStart_194374 baseEnd_194374 := by
    simpa [prefixWord, tailWord_194374, baseEnd_194374] using wordTrace_append hprefix tailTrace_194374
  have hstable : (prefixWord ++ tailWord_194374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194374).length < 2 ^ (prefixWord ++ tailWord_194374).sum := by decide
  have hdescent : baseEnd_194374 < baseStart_194374 := by decide
  rcases family_descends (prefixWord ++ tailWord_194374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194416 : List Nat := [2, 1, 1, 1, 4, 1, 1, 5, 2, 2, 3]
def baseStart_194416 : Nat := 118140960795 + 194416 * 2 ^ 59
def prefixEnd_194416 : Nat := 4983230072969 + 3 ^ 40 * 194416 * 2
def baseEnd_194416 : Nat := 99828854924616580205903

theorem tailTrace_194416 : CollatzResearch.WordTrace tailWord_194416 prefixEnd_194416 99828854924616580205903 := by
  unfold tailWord_194416
  simp only [CollatzResearch.WordTrace]
  refine ⟨3545467031835755227217551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4727289375781006969623401 3545467031835755227217551)
  ·
    refine ⟨5318200547753632840826327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3545467031835755227217551 5318200547753632840826327)
    ·
      refine ⟨7977300821630449261239491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5318200547753632840826327 7977300821630449261239491)
      ·
        refine ⟨11965951232445673891859237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7977300821630449261239491 11965951232445673891859237)
        ·
          refine ⟨2243615856083563854723607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11965951232445673891859237 2243615856083563854723607)
          ·
            refine ⟨3365423784125345782085411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2243615856083563854723607 3365423784125345782085411)
            ·
              refine ⟨5048135676188018673128117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3365423784125345782085411 5048135676188018673128117)
              ·
                refine ⟨473262719642626750605761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5048135676188018673128117 473262719642626750605761)
                ·
                  refine ⟨354947039731970062954321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 473262719642626750605761 354947039731970062954321)
                  ·
                    refine ⟨266210279798977547215741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 354947039731970062954321 266210279798977547215741)
                    ·
                      refine ⟨99828854924616580205903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 266210279798977547215741 99828854924616580205903)
                      ·
                        rfl

theorem cell23_194416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 5, 2, 2, 3].length) (baseStart_194416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_194416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_194416 prefixEnd_194416 := by exact prefixLift 194416
  have htrace : WordTrace (prefixWord ++ tailWord_194416) baseStart_194416 baseEnd_194416 := by
    simpa [prefixWord, tailWord_194416, baseEnd_194416] using wordTrace_append hprefix tailTrace_194416
  have hstable : (prefixWord ++ tailWord_194416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194416).length < 2 ^ (prefixWord ++ tailWord_194416).sum := by decide
  have hdescent : baseEnd_194416 < baseStart_194416 := by decide
  rcases family_descends (prefixWord ++ tailWord_194416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194430 : List Nat := [4, 2, 3, 1, 1, 2, 1, 2, 2, 1, 4]
def baseStart_194430 : Nat := 118140960795 + 194430 * 2 ^ 59
def prefixEnd_194430 : Nat := 4983230072969 + 3 ^ 40 * 194430 * 2
def baseEnd_194430 : Nat := 99836043653779525430839

theorem tailTrace_194430 : CollatzResearch.WordTrace tailWord_194430 prefixEnd_194430 99836043653779525430839 := by
  unfold tailWord_194430
  simp only [CollatzResearch.WordTrace]
  refine ⟨886430585702598855680593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4727629790413860563629829 886430585702598855680593)
  ·
    refine ⟨664822939276949141760445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 886430585702598855680593 664822939276949141760445)
    ·
      refine ⟨249308602228855928160167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 664822939276949141760445 249308602228855928160167)
      ·
        refine ⟨373962903343283892240251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249308602228855928160167 373962903343283892240251)
        ·
          refine ⟨560944355014925838360377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 373962903343283892240251 560944355014925838360377)
          ·
            refine ⟨420708266261194378770283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 560944355014925838360377 420708266261194378770283)
            ·
              refine ⟨631062399391791568155425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 420708266261194378770283 631062399391791568155425)
              ·
                refine ⟨473296799543843676116569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 631062399391791568155425 473296799543843676116569)
                ·
                  refine ⟨354972599657882757087427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 473296799543843676116569 354972599657882757087427)
                  ·
                    refine ⟨532458899486824135631141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 354972599657882757087427 532458899486824135631141)
                    ·
                      refine ⟨99836043653779525430839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 532458899486824135631141 99836043653779525430839)
                      ·
                        rfl

theorem cell23_194430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_194430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_194430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_194430 prefixEnd_194430 := by exact prefixLift 194430
  have htrace : WordTrace (prefixWord ++ tailWord_194430) baseStart_194430 baseEnd_194430 := by
    simpa [prefixWord, tailWord_194430, baseEnd_194430] using wordTrace_append hprefix tailTrace_194430
  have hstable : (prefixWord ++ tailWord_194430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194430).length < 2 ^ (prefixWord ++ tailWord_194430).sum := by decide
  have hdescent : baseEnd_194430 < baseStart_194430 := by decide
  rcases family_descends (prefixWord ++ tailWord_194430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194440 : List Nat := [2, 1, 3, 3, 3, 2, 1, 1, 3, 4]
def baseStart_194440 : Nat := 118140960795 + 194440 * 2 ^ 59
def prefixEnd_194440 : Nat := 4983230072969 + 3 ^ 40 * 194440 * 2
def baseEnd_194440 : Nat := 33280392820108162101931

theorem tailTrace_194440 : CollatzResearch.WordTrace tailWord_194440 prefixEnd_194440 33280392820108162101931 := by
  unfold tailWord_194440
  simp only [CollatzResearch.WordTrace]
  refine ⟨3545904707792281276654387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4727872943723041702205849 3545904707792281276654387)
  ·
    refine ⟨5318857061688421914981581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3545904707792281276654387 5318857061688421914981581)
    ·
      refine ⟨1994571398133158218118093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5318857061688421914981581 1994571398133158218118093)
      ·
        refine ⟨747964274299934331794285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1994571398133158218118093 747964274299934331794285)
        ·
          refine ⟨280486602862475374422857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 747964274299934331794285 280486602862475374422857)
          ·
            refine ⟨210364952146856530817143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 280486602862475374422857 210364952146856530817143)
            ·
              refine ⟨315547428220284796225715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 210364952146856530817143 315547428220284796225715)
              ·
                refine ⟨473321142330427194338573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 315547428220284796225715 473321142330427194338573)
                ·
                  refine ⟨177495428373910197876965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 473321142330427194338573 177495428373910197876965)
                  ·
                    refine ⟨33280392820108162101931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 177495428373910197876965 33280392820108162101931)
                    ·
                      rfl

theorem cell23_194440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 1, 1, 3, 4].length) (baseStart_194440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_194440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_194440 prefixEnd_194440 := by exact prefixLift 194440
  have htrace : WordTrace (prefixWord ++ tailWord_194440) baseStart_194440 baseEnd_194440 := by
    simpa [prefixWord, tailWord_194440, baseEnd_194440] using wordTrace_append hprefix tailTrace_194440
  have hstable : (prefixWord ++ tailWord_194440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194440).length < 2 ^ (prefixWord ++ tailWord_194440).sum := by decide
  have hdescent : baseEnd_194440 < baseStart_194440 := by decide
  rcases family_descends (prefixWord ++ tailWord_194440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194483 : List Nat := [1, 1, 1, 2, 3, 1, 7, 1, 1, 5]
def baseStart_194483 : Nat := 118140960795 + 194483 * 2 ^ 59
def prefixEnd_194483 : Nat := 4983230072969 + 3 ^ 40 * 194483 * 2
def baseEnd_194483 : Nat := 33287752709489272689365

theorem tailTrace_194483 : CollatzResearch.WordTrace tailWord_194483 prefixEnd_194483 33287752709489272689365 := by
  unfold tailWord_194483
  simp only [CollatzResearch.WordTrace]
  refine ⟨7093377754428780897124103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4728918502952520598082735 7093377754428780897124103)
  ·
    refine ⟨10640066631643171345686155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7093377754428780897124103 10640066631643171345686155)
    ·
      refine ⟨15960099947464757018529233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10640066631643171345686155 15960099947464757018529233)
      ·
        refine ⟨11970074960598567763896925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15960099947464757018529233 11970074960598567763896925)
        ·
          refine ⟨4488778110224462911461347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11970074960598567763896925 4488778110224462911461347)
          ·
            refine ⟨6733167165336694367192021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4488778110224462911461347 6733167165336694367192021)
            ·
              refine ⟨157808605437578774231063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 6733167165336694367192021 157808605437578774231063)
              ·
                refine ⟨236712908156368161346595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 157808605437578774231063 236712908156368161346595)
                ·
                  refine ⟨355069362234552242019893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 236712908156368161346595 355069362234552242019893)
                  ·
                    refine ⟨33287752709489272689365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 355069362234552242019893 33287752709489272689365)
                    ·
                      rfl

theorem cell23_194483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 7, 1, 1, 5].length) (baseStart_194483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_194483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_194483 prefixEnd_194483 := by exact prefixLift 194483
  have htrace : WordTrace (prefixWord ++ tailWord_194483) baseStart_194483 baseEnd_194483 := by
    simpa [prefixWord, tailWord_194483, baseEnd_194483] using wordTrace_append hprefix tailTrace_194483
  have hstable : (prefixWord ++ tailWord_194483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194483).length < 2 ^ (prefixWord ++ tailWord_194483).sum := by decide
  have hdescent : baseEnd_194483 < baseStart_194483 := by decide
  rcases family_descends (prefixWord ++ tailWord_194483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194506 : List Nat := [3, 1, 2, 1, 2, 1, 2, 4, 1, 1, 5]
def baseStart_194506 : Nat := 118140960795 + 194506 * 2 ^ 59
def prefixEnd_194506 : Nat := 4983230072969 + 3 ^ 40 * 194506 * 2
def baseEnd_194506 : Nat := 99875068183521228080489

theorem tailTrace_194506 : CollatzResearch.WordTrace tailWord_194506 prefixEnd_194506 99875068183521228080489 := by
  unfold tailWord_194506
  simp only [CollatzResearch.WordTrace]
  refine ⟨1773554158336363956302843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4729477755563637216807581 1773554158336363956302843)
  ·
    refine ⟨2660331237504545934454265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1773554158336363956302843 2660331237504545934454265)
    ·
      refine ⟨1995248428128409450840699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2660331237504545934454265 1995248428128409450840699)
      ·
        refine ⟨2992872642192614176261049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1995248428128409450840699 2992872642192614176261049)
        ·
          refine ⟨2244654481644460632195787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2992872642192614176261049 2244654481644460632195787)
          ·
            refine ⟨3366981722466690948293681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2244654481644460632195787 3366981722466690948293681)
            ·
              refine ⟨2525236291850018211220261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3366981722466690948293681 2525236291850018211220261)
              ·
                refine ⟨473481804721878414603799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2525236291850018211220261 473481804721878414603799)
                ·
                  refine ⟨710222707082817621905699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 473481804721878414603799 710222707082817621905699)
                  ·
                    refine ⟨1065334060624226432858549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 710222707082817621905699 1065334060624226432858549)
                    ·
                      refine ⟨99875068183521228080489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1065334060624226432858549 99875068183521228080489)
                      ·
                        rfl

theorem cell23_194506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 4, 1, 1, 5].length) (baseStart_194506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_194506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_194506 prefixEnd_194506 := by exact prefixLift 194506
  have htrace : WordTrace (prefixWord ++ tailWord_194506) baseStart_194506 baseEnd_194506 := by
    simpa [prefixWord, tailWord_194506, baseEnd_194506] using wordTrace_append hprefix tailTrace_194506
  have hstable : (prefixWord ++ tailWord_194506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194506).length < 2 ^ (prefixWord ++ tailWord_194506).sum := by decide
  have hdescent : baseEnd_194506 < baseStart_194506 := by decide
  rcases family_descends (prefixWord ++ tailWord_194506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194520 : List Nat := [2, 1, 2, 2, 2, 2, 3, 2, 3, 2, 2]
def baseStart_194520 : Nat := 118140960795 + 194520 * 2 ^ 59
def prefixEnd_194520 : Nat := 4983230072969 + 3 ^ 40 * 194520 * 2
def baseEnd_194520 : Nat := 99882256912684173305425

theorem tailTrace_194520 : CollatzResearch.WordTrace tailWord_194520 prefixEnd_194520 99882256912684173305425 := by
  unfold tailWord_194520
  simp only [CollatzResearch.WordTrace]
  refine ⟨3547363627647368108110507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4729818170196490810814009 3547363627647368108110507)
  ·
    refine ⟨5321045441471052162165761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3547363627647368108110507 5321045441471052162165761)
    ·
      refine ⟨3990784081103289121624321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5321045441471052162165761 3990784081103289121624321)
      ·
        refine ⟨2993088060827466841218241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3990784081103289121624321 2993088060827466841218241)
        ·
          refine ⟨2244816045620600130913681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2993088060827466841218241 2244816045620600130913681)
          ·
            refine ⟨1683612034215450098185261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2244816045620600130913681 1683612034215450098185261)
            ·
              refine ⟨631354512830793786819473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1683612034215450098185261 631354512830793786819473)
              ·
                refine ⟨473515884623095340114605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 631354512830793786819473 473515884623095340114605)
                ·
                  refine ⟨177568456733660752542977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 473515884623095340114605 177568456733660752542977)
                  ·
                    refine ⟨133176342550245564407233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 177568456733660752542977 133176342550245564407233)
                    ·
                      refine ⟨99882256912684173305425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 133176342550245564407233 99882256912684173305425)
                      ·
                        rfl

theorem cell23_194520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 2, 3, 2, 2].length) (baseStart_194520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_194520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_194520 prefixEnd_194520 := by exact prefixLift 194520
  have htrace : WordTrace (prefixWord ++ tailWord_194520) baseStart_194520 baseEnd_194520 := by
    simpa [prefixWord, tailWord_194520, baseEnd_194520] using wordTrace_append hprefix tailTrace_194520
  have hstable : (prefixWord ++ tailWord_194520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194520).length < 2 ^ (prefixWord ++ tailWord_194520).sum := by decide
  have hdescent : baseEnd_194520 < baseStart_194520 := by decide
  rcases family_descends (prefixWord ++ tailWord_194520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194524 : List Nat := [2, 2, 6, 1, 1, 1, 1, 1, 1, 5, 2]
def baseStart_194524 : Nat := 118140960795 + 194524 * 2 ^ 59
def prefixEnd_194524 : Nat := 4983230072969 + 3 ^ 40 * 194524 * 2
def baseEnd_194524 : Nat := 99884310835302157655407

theorem tailTrace_194524 : CollatzResearch.WordTrace tailWord_194524 prefixEnd_194524 99884310835302157655407 := by
  unfold tailWord_194524
  simp only [CollatzResearch.WordTrace]
  refine ⟨3547436573640122449683313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4729915431520163266244417 3547436573640122449683313)
  ·
    refine ⟨2660577430230091837262485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3547436573640122449683313 2660577430230091837262485)
    ·
      refine ⟨124714567042035554871679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 2660577430230091837262485 124714567042035554871679)
      ·
        refine ⟨187071850563053332307519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124714567042035554871679 187071850563053332307519)
        ·
          refine ⟨280607775844579998461279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187071850563053332307519 280607775844579998461279)
          ·
            refine ⟨420911663766869997691919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 280607775844579998461279 420911663766869997691919)
            ·
              refine ⟨631367495650304996537879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 420911663766869997691919 631367495650304996537879)
              ·
                refine ⟨947051243475457494806819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 631367495650304996537879 947051243475457494806819)
                ·
                  refine ⟨1420576865213186242210229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 947051243475457494806819 1420576865213186242210229)
                  ·
                    refine ⟨133179081113736210207209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1420576865213186242210229 133179081113736210207209)
                    ·
                      refine ⟨99884310835302157655407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 133179081113736210207209 99884310835302157655407)
                      ·
                        rfl

theorem cell23_194524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_194524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_194524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_194524 prefixEnd_194524 := by exact prefixLift 194524
  have htrace : WordTrace (prefixWord ++ tailWord_194524) baseStart_194524 baseEnd_194524 := by
    simpa [prefixWord, tailWord_194524, baseEnd_194524] using wordTrace_append hprefix tailTrace_194524
  have hstable : (prefixWord ++ tailWord_194524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194524).length < 2 ^ (prefixWord ++ tailWord_194524).sum := by decide
  have hdescent : baseEnd_194524 < baseStart_194524 := by decide
  rcases family_descends (prefixWord ++ tailWord_194524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194563 : List Nat := [1, 1, 1, 3, 2, 1, 1, 3, 5, 3, 2]
def baseStart_194563 : Nat := 118140960795 + 194563 * 2 ^ 59
def prefixEnd_194563 : Nat := 4983230072969 + 3 ^ 40 * 194563 * 2
def baseEnd_194563 : Nat := 99904336580827505067727

theorem tailTrace_194563 : CollatzResearch.WordTrace tailWord_194563 prefixEnd_194563 99904336580827505067727 := by
  unfold tailWord_194563
  simp only [CollatzResearch.WordTrace]
  refine ⟨7096295594138954560036343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4730863729425969706690895 7096295594138954560036343)
  ·
    refine ⟨10644443391208431840054515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7096295594138954560036343 10644443391208431840054515)
    ·
      refine ⟨15966665086812647760081773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10644443391208431840054515 15966665086812647760081773)
      ·
        refine ⟨5987499407554742910030665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15966665086812647760081773 5987499407554742910030665)
        ·
          refine ⟨4490624555666057182522999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5987499407554742910030665 4490624555666057182522999)
          ·
            refine ⟨6735936833499085773784499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4490624555666057182522999 6735936833499085773784499)
            ·
              refine ⟨10103905250248628660676749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6735936833499085773784499 10103905250248628660676749)
              ·
                refine ⟨3788964468843235747753781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10103905250248628660676749 3788964468843235747753781)
                ·
                  refine ⟨355215418954053351351917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3788964468843235747753781 355215418954053351351917)
                  ·
                    refine ⟨133205782107770006756969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 355215418954053351351917 133205782107770006756969)
                    ·
                      refine ⟨99904336580827505067727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 133205782107770006756969 99904336580827505067727)
                      ·
                        rfl

theorem cell23_194563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 3, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 3, 5, 3, 2].length) (baseStart_194563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_194563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_194563 prefixEnd_194563 := by exact prefixLift 194563
  have htrace : WordTrace (prefixWord ++ tailWord_194563) baseStart_194563 baseEnd_194563 := by
    simpa [prefixWord, tailWord_194563, baseEnd_194563] using wordTrace_append hprefix tailTrace_194563
  have hstable : (prefixWord ++ tailWord_194563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194563).length < 2 ^ (prefixWord ++ tailWord_194563).sum := by decide
  have hdescent : baseEnd_194563 < baseStart_194563 := by decide
  rcases family_descends (prefixWord ++ tailWord_194563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194564 : List Nat := [2, 3, 2, 4, 1, 1, 3, 1, 2, 4]
def baseStart_194564 : Nat := 118140960795 + 194564 * 2 ^ 59
def prefixEnd_194564 : Nat := 4983230072969 + 3 ^ 40 * 194564 * 2
def baseEnd_194564 : Nat := 33301616687160667051741

theorem tailTrace_194564 : CollatzResearch.WordTrace tailWord_194564 prefixEnd_194564 33301616687160667051741 := by
  unfold tailWord_194564
  simp only [CollatzResearch.WordTrace]
  refine ⟨3548166033567665865411373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4730888044756887820548497 3548166033567665865411373)
  ·
    refine ⟨1330562262587874699529265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3548166033567665865411373 1330562262587874699529265)
    ·
      refine ⟨997921696940906024646949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1330562262587874699529265 997921696940906024646949)
      ·
        refine ⟨187110318176419879621303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 997921696940906024646949 187110318176419879621303)
        ·
          refine ⟨280665477264629819431955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187110318176419879621303 280665477264629819431955)
          ·
            refine ⟨420998215896944729147933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 280665477264629819431955 420998215896944729147933)
            ·
              refine ⟨157874330961354273430475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 420998215896944729147933 157874330961354273430475)
              ·
                refine ⟨236811496442031410145713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 157874330961354273430475 236811496442031410145713)
                ·
                  refine ⟨177608622331523557609285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 236811496442031410145713 177608622331523557609285)
                  ·
                    refine ⟨33301616687160667051741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 177608622331523557609285 33301616687160667051741)
                    ·
                      rfl

theorem cell23_194564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 3, 1, 2, 4].length) (baseStart_194564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_194564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_194564 prefixEnd_194564 := by exact prefixLift 194564
  have htrace : WordTrace (prefixWord ++ tailWord_194564) baseStart_194564 baseEnd_194564 := by
    simpa [prefixWord, tailWord_194564, baseEnd_194564] using wordTrace_append hprefix tailTrace_194564
  have hstable : (prefixWord ++ tailWord_194564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194564).length < 2 ^ (prefixWord ++ tailWord_194564).sum := by decide
  have hdescent : baseEnd_194564 < baseStart_194564 := by decide
  rcases family_descends (prefixWord ++ tailWord_194564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194630 : List Nat := [6, 1, 1, 1, 1, 1, 1, 1, 4, 1, 5]
def baseStart_194630 : Nat := 118140960795 + 194630 * 2 ^ 59
def prefixEnd_194630 : Nat := 4983230072969 + 3 ^ 40 * 194630 * 2
def baseEnd_194630 : Nat := 99938739784678742929919

theorem tailTrace_194630 : CollatzResearch.WordTrace tailWord_194630 prefixEnd_194630 99938739784678742929919 := by
  unfold tailWord_194630
  simp only [CollatzResearch.WordTrace]
  refine ⟨221835602653007031335167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 4732492856597483335150229 221835602653007031335167)
  ·
    refine ⟨332753403979510547002751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 221835602653007031335167 332753403979510547002751)
    ·
      refine ⟨499130105969265820504127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 332753403979510547002751 499130105969265820504127)
      ·
        refine ⟨748695158953898730756191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 499130105969265820504127 748695158953898730756191)
        ·
          refine ⟨1123042738430848096134287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 748695158953898730756191 1123042738430848096134287)
          ·
            refine ⟨1684564107646272144201431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1123042738430848096134287 1684564107646272144201431)
            ·
              refine ⟨2526846161469408216302147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1684564107646272144201431 2526846161469408216302147)
              ·
                refine ⟨3790269242204112324453221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2526846161469408216302147 3790269242204112324453221)
                ·
                  refine ⟨710675482913271060834979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3790269242204112324453221 710675482913271060834979)
                  ·
                    refine ⟨1066013224369906591252469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 710675482913271060834979 1066013224369906591252469)
                    ·
                      refine ⟨99938739784678742929919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1066013224369906591252469 99938739784678742929919)
                      ·
                        rfl

theorem cell23_194630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_194630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_194630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_194630 prefixEnd_194630 := by exact prefixLift 194630
  have htrace : WordTrace (prefixWord ++ tailWord_194630) baseStart_194630 baseEnd_194630 := by
    simpa [prefixWord, tailWord_194630, baseEnd_194630] using wordTrace_append hprefix tailTrace_194630
  have hstable : (prefixWord ++ tailWord_194630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194630).length < 2 ^ (prefixWord ++ tailWord_194630).sum := by decide
  have hdescent : baseEnd_194630 < baseStart_194630 := by decide
  rcases family_descends (prefixWord ++ tailWord_194630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194663 : List Nat := [1, 1, 5, 1, 1, 2, 1, 4, 2, 5]
def baseStart_194663 : Nat := 118140960795 + 194663 * 2 ^ 59
def prefixEnd_194663 : Nat := 4983230072969 + 3 ^ 40 * 194663 * 2
def baseEnd_194663 : Nat := 33318561548759037939089

theorem tailTrace_194663 : CollatzResearch.WordTrace tailWord_194663 prefixEnd_194663 33318561548759037939089 := by
  unfold tailWord_194663
  simp only [CollatzResearch.WordTrace]
  refine ⟨7099942893776671638676643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4733295262517781092451095 7099942893776671638676643)
  ·
    refine ⟨10649914340665007458014965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7099942893776671638676643 10649914340665007458014965)
    ·
      refine ⟨998429469437344449188903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10649914340665007458014965 998429469437344449188903)
      ·
        refine ⟨1497644204156016673783355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 998429469437344449188903 1497644204156016673783355)
        ·
          refine ⟨2246466306234025010675033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1497644204156016673783355 2246466306234025010675033)
          ·
            refine ⟨1684849729675518758006275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2246466306234025010675033 1684849729675518758006275)
            ·
              refine ⟨2527274594513278137009413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1684849729675518758006275 2527274594513278137009413)
              ·
                refine ⟨473863986471239650689265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2527274594513278137009413 473863986471239650689265)
                ·
                  refine ⟨355397989853429738016949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 473863986471239650689265 355397989853429738016949)
                  ·
                    refine ⟨33318561548759037939089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 355397989853429738016949 33318561548759037939089)
                    ·
                      rfl

theorem cell23_194663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 4, 2, 5].length) (baseStart_194663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_194663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_194663 prefixEnd_194663 := by exact prefixLift 194663
  have htrace : WordTrace (prefixWord ++ tailWord_194663) baseStart_194663 baseEnd_194663 := by
    simpa [prefixWord, tailWord_194663, baseEnd_194663] using wordTrace_append hprefix tailTrace_194663
  have hstable : (prefixWord ++ tailWord_194663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194663).length < 2 ^ (prefixWord ++ tailWord_194663).sum := by decide
  have hdescent : baseEnd_194663 < baseStart_194663 := by decide
  rcases family_descends (prefixWord ++ tailWord_194663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194670 : List Nat := [4, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2]
def baseStart_194670 : Nat := 118140960795 + 194670 * 2 ^ 59
def prefixEnd_194670 : Nat := 4983230072969 + 3 ^ 40 * 194670 * 2
def baseEnd_194670 : Nat := 99959279010858586429735

theorem tailTrace_194670 : CollatzResearch.WordTrace tailWord_194670 prefixEnd_194670 99959279010858586429735 := by
  unfold tailWord_194670
  simp only [CollatzResearch.WordTrace]
  refine ⟨887524775593913979272683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4733465469834207889454309 887524775593913979272683)
  ·
    refine ⟨1331287163390870968909025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 887524775593913979272683 1331287163390870968909025)
    ·
      refine ⟨998465372543153226681769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1331287163390870968909025 998465372543153226681769)
      ·
        refine ⟨748849029407364920011327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 998465372543153226681769 748849029407364920011327)
        ·
          refine ⟨1123273544111047380016991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 748849029407364920011327 1123273544111047380016991)
          ·
            refine ⟨1684910316166571070025487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1123273544111047380016991 1684910316166571070025487)
            ·
              refine ⟨2527365474249856605038231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1684910316166571070025487 2527365474249856605038231)
              ·
                refine ⟨3791048211374784907557347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2527365474249856605038231 3791048211374784907557347)
                ·
                  refine ⟨5686572317062177361336021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3791048211374784907557347 5686572317062177361336021)
                  ·
                    refine ⟨133279038681144781906313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5686572317062177361336021 133279038681144781906313)
                    ·
                      refine ⟨99959279010858586429735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 133279038681144781906313 99959279010858586429735)
                      ·
                        rfl

theorem cell23_194670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2].length) (baseStart_194670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_194670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_194670 prefixEnd_194670 := by exact prefixLift 194670
  have htrace : WordTrace (prefixWord ++ tailWord_194670) baseStart_194670 baseEnd_194670 := by
    simpa [prefixWord, tailWord_194670, baseEnd_194670] using wordTrace_append hprefix tailTrace_194670
  have hstable : (prefixWord ++ tailWord_194670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194670).length < 2 ^ (prefixWord ++ tailWord_194670).sum := by decide
  have hdescent : baseEnd_194670 < baseStart_194670 := by decide
  rcases family_descends (prefixWord ++ tailWord_194670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194754 : List Nat := [3, 5, 1, 1, 1, 1, 2, 1, 1, 4, 3]
def baseStart_194754 : Nat := 118140960795 + 194754 * 2 ^ 59
def prefixEnd_194754 : Nat := 4983230072969 + 3 ^ 40 * 194754 * 2
def baseEnd_194754 : Nat := 100002411385836257779349

theorem tailTrace_194754 : CollatzResearch.WordTrace tailWord_194754 prefixEnd_194754 100002411385836257779349 := by
  unfold tailWord_194754
  simp only [CollatzResearch.WordTrace]
  refine ⟨1775815484111748545059829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4735507957631329453492877 1775815484111748545059829)
  ·
    refine ⟨166482701635476426099359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1775815484111748545059829 166482701635476426099359)
    ·
      refine ⟨249724052453214639149039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166482701635476426099359 249724052453214639149039)
      ·
        refine ⟨374586078679821958723559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 249724052453214639149039 374586078679821958723559)
        ·
          refine ⟨561879118019732938085339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 374586078679821958723559 561879118019732938085339)
          ·
            refine ⟨842818677029599407128009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 561879118019732938085339 842818677029599407128009)
            ·
              refine ⟨632114007772199555346007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 842818677029599407128009 632114007772199555346007)
              ·
                refine ⟨948171011658299333019011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 632114007772199555346007 948171011658299333019011)
                ·
                  refine ⟨1422256517487448999528517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 948171011658299333019011 1422256517487448999528517)
                  ·
                    refine ⟨266673097028896687411597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1422256517487448999528517 266673097028896687411597)
                    ·
                      refine ⟨100002411385836257779349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 266673097028896687411597 100002411385836257779349)
                      ·
                        rfl

theorem cell23_194754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_194754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_194754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_194754 prefixEnd_194754 := by exact prefixLift 194754
  have htrace : WordTrace (prefixWord ++ tailWord_194754) baseStart_194754 baseEnd_194754 := by
    simpa [prefixWord, tailWord_194754, baseEnd_194754] using wordTrace_append hprefix tailTrace_194754
  have hstable : (prefixWord ++ tailWord_194754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194754).length < 2 ^ (prefixWord ++ tailWord_194754).sum := by decide
  have hdescent : baseEnd_194754 < baseStart_194754 := by decide
  rcases family_descends (prefixWord ++ tailWord_194754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194803 : List Nat := [1, 1, 1, 2, 2, 4, 1, 3, 1, 1, 6]
def baseStart_194803 : Nat := 118140960795 + 194803 * 2 ^ 59
def prefixEnd_194803 : Nat := 4983230072969 + 3 ^ 40 * 194803 * 2
def baseEnd_194803 : Nat := 100027571937906566066623

theorem tailTrace_194803 : CollatzResearch.WordTrace tailWord_194803 prefixEnd_194803 100027571937906566066623 := by
  unfold tailWord_194803
  simp only [CollatzResearch.WordTrace]
  refine ⟨7105049113269475548773063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4736699408846317032515375 7105049113269475548773063)
  ·
    refine ⟨10657573669904213323159595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7105049113269475548773063 10657573669904213323159595)
    ·
      refine ⟨15986360504856319984739393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10657573669904213323159595 15986360504856319984739393)
      ·
        refine ⟨11989770378642239988554545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15986360504856319984739393 11989770378642239988554545)
        ·
          refine ⟨8992327783981679991415909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11989770378642239988554545 8992327783981679991415909)
          ·
            refine ⟨1686061459496564998390483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8992327783981679991415909 1686061459496564998390483)
            ·
              refine ⟨2529092189244847497585725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1686061459496564998390483 2529092189244847497585725)
              ·
                refine ⟨948409570966817811594647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2529092189244847497585725 948409570966817811594647)
                ·
                  refine ⟨1422614356450226717391971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 948409570966817811594647 1422614356450226717391971)
                  ·
                    refine ⟨2133921534675340076087957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1422614356450226717391971 2133921534675340076087957)
                    ·
                      refine ⟨100027571937906566066623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2133921534675340076087957 100027571937906566066623)
                      ·
                        rfl

theorem cell23_194803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 3, 1, 1, 6].length) (baseStart_194803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_194803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_194803 prefixEnd_194803 := by exact prefixLift 194803
  have htrace : WordTrace (prefixWord ++ tailWord_194803) baseStart_194803 baseEnd_194803 := by
    simpa [prefixWord, tailWord_194803, baseEnd_194803] using wordTrace_append hprefix tailTrace_194803
  have hstable : (prefixWord ++ tailWord_194803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194803).length < 2 ^ (prefixWord ++ tailWord_194803).sum := by decide
  have hdescent : baseEnd_194803 < baseStart_194803 := by decide
  rcases family_descends (prefixWord ++ tailWord_194803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194824 : List Nat := [2, 1, 3, 2, 3, 2, 3, 1, 1, 1, 4]
def baseStart_194824 : Nat := 118140960795 + 194824 * 2 ^ 59
def prefixEnd_194824 : Nat := 4983230072969 + 3 ^ 40 * 194824 * 2
def baseEnd_194824 : Nat := 100038355031650983904027

theorem tailTrace_194824 : CollatzResearch.WordTrace tailWord_194824 prefixEnd_194824 100038355031650983904027 := by
  unfold tailWord_194824
  simp only [CollatzResearch.WordTrace]
  refine ⟨3552907523096698067643763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4737210030795597423525017 3552907523096698067643763)
  ·
    refine ⟨5329361284645047101465645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3552907523096698067643763 5329361284645047101465645)
    ·
      refine ⟨1998510481741892663049617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5329361284645047101465645 1998510481741892663049617)
      ·
        refine ⟨1498882861306419497287213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1998510481741892663049617 1498882861306419497287213)
        ·
          refine ⟨562081072989907311482705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1498882861306419497287213 562081072989907311482705)
          ·
            refine ⟨421560804742430483612029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 562081072989907311482705 421560804742430483612029)
            ·
              refine ⟨158085301778411431354511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 421560804742430483612029 158085301778411431354511)
              ·
                refine ⟨237127952667617147031767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 158085301778411431354511 237127952667617147031767)
                ·
                  refine ⟨355691929001425720547651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 237127952667617147031767 355691929001425720547651)
                  ·
                    refine ⟨533537893502138580821477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 355691929001425720547651 533537893502138580821477)
                    ·
                      refine ⟨100038355031650983904027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 533537893502138580821477 100038355031650983904027)
                      ·
                        rfl

theorem cell23_194824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 3, 1, 1, 1, 4].length) (baseStart_194824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_194824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_194824 prefixEnd_194824 := by exact prefixLift 194824
  have htrace : WordTrace (prefixWord ++ tailWord_194824) baseStart_194824 baseEnd_194824 := by
    simpa [prefixWord, tailWord_194824, baseEnd_194824] using wordTrace_append hprefix tailTrace_194824
  have hstable : (prefixWord ++ tailWord_194824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194824).length < 2 ^ (prefixWord ++ tailWord_194824).sum := by decide
  have hdescent : baseEnd_194824 < baseStart_194824 := by decide
  rcases family_descends (prefixWord ++ tailWord_194824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194840 : List Nat := [2, 1, 2, 3, 1, 2, 1, 2, 3, 3, 3]
def baseStart_194840 : Nat := 118140960795 + 194840 * 2 ^ 59
def prefixEnd_194840 : Nat := 4983230072969 + 3 ^ 40 * 194840 * 2
def baseEnd_194840 : Nat := 100046570722122921303953

theorem tailTrace_194840 : CollatzResearch.WordTrace tailWord_194840 prefixEnd_194840 100046570722122921303953 := by
  unfold tailWord_194840
  simp only [CollatzResearch.WordTrace]
  refine ⟨3553199307067715433934987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4737599076090287245246649 3553199307067715433934987)
  ·
    refine ⟨5329798960601573150902481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3553199307067715433934987 5329798960601573150902481)
    ·
      refine ⟨3997349220451179863176861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5329798960601573150902481 3997349220451179863176861)
      ·
        refine ⟨1499005957669192448691323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3997349220451179863176861 1499005957669192448691323)
        ·
          refine ⟨2248508936503788673036985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1499005957669192448691323 2248508936503788673036985)
          ·
            refine ⟨1686381702377841504777739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2248508936503788673036985 1686381702377841504777739)
            ·
              refine ⟨2529572553566762257166609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1686381702377841504777739 2529572553566762257166609)
              ·
                refine ⟨1897179415175071692874957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2529572553566762257166609 1897179415175071692874957)
                ·
                  refine ⟨711442280690651884828109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1897179415175071692874957 711442280690651884828109)
                  ·
                    refine ⟨266790855258994456810541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 711442280690651884828109 266790855258994456810541)
                    ·
                      refine ⟨100046570722122921303953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 266790855258994456810541 100046570722122921303953)
                      ·
                        rfl

theorem cell23_194840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 2, 3, 3, 3].length) (baseStart_194840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_194840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_194840 prefixEnd_194840 := by exact prefixLift 194840
  have htrace : WordTrace (prefixWord ++ tailWord_194840) baseStart_194840 baseEnd_194840 := by
    simpa [prefixWord, tailWord_194840, baseEnd_194840] using wordTrace_append hprefix tailTrace_194840
  have hstable : (prefixWord ++ tailWord_194840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194840).length < 2 ^ (prefixWord ++ tailWord_194840).sum := by decide
  have hdescent : baseEnd_194840 < baseStart_194840 := by decide
  rcases family_descends (prefixWord ++ tailWord_194840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194843 : List Nat := [1, 1, 1, 1, 1, 1, 7, 1, 2, 7]
def baseStart_194843 : Nat := 118140960795 + 194843 * 2 ^ 59
def prefixEnd_194843 : Nat := 4983230072969 + 3 ^ 40 * 194843 * 2
def baseEnd_194843 : Nat := 33349370388028803188813

theorem tailTrace_194843 : CollatzResearch.WordTrace tailWord_194843 prefixEnd_194843 33349370388028803188813 := by
  unfold tailWord_194843
  simp only [CollatzResearch.WordTrace]
  refine ⟨7106508033124562380229183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4737672022083041586819455 7106508033124562380229183)
  ·
    refine ⟨10659762049686843570343775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7106508033124562380229183 10659762049686843570343775)
    ·
      refine ⟨15989643074530265355515663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10659762049686843570343775 15989643074530265355515663)
      ·
        refine ⟨23984464611795398033273495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15989643074530265355515663 23984464611795398033273495)
        ·
          refine ⟨35976696917693097049910243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23984464611795398033273495 35976696917693097049910243)
          ·
            refine ⟨53965045376539645574865365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35976696917693097049910243 53965045376539645574865365)
            ·
              refine ⟨1264805751012647943160907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 53965045376539645574865365 1264805751012647943160907)
              ·
                refine ⟨1897208626518971914741361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1264805751012647943160907 1897208626518971914741361)
                ·
                  refine ⟨1422906469889228936056021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1897208626518971914741361 1422906469889228936056021)
                  ·
                    refine ⟨33349370388028803188813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1422906469889228936056021 33349370388028803188813)
                    ·
                      rfl

theorem cell23_194843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 1, 2, 7].length) (baseStart_194843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_194843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_194843 prefixEnd_194843 := by exact prefixLift 194843
  have htrace : WordTrace (prefixWord ++ tailWord_194843) baseStart_194843 baseEnd_194843 := by
    simpa [prefixWord, tailWord_194843, baseEnd_194843] using wordTrace_append hprefix tailTrace_194843
  have hstable : (prefixWord ++ tailWord_194843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194843).length < 2 ^ (prefixWord ++ tailWord_194843).sum := by decide
  have hdescent : baseEnd_194843 < baseStart_194843 := by decide
  rcases family_descends (prefixWord ++ tailWord_194843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194867 : List Nat := [1, 1, 1, 2, 5, 1, 1, 3, 3, 3, 2]
def baseStart_194867 : Nat := 118140960795 + 194867 * 2 ^ 59
def prefixEnd_194867 : Nat := 4983230072969 + 3 ^ 40 * 194867 * 2
def baseEnd_194867 : Nat := 100060434699794315666329

theorem tailTrace_194867 : CollatzResearch.WordTrace tailWord_194867 prefixEnd_194867 100060434699794315666329 := by
  unfold tailWord_194867
  simp only [CollatzResearch.WordTrace]
  refine ⟨7107383385037614479102855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4738255590025076319401903 7107383385037614479102855)
  ·
    refine ⟨10661075077556421718654283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7107383385037614479102855 10661075077556421718654283)
    ·
      refine ⟨15991612616334632577981425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10661075077556421718654283 15991612616334632577981425)
      ·
        refine ⟨11993709462250974433486069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15991612616334632577981425 11993709462250974433486069)
        ·
          refine ⟨1124410262086028853139319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11993709462250974433486069 1124410262086028853139319)
          ·
            refine ⟨1686615393129043279708979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1124410262086028853139319 1686615393129043279708979)
            ·
              refine ⟨2529923089693564919563469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1686615393129043279708979 2529923089693564919563469)
              ·
                refine ⟨948721158635086844836301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2529923089693564919563469 948721158635086844836301)
                ·
                  refine ⟨355770434488157566813613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 948721158635086844836301 355770434488157566813613)
                  ·
                    refine ⟨133413912933059087555105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 355770434488157566813613 133413912933059087555105)
                    ·
                      refine ⟨100060434699794315666329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 133413912933059087555105 100060434699794315666329)
                      ·
                        rfl

theorem cell23_194867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 3, 3, 3, 2].length) (baseStart_194867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_194867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_194867 prefixEnd_194867 := by exact prefixLift 194867
  have htrace : WordTrace (prefixWord ++ tailWord_194867) baseStart_194867 baseEnd_194867 := by
    simpa [prefixWord, tailWord_194867, baseEnd_194867] using wordTrace_append hprefix tailTrace_194867
  have hstable : (prefixWord ++ tailWord_194867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194867).length < 2 ^ (prefixWord ++ tailWord_194867).sum := by decide
  have hdescent : baseEnd_194867 < baseStart_194867 := by decide
  rcases family_descends (prefixWord ++ tailWord_194867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194908 : List Nat := [2, 2, 4, 3, 2, 1, 1, 1, 1, 3, 3]
def baseStart_194908 : Nat := 118140960795 + 194908 * 2 ^ 59
def prefixEnd_194908 : Nat := 4983230072969 + 3 ^ 40 * 194908 * 2
def baseEnd_194908 : Nat := 100081487406628655253641

theorem tailTrace_194908 : CollatzResearch.WordTrace tailWord_194908 prefixEnd_194908 100081487406628655253641 := by
  unfold tailWord_194908
  simp only [CollatzResearch.WordTrace]
  refine ⟨3554439388944539240672689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4739252518592718987563585 3554439388944539240672689)
  ·
    refine ⟨2665829541708404430504517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3554439388944539240672689 2665829541708404430504517)
    ·
      refine ⟨499843039070325830719597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2665829541708404430504517 499843039070325830719597)
      ·
        refine ⟨187441139651372186519849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 499843039070325830719597 187441139651372186519849)
        ·
          refine ⟨140580854738529139889887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187441139651372186519849 140580854738529139889887)
          ·
            refine ⟨210871282107793709834831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140580854738529139889887 210871282107793709834831)
            ·
              refine ⟨316306923161690564752247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 210871282107793709834831 316306923161690564752247)
              ·
                refine ⟨474460384742535847128371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 316306923161690564752247 474460384742535847128371)
                ·
                  refine ⟨711690577113803770692557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 474460384742535847128371 711690577113803770692557)
                  ·
                    refine ⟨266883966417676414009709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 711690577113803770692557 266883966417676414009709)
                    ·
                      refine ⟨100081487406628655253641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 266883966417676414009709 100081487406628655253641)
                      ·
                        rfl

theorem cell23_194908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_194908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_194908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_194908 prefixEnd_194908 := by exact prefixLift 194908
  have htrace : WordTrace (prefixWord ++ tailWord_194908) baseStart_194908 baseEnd_194908 := by
    simpa [prefixWord, tailWord_194908, baseEnd_194908] using wordTrace_append hprefix tailTrace_194908
  have hstable : (prefixWord ++ tailWord_194908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194908).length < 2 ^ (prefixWord ++ tailWord_194908).sum := by decide
  have hdescent : baseEnd_194908 < baseStart_194908 := by decide
  rcases family_descends (prefixWord ++ tailWord_194908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194980 : List Nat := [2, 3, 1, 2, 1, 1, 2, 1, 2, 8]
def baseStart_194980 : Nat := 118140960795 + 194980 * 2 ^ 59
def prefixEnd_194980 : Nat := 4983230072969 + 3 ^ 40 * 194980 * 2
def baseEnd_194980 : Nat := 33372819337917457851103

theorem tailTrace_194980 : CollatzResearch.WordTrace tailWord_194980 prefixEnd_194980 33372819337917457851103 := by
  unfold tailWord_194980
  simp only [CollatzResearch.WordTrace]
  refine ⟨3555752416814117388983197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4741003222418823185310929 3555752416814117388983197)
  ·
    refine ⟨1333407156305294020868699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3555752416814117388983197 1333407156305294020868699)
    ·
      refine ⟨2000110734457941031303049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1333407156305294020868699 2000110734457941031303049)
      ·
        refine ⟨1500083050843455773477287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2000110734457941031303049 1500083050843455773477287)
        ·
          refine ⟨2250124576265183660215931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1500083050843455773477287 2250124576265183660215931)
          ·
            refine ⟨3375186864397775490323897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2250124576265183660215931 3375186864397775490323897)
            ·
              refine ⟨2531390148298331617742923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3375186864397775490323897 2531390148298331617742923)
              ·
                refine ⟨3797085222447497426614385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2531390148298331617742923 3797085222447497426614385)
                ·
                  refine ⟨2847813916835623069960789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3797085222447497426614385 2847813916835623069960789)
                  ·
                    refine ⟨33372819337917457851103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 2847813916835623069960789 33372819337917457851103)
                    ·
                      rfl

theorem cell23_194980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 1, 2, 8].length) (baseStart_194980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_194980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_194980 prefixEnd_194980 := by exact prefixLift 194980
  have htrace : WordTrace (prefixWord ++ tailWord_194980) baseStart_194980 baseEnd_194980 := by
    simpa [prefixWord, tailWord_194980, baseEnd_194980] using wordTrace_append hprefix tailTrace_194980
  have hstable : (prefixWord ++ tailWord_194980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194980).length < 2 ^ (prefixWord ++ tailWord_194980).sum := by decide
  have hdescent : baseEnd_194980 < baseStart_194980 := by decide
  rcases family_descends (prefixWord ++ tailWord_194980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_194984 : List Nat := [2, 1, 6, 1, 1, 1, 1, 3, 2, 5]
def baseStart_194984 : Nat := 118140960795 + 194984 * 2 ^ 59
def prefixEnd_194984 : Nat := 4983230072969 + 3 ^ 40 * 194984 * 2
def baseEnd_194984 : Nat := 33373503978790119301097

theorem tailTrace_194984 : CollatzResearch.WordTrace tailWord_194984 prefixEnd_194984 33373503978790119301097 := by
  unfold tailWord_194984
  simp only [CollatzResearch.WordTrace]
  refine ⟨3555825362806871730556003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4741100483742495640741337 3555825362806871730556003)
  ·
    refine ⟨5333738044210307595834005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3555825362806871730556003 5333738044210307595834005)
    ·
      refine ⟨250018970822358168554719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 5333738044210307595834005 250018970822358168554719)
      ·
        refine ⟨375028456233537252832079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250018970822358168554719 375028456233537252832079)
        ·
          refine ⟨562542684350305879248119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 375028456233537252832079 562542684350305879248119)
          ·
            refine ⟨843814026525458818872179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 562542684350305879248119 843814026525458818872179)
            ·
              refine ⟨1265721039788188228308269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 843814026525458818872179 1265721039788188228308269)
              ·
                refine ⟨474645389920570585615601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1265721039788188228308269 474645389920570585615601)
                ·
                  refine ⟨355984042440427939211701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 474645389920570585615601 355984042440427939211701)
                  ·
                    refine ⟨33373503978790119301097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 355984042440427939211701 33373503978790119301097)
                    ·
                      rfl

theorem cell23_194984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_194984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_194984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_194984 prefixEnd_194984 := by exact prefixLift 194984
  have htrace : WordTrace (prefixWord ++ tailWord_194984) baseStart_194984 baseEnd_194984 := by
    simpa [prefixWord, tailWord_194984, baseEnd_194984] using wordTrace_append hprefix tailTrace_194984
  have hstable : (prefixWord ++ tailWord_194984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_194984).length < 2 ^ (prefixWord ++ tailWord_194984).sum := by decide
  have hdescent : baseEnd_194984 < baseStart_194984 := by decide
  rcases family_descends (prefixWord ++ tailWord_194984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195000 : List Nat := [2, 1, 2, 1, 2, 2, 1, 3, 2, 1, 6]
def baseStart_195000 : Nat := 118140960795 + 195000 * 2 ^ 59
def prefixEnd_195000 : Nat := 4983230072969 + 3 ^ 40 * 195000 * 2
def baseEnd_195000 : Nat := 100128727626842295303217

theorem tailTrace_195000 : CollatzResearch.WordTrace tailWord_195000 prefixEnd_195000 100128727626842295303217 := by
  unfold tailWord_195000
  simp only [CollatzResearch.WordTrace]
  refine ⟨3556117146777889096847227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4741489529037185462462969 3556117146777889096847227)
  ·
    refine ⟨5334175720166833645270841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3556117146777889096847227 5334175720166833645270841)
    ·
      refine ⟨4000631790125125233953131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5334175720166833645270841 4000631790125125233953131)
      ·
        refine ⟨6000947685187687850929697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4000631790125125233953131 6000947685187687850929697)
        ·
          refine ⟨4500710763890765888197273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6000947685187687850929697 4500710763890765888197273)
          ·
            refine ⟨3375533072918074416147955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4500710763890765888197273 3375533072918074416147955)
            ·
              refine ⟨5063299609377111624221933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3375533072918074416147955 5063299609377111624221933)
              ·
                refine ⟨1898737353516416859083225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5063299609377111624221933 1898737353516416859083225)
                ·
                  refine ⟨1424053015137312644312419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1898737353516416859083225 1424053015137312644312419)
                  ·
                    refine ⟨2136079522705968966468629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1424053015137312644312419 2136079522705968966468629)
                    ·
                      refine ⟨100128727626842295303217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 2136079522705968966468629 100128727626842295303217)
                      ·
                        rfl

theorem cell23_195000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 3, 2, 1, 6].length) (baseStart_195000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_195000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_195000 prefixEnd_195000 := by exact prefixLift 195000
  have htrace : WordTrace (prefixWord ++ tailWord_195000) baseStart_195000 baseEnd_195000 := by
    simpa [prefixWord, tailWord_195000, baseEnd_195000] using wordTrace_append hprefix tailTrace_195000
  have hstable : (prefixWord ++ tailWord_195000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195000).length < 2 ^ (prefixWord ++ tailWord_195000).sum := by decide
  have hdescent : baseEnd_195000 < baseStart_195000 := by decide
  rcases family_descends (prefixWord ++ tailWord_195000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195004 : List Nat := [2, 2, 2, 4, 1, 1, 2, 2, 2, 1, 4]
def baseStart_195004 : Nat := 118140960795 + 195004 * 2 ^ 59
def prefixEnd_195004 : Nat := 4983230072969 + 3 ^ 40 * 195004 * 2
def baseEnd_195004 : Nat := 100130781549460279653199

theorem tailTrace_195004 : CollatzResearch.WordTrace tailWord_195004 prefixEnd_195004 100130781549460279653199 := by
  unfold tailWord_195004
  simp only [CollatzResearch.WordTrace]
  refine ⟨3556190092770643438420033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4741586790360857917893377 3556190092770643438420033)
  ·
    refine ⟨2667142569577982578815025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3556190092770643438420033 2667142569577982578815025)
    ·
      refine ⟨2000356927183486934111269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2667142569577982578815025 2000356927183486934111269)
      ·
        refine ⟨375066923846903800145863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2000356927183486934111269 375066923846903800145863)
        ·
          refine ⟨562600385770355700218795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 375066923846903800145863 562600385770355700218795)
          ·
            refine ⟨843900578655533550328193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 562600385770355700218795 843900578655533550328193)
            ·
              refine ⟨632925433991650162746145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 843900578655533550328193 632925433991650162746145)
              ·
                refine ⟨474694075493737622059609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 632925433991650162746145 474694075493737622059609)
                ·
                  refine ⟨356020556620303216544707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 474694075493737622059609 356020556620303216544707)
                  ·
                    refine ⟨534030834930454824817061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 356020556620303216544707 534030834930454824817061)
                    ·
                      refine ⟨100130781549460279653199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 534030834930454824817061 100130781549460279653199)
                      ·
                        rfl

theorem cell23_195004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_195004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_195004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_195004 prefixEnd_195004 := by exact prefixLift 195004
  have htrace : WordTrace (prefixWord ++ tailWord_195004) baseStart_195004 baseEnd_195004 := by
    simpa [prefixWord, tailWord_195004, baseEnd_195004] using wordTrace_append hprefix tailTrace_195004
  have hstable : (prefixWord ++ tailWord_195004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195004).length < 2 ^ (prefixWord ++ tailWord_195004).sum := by decide
  have hdescent : baseEnd_195004 < baseStart_195004 := by decide
  rcases family_descends (prefixWord ++ tailWord_195004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195064 : List Nat := [2, 1, 2, 1, 1, 4, 2, 1, 4, 3, 2]
def baseStart_195064 : Nat := 118140960795 + 195064 * 2 ^ 59
def prefixEnd_195064 : Nat := 4983230072969 + 3 ^ 40 * 195064 * 2
def baseEnd_195064 : Nat := 100161590388730044902923

theorem tailTrace_195064 : CollatzResearch.WordTrace tailWord_195064 prefixEnd_195064 100161590388730044902923 := by
  unfold tailWord_195064
  simp only [CollatzResearch.WordTrace]
  refine ⟨3557284282661958562012123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4743045710215944749349497 3557284282661958562012123)
  ·
    refine ⟨5335926423992937843018185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3557284282661958562012123 5335926423992937843018185)
    ·
      refine ⟨4001944817994703382263639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5335926423992937843018185 4001944817994703382263639)
      ·
        refine ⟨6002917226992055073395459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4001944817994703382263639 6002917226992055073395459)
        ·
          refine ⟨9004375840488082610093189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6002917226992055073395459 9004375840488082610093189)
          ·
            refine ⟨1688320470091515489392473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9004375840488082610093189 1688320470091515489392473)
            ·
              refine ⟨1266240352568636617044355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1688320470091515489392473 1266240352568636617044355)
              ·
                refine ⟨1899360528852954925566533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1266240352568636617044355 1899360528852954925566533)
                ·
                  refine ⟨356130099159929048543725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1899360528852954925566533 356130099159929048543725)
                  ·
                    refine ⟨133548787184973393203897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 356130099159929048543725 133548787184973393203897)
                    ·
                      refine ⟨100161590388730044902923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 133548787184973393203897 100161590388730044902923)
                      ·
                        rfl

theorem cell23_195064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 1, 4, 3, 2].length) (baseStart_195064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_195064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_195064 prefixEnd_195064 := by exact prefixLift 195064
  have htrace : WordTrace (prefixWord ++ tailWord_195064) baseStart_195064 baseEnd_195064 := by
    simpa [prefixWord, tailWord_195064, baseEnd_195064] using wordTrace_append hprefix tailTrace_195064
  have hstable : (prefixWord ++ tailWord_195064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195064).length < 2 ^ (prefixWord ++ tailWord_195064).sum := by decide
  have hdescent : baseEnd_195064 < baseStart_195064 := by decide
  rcases family_descends (prefixWord ++ tailWord_195064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195071 : List Nat := [1, 1, 2, 2, 1, 2, 3, 6, 1, 1, 3]
def baseStart_195071 : Nat := 118140960795 + 195071 * 2 ^ 59
def prefixEnd_195071 : Nat := 4983230072969 + 3 ^ 40 * 195071 * 2
def baseEnd_195071 : Nat := 100165184753311517515391

theorem tailTrace_195071 : CollatzResearch.WordTrace tailWord_195071 prefixEnd_195071 100165184753311517515391 := by
  unfold tailWord_195071
  simp only [CollatzResearch.WordTrace]
  refine ⟨7114823876298557319529067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4743215917532371546352711 7114823876298557319529067)
  ·
    refine ⟨10672235814447835979293601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7114823876298557319529067 10672235814447835979293601)
    ·
      refine ⟨8004176860835876984470201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10672235814447835979293601 8004176860835876984470201)
      ·
        refine ⟨6003132645626907738352651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8004176860835876984470201 6003132645626907738352651)
        ·
          refine ⟨9004698968440361607528977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6003132645626907738352651 9004698968440361607528977)
          ·
            refine ⟨6753524226330271205646733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9004698968440361607528977 6753524226330271205646733)
            ·
              refine ⟨2532571584873851702117525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6753524226330271205646733 2532571584873851702117525)
              ·
                refine ⟨118714293040961798536759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2532571584873851702117525 118714293040961798536759)
                ·
                  refine ⟨178071439561442697805139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 118714293040961798536759 178071439561442697805139)
                  ·
                    refine ⟨267107159342164046707709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 178071439561442697805139 267107159342164046707709)
                    ·
                      refine ⟨100165184753311517515391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 267107159342164046707709 100165184753311517515391)
                      ·
                        rfl

theorem cell23_195071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 6, 1, 1, 3].length) (baseStart_195071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_195071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_195071 prefixEnd_195071 := by exact prefixLift 195071
  have htrace : WordTrace (prefixWord ++ tailWord_195071) baseStart_195071 baseEnd_195071 := by
    simpa [prefixWord, tailWord_195071, baseEnd_195071] using wordTrace_append hprefix tailTrace_195071
  have hstable : (prefixWord ++ tailWord_195071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195071).length < 2 ^ (prefixWord ++ tailWord_195071).sum := by decide
  have hdescent : baseEnd_195071 < baseStart_195071 := by decide
  rcases family_descends (prefixWord ++ tailWord_195071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195077 : List Nat := [1, 3, 1, 1, 2, 2, 2, 1, 5, 1, 4]
def baseStart_195077 : Nat := 118140960795 + 195077 * 2 ^ 59
def prefixEnd_195077 : Nat := 4983230072969 + 3 ^ 40 * 195077 * 2
def baseEnd_195077 : Nat := 100168265637238494040363

theorem tailTrace_195077 : CollatzResearch.WordTrace tailWord_195077 prefixEnd_195077 100168265637238494040363 := by
  unfold tailWord_195077
  simp only [CollatzResearch.WordTrace]
  refine ⟨7115042714276820344247485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4743361809517880229498323 7115042714276820344247485)
  ·
    refine ⟨2668141017853807629092807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7115042714276820344247485 2668141017853807629092807)
    ·
      refine ⟨4002211526780711443639211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2668141017853807629092807 4002211526780711443639211)
      ·
        refine ⟨6003317290171067165458817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4002211526780711443639211 6003317290171067165458817)
        ·
          refine ⟨4502487967628300374094113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6003317290171067165458817 4502487967628300374094113)
          ·
            refine ⟨3376865975721225280570585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4502487967628300374094113 3376865975721225280570585)
            ·
              refine ⟨2532649481790918960427939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3376865975721225280570585 2532649481790918960427939)
              ·
                refine ⟨3798974222686378440641909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2532649481790918960427939 3798974222686378440641909)
                ·
                  refine ⟨356153833376847978810179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3798974222686378440641909 356153833376847978810179)
                  ·
                    refine ⟨534230750065271968215269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 356153833376847978810179 534230750065271968215269)
                    ·
                      refine ⟨100168265637238494040363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 534230750065271968215269 100168265637238494040363)
                      ·
                        rfl

theorem cell23_195077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 1, 5, 1, 4].length) (baseStart_195077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_195077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_195077 prefixEnd_195077 := by exact prefixLift 195077
  have htrace : WordTrace (prefixWord ++ tailWord_195077) baseStart_195077 baseEnd_195077 := by
    simpa [prefixWord, tailWord_195077, baseEnd_195077] using wordTrace_append hprefix tailTrace_195077
  have hstable : (prefixWord ++ tailWord_195077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195077).length < 2 ^ (prefixWord ++ tailWord_195077).sum := by decide
  have hdescent : baseEnd_195077 < baseStart_195077 := by decide
  rcases family_descends (prefixWord ++ tailWord_195077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195087 : List Nat := [1, 1, 2, 1, 1, 1, 2, 4, 6, 4]
def baseStart_195087 : Nat := 118140960795 + 195087 * 2 ^ 59
def prefixEnd_195087 : Nat := 4983230072969 + 3 ^ 40 * 195087 * 2
def baseEnd_195087 : Nat := 33391133481261151638439

theorem tailTrace_195087 : CollatzResearch.WordTrace tailWord_195087 prefixEnd_195087 33391133481261151638439 := by
  unfold tailWord_195087
  simp only [CollatzResearch.WordTrace]
  refine ⟨7115407444240592052111515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4743604962827061368074343 7115407444240592052111515)
  ·
    refine ⟨10673111166360888078167273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7115407444240592052111515 10673111166360888078167273)
    ·
      refine ⟨8004833374770666058625455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10673111166360888078167273 8004833374770666058625455)
      ·
        refine ⟨12007250062155999087938183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8004833374770666058625455 12007250062155999087938183)
        ·
          refine ⟨18010875093233998631907275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12007250062155999087938183 18010875093233998631907275)
          ·
            refine ⟨27016312639850997947860913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18010875093233998631907275 27016312639850997947860913)
            ·
              refine ⟨20262234479888248460895685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27016312639850997947860913 20262234479888248460895685)
              ·
                refine ⟨3799168964979046586417941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20262234479888248460895685 3799168964979046586417941)
                ·
                  refine ⟨178086045233392808738341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3799168964979046586417941 178086045233392808738341)
                  ·
                    refine ⟨33391133481261151638439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 178086045233392808738341 33391133481261151638439)
                    ·
                      rfl

theorem cell23_195087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 4, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 4, 6, 4].length) (baseStart_195087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_195087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_195087 prefixEnd_195087 := by exact prefixLift 195087
  have htrace : WordTrace (prefixWord ++ tailWord_195087) baseStart_195087 baseEnd_195087 := by
    simpa [prefixWord, tailWord_195087, baseEnd_195087] using wordTrace_append hprefix tailTrace_195087
  have hstable : (prefixWord ++ tailWord_195087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195087).length < 2 ^ (prefixWord ++ tailWord_195087).sum := by decide
  have hdescent : baseEnd_195087 < baseStart_195087 := by decide
  rcases family_descends (prefixWord ++ tailWord_195087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195114 : List Nat := [3, 1, 4, 1, 1, 2, 1, 3, 1, 1, 5]
def baseStart_195114 : Nat := 118140960795 + 195114 * 2 ^ 59
def prefixEnd_195114 : Nat := 4983230072969 + 3 ^ 40 * 195114 * 2
def baseEnd_195114 : Nat := 100187264421454849277693

theorem tailTrace_195114 : CollatzResearch.WordTrace tailWord_195114 prefixEnd_195114 100187264421454849277693 := by
  unfold tailWord_195114
  simp only [CollatzResearch.WordTrace]
  refine ⟨1779098053785693915836099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4744261476761850442229597 1779098053785693915836099)
  ·
    refine ⟨2668647080678540873754149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1779098053785693915836099 2668647080678540873754149)
    ·
      refine ⟨500371327627226413828903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2668647080678540873754149 500371327627226413828903)
      ·
        refine ⟨750556991440839620743355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 500371327627226413828903 750556991440839620743355)
        ·
          refine ⟨1125835487161259431115033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 750556991440839620743355 1125835487161259431115033)
          ·
            refine ⟨844376615370944573336275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1125835487161259431115033 844376615370944573336275)
            ·
              refine ⟨1266564923056416860004413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 844376615370944573336275 1266564923056416860004413)
              ·
                refine ⟨474961846146156322501655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1266564923056416860004413 474961846146156322501655)
                ·
                  refine ⟨712442769219234483752483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 474961846146156322501655 712442769219234483752483)
                  ·
                    refine ⟨1068664153828851725628725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 712442769219234483752483 1068664153828851725628725)
                    ·
                      refine ⟨100187264421454849277693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1068664153828851725628725 100187264421454849277693)
                      ·
                        rfl

theorem cell23_195114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_195114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_195114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_195114 prefixEnd_195114 := by exact prefixLift 195114
  have htrace : WordTrace (prefixWord ++ tailWord_195114) baseStart_195114 baseEnd_195114 := by
    simpa [prefixWord, tailWord_195114, baseEnd_195114] using wordTrace_append hprefix tailTrace_195114
  have hstable : (prefixWord ++ tailWord_195114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195114).length < 2 ^ (prefixWord ++ tailWord_195114).sum := by decide
  have hdescent : baseEnd_195114 < baseStart_195114 := by decide
  rcases family_descends (prefixWord ++ tailWord_195114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195157 : List Nat := [1, 3, 2, 2, 1, 1, 2, 1, 1, 4, 5]
def baseStart_195157 : Nat := 118140960795 + 195157 * 2 ^ 59
def prefixEnd_195157 : Nat := 4983230072969 + 3 ^ 40 * 195157 * 2
def baseEnd_195157 : Nat := 100209344089598181039995

theorem tailTrace_195157 : CollatzResearch.WordTrace tailWord_195157 prefixEnd_195157 100209344089598181039995 := by
  unfold tailWord_195157
  simp only [CollatzResearch.WordTrace]
  refine ⟨7117960553986994007159725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4745307035991329338106483 7117960553986994007159725)
  ·
    refine ⟨2669235207745122752684897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7117960553986994007159725 2669235207745122752684897)
    ·
      refine ⟨2001926405808842064513673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2669235207745122752684897 2001926405808842064513673)
      ·
        refine ⟨1501444804356631548385255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2001926405808842064513673 1501444804356631548385255)
        ·
          refine ⟨2252167206534947322577883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1501444804356631548385255 2252167206534947322577883)
          ·
            refine ⟨3378250809802420983866825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2252167206534947322577883 3378250809802420983866825)
            ·
              refine ⟨2533688107351815737900119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3378250809802420983866825 2533688107351815737900119)
              ·
                refine ⟨3800532161027723606850179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2533688107351815737900119 3800532161027723606850179)
                ·
                  refine ⟨5700798241541585410275269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3800532161027723606850179 5700798241541585410275269)
                  ·
                    refine ⟨1068899670289047264426613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5700798241541585410275269 1068899670289047264426613)
                    ·
                      refine ⟨100209344089598181039995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1068899670289047264426613 100209344089598181039995)
                      ·
                        rfl

theorem cell23_195157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 1, 1, 4, 5].length) (baseStart_195157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_195157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_195157 prefixEnd_195157 := by exact prefixLift 195157
  have htrace : WordTrace (prefixWord ++ tailWord_195157) baseStart_195157 baseEnd_195157 := by
    simpa [prefixWord, tailWord_195157, baseEnd_195157] using wordTrace_append hprefix tailTrace_195157
  have hstable : (prefixWord ++ tailWord_195157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195157).length < 2 ^ (prefixWord ++ tailWord_195157).sum := by decide
  have hdescent : baseEnd_195157 < baseStart_195157 := by decide
  rcases family_descends (prefixWord ++ tailWord_195157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195167 : List Nat := [1, 1, 2, 3, 1, 1, 1, 2, 4, 3, 4]
def baseStart_195167 : Nat := 118140960795 + 195167 * 2 ^ 59
def prefixEnd_195167 : Nat := 4983230072969 + 3 ^ 40 * 195167 * 2
def baseEnd_195167 : Nat := 100214478896143141914949

theorem tailTrace_195167 : CollatzResearch.WordTrace tailWord_195167 prefixEnd_195167 100214478896143141914949 := by
  unfold tailWord_195167
  simp only [CollatzResearch.WordTrace]
  refine ⟨7118325283950765715023755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4745550189300510476682503 7118325283950765715023755)
  ·
    refine ⟨10677487925926148572535633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7118325283950765715023755 10677487925926148572535633)
    ·
      refine ⟨8008115944444611429401725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10677487925926148572535633 8008115944444611429401725)
      ·
        refine ⟨3003043479166729286025647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8008115944444611429401725 3003043479166729286025647)
        ·
          refine ⟨4504565218750093929038471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3003043479166729286025647 4504565218750093929038471)
          ·
            refine ⟨6756847828125140893557707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4504565218750093929038471 6756847828125140893557707)
            ·
              refine ⟨10135271742187711340336561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6756847828125140893557707 10135271742187711340336561)
              ·
                refine ⟨7601453806640783505252421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10135271742187711340336561 7601453806640783505252421)
                ·
                  refine ⟨1425272588745146907234829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7601453806640783505252421 1425272588745146907234829)
                  ·
                    refine ⟨534477220779430090213061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1425272588745146907234829 534477220779430090213061)
                    ·
                      refine ⟨100214478896143141914949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 534477220779430090213061 100214478896143141914949)
                      ·
                        rfl

theorem cell23_195167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 4, 3, 4].length) (baseStart_195167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_195167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_195167 prefixEnd_195167 := by exact prefixLift 195167
  have htrace : WordTrace (prefixWord ++ tailWord_195167) baseStart_195167 baseEnd_195167 := by
    simpa [prefixWord, tailWord_195167, baseEnd_195167] using wordTrace_append hprefix tailTrace_195167
  have hstable : (prefixWord ++ tailWord_195167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195167).length < 2 ^ (prefixWord ++ tailWord_195167).sum := by decide
  have hdescent : baseEnd_195167 < baseStart_195167 := by decide
  rcases family_descends (prefixWord ++ tailWord_195167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195177 : List Nat := [1, 2, 1, 1, 1, 4, 1, 4, 2, 6]
def baseStart_195177 : Nat := 118140960795 + 195177 * 2 ^ 59
def prefixEnd_195177 : Nat := 4983230072969 + 3 ^ 40 * 195177 * 2
def baseEnd_195177 : Nat := 33406537900896034263301

theorem tailTrace_195177 : CollatzResearch.WordTrace tailWord_195177 prefixEnd_195177 33406537900896034263301 := by
  unfold tailWord_195177
  simp only [CollatzResearch.WordTrace]
  refine ⟨7118690013914537422887785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4745793342609691615258523 7118690013914537422887785)
  ·
    refine ⟨5339017510435903067165839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7118690013914537422887785 5339017510435903067165839)
    ·
      refine ⟨8008526265653854600748759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5339017510435903067165839 8008526265653854600748759)
      ·
        refine ⟨12012789398480781901123139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8008526265653854600748759 12012789398480781901123139)
        ·
          refine ⟨18019184097721172851684709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12012789398480781901123139 18019184097721172851684709)
          ·
            refine ⟨3378597018322719909690883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18019184097721172851684709 3378597018322719909690883)
            ·
              refine ⟨5067895527484079864536325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3378597018322719909690883 5067895527484079864536325)
              ·
                refine ⟨950230411403264974600561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5067895527484079864536325 950230411403264974600561)
                ·
                  refine ⟨712672808552448730950421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 950230411403264974600561 712672808552448730950421)
                  ·
                    refine ⟨33406537900896034263301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 712672808552448730950421 33406537900896034263301)
                    ·
                      rfl

theorem cell23_195177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 4, 2, 6].length) (baseStart_195177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_195177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_195177 prefixEnd_195177 := by exact prefixLift 195177
  have htrace : WordTrace (prefixWord ++ tailWord_195177) baseStart_195177 baseEnd_195177 := by
    simpa [prefixWord, tailWord_195177, baseEnd_195177] using wordTrace_append hprefix tailTrace_195177
  have hstable : (prefixWord ++ tailWord_195177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195177).length < 2 ^ (prefixWord ++ tailWord_195177).sum := by decide
  have hdescent : baseEnd_195177 < baseStart_195177 := by decide
  rcases family_descends (prefixWord ++ tailWord_195177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195178 : List Nat := [3, 1, 3, 2, 1, 1, 4, 2, 2, 1, 3]
def baseStart_195178 : Nat := 118140960795 + 195178 * 2 ^ 59
def prefixEnd_195178 : Nat := 4983230072969 + 3 ^ 40 * 195178 * 2
def baseEnd_195178 : Nat := 100220127183342598877399

theorem tailTrace_195178 : CollatzResearch.WordTrace tailWord_195178 prefixEnd_195178 100220127183342598877399 := by
  unfold tailWord_195178
  simp only [CollatzResearch.WordTrace]
  refine ⟨1779681621727728648418547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4745817657940609729116125 1779681621727728648418547)
  ·
    refine ⟨2669522432591592972627821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1779681621727728648418547 2669522432591592972627821)
    ·
      refine ⟨1001070912221847364735433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2669522432591592972627821 1001070912221847364735433)
      ·
        refine ⟨750803184166385523551575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1001070912221847364735433 750803184166385523551575)
        ·
          refine ⟨1126204776249578285327363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 750803184166385523551575 1126204776249578285327363)
          ·
            refine ⟨1689307164374367427991045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1126204776249578285327363 1689307164374367427991045)
            ·
              refine ⟨316745093320193892748321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1689307164374367427991045 316745093320193892748321)
              ·
                refine ⟨237558819990145419561241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 316745093320193892748321 237558819990145419561241)
                ·
                  refine ⟨178169114992609064670931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 237558819990145419561241 178169114992609064670931)
                  ·
                    refine ⟨267253672488913597006397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 178169114992609064670931 267253672488913597006397)
                    ·
                      refine ⟨100220127183342598877399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 267253672488913597006397 100220127183342598877399)
                      ·
                        rfl

theorem cell23_195178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 4, 2, 2, 1, 3].length) (baseStart_195178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_195178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_195178 prefixEnd_195178 := by exact prefixLift 195178
  have htrace : WordTrace (prefixWord ++ tailWord_195178) baseStart_195178 baseEnd_195178 := by
    simpa [prefixWord, tailWord_195178, baseEnd_195178] using wordTrace_append hprefix tailTrace_195178
  have hstable : (prefixWord ++ tailWord_195178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195178).length < 2 ^ (prefixWord ++ tailWord_195178).sum := by decide
  have hdescent : baseEnd_195178 < baseStart_195178 := by decide
  rcases family_descends (prefixWord ++ tailWord_195178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195187 : List Nat := [1, 1, 1, 2, 2, 1, 1, 4, 4, 1, 5]
def baseStart_195187 : Nat := 118140960795 + 195187 * 2 ^ 59
def prefixEnd_195187 : Nat := 4983230072969 + 3 ^ 40 * 195187 * 2
def baseEnd_195187 : Nat := 100224748509233063664857

theorem tailTrace_195187 : CollatzResearch.WordTrace tailWord_195187 prefixEnd_195187 100224748509233063664857 := by
  unfold tailWord_195187
  simp only [CollatzResearch.WordTrace]
  refine ⟨7119054743878309130751815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4746036495918872753834543 7119054743878309130751815)
  ·
    refine ⟨10678582115817463696127723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7119054743878309130751815 10678582115817463696127723)
    ·
      refine ⟨16017873173726195544191585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10678582115817463696127723 16017873173726195544191585)
      ·
        refine ⟨12013404880294646658143689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16017873173726195544191585 12013404880294646658143689)
        ·
          refine ⟨9010053660220984993607767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12013404880294646658143689 9010053660220984993607767)
          ·
            refine ⟨13515080490331477490411651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9010053660220984993607767 13515080490331477490411651)
            ·
              refine ⟨20272620735497216235617477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13515080490331477490411651 20272620735497216235617477)
              ·
                refine ⟨3801116387905728044178277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20272620735497216235617477 3801116387905728044178277)
                ·
                  refine ⟨712709322732324008283427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3801116387905728044178277 712709322732324008283427)
                  ·
                    refine ⟨1069063984098486012425141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 712709322732324008283427 1069063984098486012425141)
                    ·
                      refine ⟨100224748509233063664857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1069063984098486012425141 100224748509233063664857)
                      ·
                        rfl

theorem cell23_195187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 4, 4, 1, 5].length) (baseStart_195187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_195187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_195187 prefixEnd_195187 := by exact prefixLift 195187
  have htrace : WordTrace (prefixWord ++ tailWord_195187) baseStart_195187 baseEnd_195187 := by
    simpa [prefixWord, tailWord_195187, baseEnd_195187] using wordTrace_append hprefix tailTrace_195187
  have hstable : (prefixWord ++ tailWord_195187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195187).length < 2 ^ (prefixWord ++ tailWord_195187).sum := by decide
  have hdescent : baseEnd_195187 < baseStart_195187 := by decide
  rcases family_descends (prefixWord ++ tailWord_195187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195214 : List Nat := [4, 1, 1, 3, 1, 1, 1, 2, 1, 4, 4]
def baseStart_195214 : Nat := 118140960795 + 195214 * 2 ^ 59
def prefixEnd_195214 : Nat := 4983230072969 + 3 ^ 40 * 195214 * 2
def baseEnd_195214 : Nat := 100238612486904458027233

theorem tailTrace_195214 : CollatzResearch.WordTrace tailWord_195214 prefixEnd_195214 100238612486904458027233 := by
  unfold tailWord_195214
  simp only [CollatzResearch.WordTrace]
  refine ⟨890004939347561592748087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4746693009853661827989797 890004939347561592748087)
  ·
    refine ⟨1335007409021342389122131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 890004939347561592748087 1335007409021342389122131)
    ·
      refine ⟨2002511113532013583683197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1335007409021342389122131 2002511113532013583683197)
      ·
        refine ⟨750941667574505093881199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2002511113532013583683197 750941667574505093881199)
        ·
          refine ⟨1126412501361757640821799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 750941667574505093881199 1126412501361757640821799)
          ·
            refine ⟨1689618752042636461232699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1126412501361757640821799 1689618752042636461232699)
            ·
              refine ⟨2534428128063954691849049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1689618752042636461232699 2534428128063954691849049)
              ·
                refine ⟨1900821096047966018886787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2534428128063954691849049 1900821096047966018886787)
                ·
                  refine ⟨2851231644071949028330181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1900821096047966018886787 2851231644071949028330181)
                  ·
                    refine ⟨534605933263490442811909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2851231644071949028330181 534605933263490442811909)
                    ·
                      refine ⟨100238612486904458027233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 534605933263490442811909 100238612486904458027233)
                      ·
                        rfl

theorem cell23_195214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_195214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_195214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_195214 prefixEnd_195214 := by exact prefixLift 195214
  have htrace : WordTrace (prefixWord ++ tailWord_195214) baseStart_195214 baseEnd_195214 := by
    simpa [prefixWord, tailWord_195214, baseEnd_195214] using wordTrace_append hprefix tailTrace_195214
  have hstable : (prefixWord ++ tailWord_195214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195214).length < 2 ^ (prefixWord ++ tailWord_195214).sum := by decide
  have hdescent : baseEnd_195214 < baseStart_195214 := by decide
  rcases family_descends (prefixWord ++ tailWord_195214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195218 : List Nat := [3, 2, 3, 1, 2, 1, 2, 2, 1, 4, 2]
def baseStart_195218 : Nat := 118140960795 + 195218 * 2 ^ 59
def prefixEnd_195218 : Nat := 4983230072969 + 3 ^ 40 * 195218 * 2
def baseEnd_195218 : Nat := 100240666409522442377215

theorem tailTrace_195218 : CollatzResearch.WordTrace tailWord_195218 prefixEnd_195218 100240666409522442377215 := by
  unfold tailWord_195218
  simp only [CollatzResearch.WordTrace]
  refine ⟨1780046351691500356282577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4746790271177334283420205 1780046351691500356282577)
  ·
    refine ⟨1335034763768625267211933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1780046351691500356282577 1335034763768625267211933)
    ·
      refine ⟨500638036413234475204475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1335034763768625267211933 500638036413234475204475)
      ·
        refine ⟨750957054619851712806713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 500638036413234475204475 750957054619851712806713)
        ·
          refine ⟨563217790964888784605035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 750957054619851712806713 563217790964888784605035)
          ·
            refine ⟨844826686447333176907553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 563217790964888784605035 844826686447333176907553)
            ·
              refine ⟨633620014835499882680665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 844826686447333176907553 633620014835499882680665)
              ·
                refine ⟨475215011126624912010499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 633620014835499882680665 475215011126624912010499)
                ·
                  refine ⟨712822516689937368015749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 475215011126624912010499 712822516689937368015749)
                  ·
                    refine ⟨133654221879363256502953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 712822516689937368015749 133654221879363256502953)
                    ·
                      refine ⟨100240666409522442377215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 133654221879363256502953 100240666409522442377215)
                      ·
                        rfl

theorem cell23_195218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 2, 1, 4, 2].length) (baseStart_195218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_195218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_195218 prefixEnd_195218 := by exact prefixLift 195218
  have htrace : WordTrace (prefixWord ++ tailWord_195218) baseStart_195218 baseEnd_195218 := by
    simpa [prefixWord, tailWord_195218, baseEnd_195218] using wordTrace_append hprefix tailTrace_195218
  have hstable : (prefixWord ++ tailWord_195218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195218).length < 2 ^ (prefixWord ++ tailWord_195218).sum := by decide
  have hdescent : baseEnd_195218 < baseStart_195218 := by decide
  rcases family_descends (prefixWord ++ tailWord_195218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195368 : List Nat := [2, 1, 5, 1, 1, 1, 2, 2, 1, 5, 2]
def baseStart_195368 : Nat := 118140960795 + 195368 * 2 ^ 59
def prefixEnd_195368 : Nat := 4983230072969 + 3 ^ 40 * 195368 * 2
def baseEnd_195368 : Nat := 100317688507696855501525

theorem tailTrace_195368 : CollatzResearch.WordTrace tailWord_195368 prefixEnd_195368 100317688507696855501525 := by
  unfold tailWord_195368
  simp only [CollatzResearch.WordTrace]
  refine ⟨3562828178111288521545379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4750437570815051362060505 3562828178111288521545379)
  ·
    refine ⟨5344242267166932782318069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3562828178111288521545379 5344242267166932782318069)
    ·
      refine ⟨501022712546899948342319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5344242267166932782318069 501022712546899948342319)
      ·
        refine ⟨751534068820349922513479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 501022712546899948342319 751534068820349922513479)
        ·
          refine ⟨1127301103230524883770219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 751534068820349922513479 1127301103230524883770219)
          ·
            refine ⟨1690951654845787325655329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1127301103230524883770219 1690951654845787325655329)
            ·
              refine ⟨1268213741134340494241497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1690951654845787325655329 1268213741134340494241497)
              ·
                refine ⟨951160305850755370681123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1268213741134340494241497 951160305850755370681123)
                ·
                  refine ⟨1426740458776133056021685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 951160305850755370681123 1426740458776133056021685)
                  ·
                    refine ⟨133756918010262474002033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1426740458776133056021685 133756918010262474002033)
                    ·
                      refine ⟨100317688507696855501525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 133756918010262474002033 100317688507696855501525)
                      ·
                        rfl

theorem cell23_195368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 2, 1, 5, 2].length) (baseStart_195368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_195368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_195368 prefixEnd_195368 := by exact prefixLift 195368
  have htrace : WordTrace (prefixWord ++ tailWord_195368) baseStart_195368 baseEnd_195368 := by
    simpa [prefixWord, tailWord_195368, baseEnd_195368] using wordTrace_append hprefix tailTrace_195368
  have hstable : (prefixWord ++ tailWord_195368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195368).length < 2 ^ (prefixWord ++ tailWord_195368).sum := by decide
  have hdescent : baseEnd_195368 < baseStart_195368 := by decide
  rcases family_descends (prefixWord ++ tailWord_195368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195391 : List Nat := [1, 1, 2, 2, 5, 1, 2, 2, 1, 6]
def baseStart_195391 : Nat := 118140960795 + 195391 * 2 ^ 59
def prefixEnd_195391 : Nat := 4983230072969 + 3 ^ 40 * 195391 * 2
def baseEnd_195391 : Nat := 33443166187583421837973

theorem tailTrace_195391 : CollatzResearch.WordTrace tailWord_195391 prefixEnd_195391 33443166187583421837973 := by
  unfold tailWord_195391
  simp only [CollatzResearch.WordTrace]
  refine ⟨7126495235139251971178027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4750996823426167980785351 7126495235139251971178027)
  ·
    refine ⟨10689742852708877956767041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7126495235139251971178027 10689742852708877956767041)
    ·
      refine ⟨8017307139531658467575281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10689742852708877956767041 8017307139531658467575281)
      ·
        refine ⟨6012980354648743850681461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8017307139531658467575281 6012980354648743850681461)
        ·
          refine ⟨563716908248319736001387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6012980354648743850681461 563716908248319736001387)
          ·
            refine ⟨845575362372479604002081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 563716908248319736001387 845575362372479604002081)
            ·
              refine ⟨634181521779359703001561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 845575362372479604002081 634181521779359703001561)
              ·
                refine ⟨475636141334519777251171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 634181521779359703001561 475636141334519777251171)
                ·
                  refine ⟨713454212001779665876757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 475636141334519777251171 713454212001779665876757)
                  ·
                    refine ⟨33443166187583421837973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 713454212001779665876757 33443166187583421837973)
                    ·
                      rfl

theorem cell23_195391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 2, 1, 6].length) (baseStart_195391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_195391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_195391 prefixEnd_195391 := by exact prefixLift 195391
  have htrace : WordTrace (prefixWord ++ tailWord_195391) baseStart_195391 baseEnd_195391 := by
    simpa [prefixWord, tailWord_195391, baseEnd_195391] using wordTrace_append hprefix tailTrace_195391
  have hstable : (prefixWord ++ tailWord_195391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195391).length < 2 ^ (prefixWord ++ tailWord_195391).sum := by decide
  have hdescent : baseEnd_195391 < baseStart_195391 := by decide
  rcases family_descends (prefixWord ++ tailWord_195391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195408 : List Nat := [2, 1, 1, 1, 1, 4, 5, 2, 2, 4]
def baseStart_195408 : Nat := 118140960795 + 195408 * 2 ^ 59
def prefixEnd_195408 : Nat := 4983230072969 + 3 ^ 40 * 195408 * 2
def baseEnd_195408 : Nat := 33446075911292233000447

theorem tailTrace_195408 : CollatzResearch.WordTrace tailWord_195408 prefixEnd_195408 33446075911292233000447 := by
  unfold tailWord_195408
  simp only [CollatzResearch.WordTrace]
  refine ⟨3563557638038831937273439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4751410184051775916364585 3563557638038831937273439)
  ·
    refine ⟨5345336457058247905910159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3563557638038831937273439 5345336457058247905910159)
    ·
      refine ⟨8018004685587371858865239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5345336457058247905910159 8018004685587371858865239)
      ·
        refine ⟨12027007028381057788297859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8018004685587371858865239 12027007028381057788297859)
        ·
          refine ⟨18040510542571586682446789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12027007028381057788297859 18040510542571586682446789)
          ·
            refine ⟨3382595726732172502958773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18040510542571586682446789 3382595726732172502958773)
            ·
              refine ⟨317118349381141172152385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3382595726732172502958773 317118349381141172152385)
              ·
                refine ⟨237838762035855879114289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 317118349381141172152385 237838762035855879114289)
                ·
                  refine ⟨178379071526891909335717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 237838762035855879114289 178379071526891909335717)
                  ·
                    refine ⟨33446075911292233000447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 178379071526891909335717 33446075911292233000447)
                    ·
                      rfl

theorem cell23_195408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 5, 2, 2, 4].length) (baseStart_195408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_195408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_195408 prefixEnd_195408 := by exact prefixLift 195408
  have htrace : WordTrace (prefixWord ++ tailWord_195408) baseStart_195408 baseEnd_195408 := by
    simpa [prefixWord, tailWord_195408, baseEnd_195408] using wordTrace_append hprefix tailTrace_195408
  have hstable : (prefixWord ++ tailWord_195408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195408).length < 2 ^ (prefixWord ++ tailWord_195408).sum := by decide
  have hdescent : baseEnd_195408 < baseStart_195408 := by decide
  rcases family_descends (prefixWord ++ tailWord_195408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195415 : List Nat := [1, 1, 3, 2, 4, 1, 1, 3, 3, 2, 2]
def baseStart_195415 : Nat := 118140960795 + 195415 * 2 ^ 59
def prefixEnd_195415 : Nat := 4983230072969 + 3 ^ 40 * 195415 * 2
def baseEnd_195415 : Nat := 100341822098458171613809

theorem tailTrace_195415 : CollatzResearch.WordTrace tailWord_195415 prefixEnd_195415 100341822098458171613809 := by
  unfold tailWord_195415
  simp only [CollatzResearch.WordTrace]
  refine ⟨7127370587052304070051699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4751580391368202713367799 7127370587052304070051699)
  ·
    refine ⟨10691055880578456105077549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7127370587052304070051699 10691055880578456105077549)
    ·
      refine ⟨4009145955216921039404081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10691055880578456105077549 4009145955216921039404081)
      ·
        refine ⟨3006859466412690779553061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4009145955216921039404081 3006859466412690779553061)
        ·
          refine ⟨563786149952379521166199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3006859466412690779553061 563786149952379521166199)
          ·
            refine ⟨845679224928569281749299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 563786149952379521166199 845679224928569281749299)
            ·
              refine ⟨1268518837392853922623949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 845679224928569281749299 1268518837392853922623949)
              ·
                refine ⟨475694564022320220983981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1268518837392853922623949 475694564022320220983981)
                ·
                  refine ⟨178385461508370082868993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 475694564022320220983981 178385461508370082868993)
                  ·
                    refine ⟨133789096131277562151745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 178385461508370082868993 133789096131277562151745)
                    ·
                      refine ⟨100341822098458171613809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 133789096131277562151745 100341822098458171613809)
                      ·
                        rfl

theorem cell23_195415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 3, 3, 2, 2].length) (baseStart_195415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_195415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_195415 prefixEnd_195415 := by exact prefixLift 195415
  have htrace : WordTrace (prefixWord ++ tailWord_195415) baseStart_195415 baseEnd_195415 := by
    simpa [prefixWord, tailWord_195415, baseEnd_195415] using wordTrace_append hprefix tailTrace_195415
  have hstable : (prefixWord ++ tailWord_195415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195415).length < 2 ^ (prefixWord ++ tailWord_195415).sum := by decide
  have hdescent : baseEnd_195415 < baseStart_195415 := by decide
  rcases family_descends (prefixWord ++ tailWord_195415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195428 : List Nat := [2, 3, 1, 1, 4, 1, 3, 1, 1, 2, 4]
def baseStart_195428 : Nat := 118140960795 + 195428 * 2 ^ 59
def prefixEnd_195428 : Nat := 4983230072969 + 3 ^ 40 * 195428 * 2
def baseEnd_195428 : Nat := 100348497346966620751249

theorem tailTrace_195428 : CollatzResearch.WordTrace tailWord_195428 prefixEnd_195428 100348497346966620751249 := by
  unfold tailWord_195428
  simp only [CollatzResearch.WordTrace]
  refine ⟨3563922368002603645137469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4751896490670138193516625 3563922368002603645137469)
  ·
    refine ⟨1336470888000976366926551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3563922368002603645137469 1336470888000976366926551)
    ·
      refine ⟨2004706332001464550389827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1336470888000976366926551 2004706332001464550389827)
      ·
        refine ⟨3007059498002196825584741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2004706332001464550389827 3007059498002196825584741)
        ·
          refine ⟨563823655875411904797139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3007059498002196825584741 563823655875411904797139)
          ·
            refine ⟨845735483813117857195709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 563823655875411904797139 845735483813117857195709)
            ·
              refine ⟨317150806429919196448391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 845735483813117857195709 317150806429919196448391)
              ·
                refine ⟨475726209644878794672587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 317150806429919196448391 475726209644878794672587)
                ·
                  refine ⟨713589314467318192008881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 475726209644878794672587 713589314467318192008881)
                  ·
                    refine ⟨535191985850488644006661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 713589314467318192008881 535191985850488644006661)
                    ·
                      refine ⟨100348497346966620751249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 535191985850488644006661 100348497346966620751249)
                      ·
                        rfl

theorem cell23_195428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 3, 1, 1, 2, 4].length) (baseStart_195428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_195428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_195428 prefixEnd_195428 := by exact prefixLift 195428
  have htrace : WordTrace (prefixWord ++ tailWord_195428) baseStart_195428 baseEnd_195428 := by
    simpa [prefixWord, tailWord_195428, baseEnd_195428] using wordTrace_append hprefix tailTrace_195428
  have hstable : (prefixWord ++ tailWord_195428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195428).length < 2 ^ (prefixWord ++ tailWord_195428).sum := by decide
  have hdescent : baseEnd_195428 < baseStart_195428 := by decide
  rcases family_descends (prefixWord ++ tailWord_195428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195438 : List Nat := [4, 1, 2, 3, 2, 1, 1, 9]
def baseStart_195438 : Nat := 118140960795 + 195438 * 2 ^ 59
def prefixEnd_195438 : Nat := 4983230072969 + 3 ^ 40 * 195438 * 2
def baseEnd_195438 : Nat := 3716801190870799319489

theorem tailTrace_195438 : CollatzResearch.WordTrace tailWord_195438 prefixEnd_195438 3716801190870799319489 := by
  unfold tailWord_195438
  simp only [CollatzResearch.WordTrace]
  refine ⟨891026183246122374767371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4752139643979319332092645 891026183246122374767371)
  ·
    refine ⟨1336539274869183562151057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 891026183246122374767371 1336539274869183562151057)
    ·
      refine ⟨1002404456151887671613293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1336539274869183562151057 1002404456151887671613293)
      ·
        refine ⟨375901671056957876854985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1002404456151887671613293 375901671056957876854985)
        ·
          refine ⟨281926253292718407641239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 375901671056957876854985 281926253292718407641239)
          ·
            refine ⟨422889379939077611461859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 281926253292718407641239 422889379939077611461859)
            ·
              refine ⟨634334069908616417192789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 422889379939077611461859 634334069908616417192789)
              ·
                refine ⟨3716801190870799319489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 634334069908616417192789 3716801190870799319489)
                ·
                  rfl

theorem cell23_195438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 9].length) (baseStart_195438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_195438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_195438 prefixEnd_195438 := by exact prefixLift 195438
  have htrace : WordTrace (prefixWord ++ tailWord_195438) baseStart_195438 baseEnd_195438 := by
    simpa [prefixWord, tailWord_195438, baseEnd_195438] using wordTrace_append hprefix tailTrace_195438
  have hstable : (prefixWord ++ tailWord_195438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195438).length < 2 ^ (prefixWord ++ tailWord_195438).sum := by decide
  have hdescent : baseEnd_195438 < baseStart_195438 := by decide
  rcases family_descends (prefixWord ++ tailWord_195438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195449 : List Nat := [1, 2, 1, 3, 2, 5, 1, 3, 1, 2, 2]
def baseStart_195449 : Nat := 118140960795 + 195449 * 2 ^ 59
def prefixEnd_195449 : Nat := 4983230072969 + 3 ^ 40 * 195449 * 2
def baseEnd_195449 : Nat := 100359280440711038588653

theorem tailTrace_195449 : CollatzResearch.WordTrace tailWord_195449 prefixEnd_195449 100359280440711038588653 := by
  unfold tailWord_195449
  simp only [CollatzResearch.WordTrace]
  refine ⟨7128610668929127876789401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4752407112619418584526267 7128610668929127876789401)
  ·
    refine ⟨5346458001696845907592051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7128610668929127876789401 5346458001696845907592051)
    ·
      refine ⟨8019687002545268861388077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5346458001696845907592051 8019687002545268861388077)
      ·
        refine ⟨3007382625954475823020529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8019687002545268861388077 3007382625954475823020529)
        ·
          refine ⟨2255536969465856867265397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3007382625954475823020529 2255536969465856867265397)
          ·
            refine ⟨211456590887424081306131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2255536969465856867265397 211456590887424081306131)
            ·
              refine ⟨317184886331136121959197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 211456590887424081306131 317184886331136121959197)
              ·
                refine ⟨118944332374176045734699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 317184886331136121959197 118944332374176045734699)
                ·
                  refine ⟨178416498561264068602049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 118944332374176045734699 178416498561264068602049)
                  ·
                    refine ⟨133812373920948051451537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 178416498561264068602049 133812373920948051451537)
                    ·
                      refine ⟨100359280440711038588653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 133812373920948051451537 100359280440711038588653)
                      ·
                        rfl

theorem cell23_195449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 1, 3, 1, 2, 2].length) (baseStart_195449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_195449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_195449 prefixEnd_195449 := by exact prefixLift 195449
  have htrace : WordTrace (prefixWord ++ tailWord_195449) baseStart_195449 baseEnd_195449 := by
    simpa [prefixWord, tailWord_195449, baseEnd_195449] using wordTrace_append hprefix tailTrace_195449
  have hstable : (prefixWord ++ tailWord_195449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195449).length < 2 ^ (prefixWord ++ tailWord_195449).sum := by decide
  have hdescent : baseEnd_195449 < baseStart_195449 := by decide
  rcases family_descends (prefixWord ++ tailWord_195449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195466 : List Nat := [3, 1, 2, 4, 1, 2, 3, 2, 1, 2, 2]
def baseStart_195466 : Nat := 118140960795 + 195466 * 2 ^ 59
def prefixEnd_195466 : Nat := 4983230072969 + 3 ^ 40 * 195466 * 2
def baseEnd_195466 : Nat := 100368009611837472076075

theorem tailTrace_195466 : CollatzResearch.WordTrace tailWord_195466 prefixEnd_195466 100368009611837472076075 := by
  unfold tailWord_195466
  simp only [CollatzResearch.WordTrace]
  refine ⟨1782307677466884945039563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4752820473245026520105501 1782307677466884945039563)
  ·
    refine ⟨2673461516200327417559345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1782307677466884945039563 2673461516200327417559345)
    ·
      refine ⟨2005096137150245563169509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2673461516200327417559345 2005096137150245563169509)
      ·
        refine ⟨375955525715671043094283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2005096137150245563169509 375955525715671043094283)
        ·
          refine ⟨563933288573506564641425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 375955525715671043094283 563933288573506564641425)
          ·
            refine ⟨422949966430129923481069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 563933288573506564641425 422949966430129923481069)
            ·
              refine ⟨158606237411298721305401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 422949966430129923481069 158606237411298721305401)
              ·
                refine ⟨118954678058474040979051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 158606237411298721305401 118954678058474040979051)
                ·
                  refine ⟨178432017087711061468577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 118954678058474040979051 178432017087711061468577)
                  ·
                    refine ⟨133824012815783296101433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 178432017087711061468577 133824012815783296101433)
                    ·
                      refine ⟨100368009611837472076075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 133824012815783296101433 100368009611837472076075)
                      ·
                        rfl

theorem cell23_195466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 3, 2, 1, 2, 2].length) (baseStart_195466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_195466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_195466 prefixEnd_195466 := by exact prefixLift 195466
  have htrace : WordTrace (prefixWord ++ tailWord_195466) baseStart_195466 baseEnd_195466 := by
    simpa [prefixWord, tailWord_195466, baseEnd_195466] using wordTrace_append hprefix tailTrace_195466
  have hstable : (prefixWord ++ tailWord_195466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195466).length < 2 ^ (prefixWord ++ tailWord_195466).sum := by decide
  have hdescent : baseEnd_195466 < baseStart_195466 := by decide
  rcases family_descends (prefixWord ++ tailWord_195466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195482 : List Nat := [3, 1, 1, 4, 3, 1, 1, 3, 2, 1, 3]
def baseStart_195482 : Nat := 118140960795 + 195482 * 2 ^ 59
def prefixEnd_195482 : Nat := 4983230072969 + 3 ^ 40 * 195482 * 2
def baseEnd_195482 : Nat := 100376225302309409476001

theorem tailTrace_195482 : CollatzResearch.WordTrace tailWord_195482 prefixEnd_195482 100376225302309409476001 := by
  unfold tailWord_195482
  simp only [CollatzResearch.WordTrace]
  refine ⟨1782453569452393628185175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4753209518539716341827133 1782453569452393628185175)
  ·
    refine ⟨2673680354178590442277763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1782453569452393628185175 2673680354178590442277763)
    ·
      refine ⟨4010520531267885663416645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2673680354178590442277763 4010520531267885663416645)
      ·
        refine ⟨751972599612728561890621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4010520531267885663416645 751972599612728561890621)
        ·
          refine ⟨281989724854773210708983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 751972599612728561890621 281989724854773210708983)
          ·
            refine ⟨422984587282159816063475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 281989724854773210708983 422984587282159816063475)
            ·
              refine ⟨634476880923239724095213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 422984587282159816063475 634476880923239724095213)
              ·
                refine ⟨237928830346214896535705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 634476880923239724095213 237928830346214896535705)
                ·
                  refine ⟨178446622759661172401779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 237928830346214896535705 178446622759661172401779)
                  ·
                    refine ⟨267669934139491758602669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 178446622759661172401779 267669934139491758602669)
                    ·
                      refine ⟨100376225302309409476001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 267669934139491758602669 100376225302309409476001)
                      ·
                        rfl

theorem cell23_195482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 3, 2, 1, 3].length) (baseStart_195482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_195482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_195482 prefixEnd_195482 := by exact prefixLift 195482
  have htrace : WordTrace (prefixWord ++ tailWord_195482) baseStart_195482 baseEnd_195482 := by
    simpa [prefixWord, tailWord_195482, baseEnd_195482] using wordTrace_append hprefix tailTrace_195482
  have hstable : (prefixWord ++ tailWord_195482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195482).length < 2 ^ (prefixWord ++ tailWord_195482).sum := by decide
  have hdescent : baseEnd_195482 < baseStart_195482 := by decide
  rcases family_descends (prefixWord ++ tailWord_195482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195491 : List Nat := [1, 1, 1, 4, 1, 2, 3, 2, 2, 1, 5]
def baseStart_195491 : Nat := 118140960795 + 195491 * 2 ^ 59
def prefixEnd_195491 : Nat := 4983230072969 + 3 ^ 40 * 195491 * 2
def baseEnd_195491 : Nat := 100380846628199874263459

theorem tailTrace_195491 : CollatzResearch.WordTrace tailWord_195491 prefixEnd_195491 100380846628199874263459 := by
  unfold tailWord_195491
  simp only [CollatzResearch.WordTrace]
  refine ⟨7130142534776969049818327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4753428356517979366545551 7130142534776969049818327)
  ·
    refine ⟨10695213802165453574727491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7130142534776969049818327 10695213802165453574727491)
    ·
      refine ⟨16042820703248180362091237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10695213802165453574727491 16042820703248180362091237)
      ·
        refine ⟨3008028881859033817892107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16042820703248180362091237 3008028881859033817892107)
        ·
          refine ⟨4512043322788550726838161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3008028881859033817892107 4512043322788550726838161)
          ·
            refine ⟨3384032492091413045128621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4512043322788550726838161 3384032492091413045128621)
            ·
              refine ⟨1269012184534279891923233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3384032492091413045128621 1269012184534279891923233)
              ·
                refine ⟨951759138400709918942425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1269012184534279891923233 951759138400709918942425)
                ·
                  refine ⟨713819353800532439206819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 951759138400709918942425 713819353800532439206819)
                  ·
                    refine ⟨1070729030700798658810229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 713819353800532439206819 1070729030700798658810229)
                    ·
                      refine ⟨100380846628199874263459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 1070729030700798658810229 100380846628199874263459)
                      ·
                        rfl

theorem cell23_195491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 2, 2, 1, 5].length) (baseStart_195491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_195491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_195491 prefixEnd_195491 := by exact prefixLift 195491
  have htrace : WordTrace (prefixWord ++ tailWord_195491) baseStart_195491 baseEnd_195491 := by
    simpa [prefixWord, tailWord_195491, baseEnd_195491] using wordTrace_append hprefix tailTrace_195491
  have hstable : (prefixWord ++ tailWord_195491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195491).length < 2 ^ (prefixWord ++ tailWord_195491).sum := by decide
  have hdescent : baseEnd_195491 < baseStart_195491 := by decide
  rcases family_descends (prefixWord ++ tailWord_195491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195518 : List Nat := [4, 2, 1, 1, 1, 2, 2, 2, 2, 2, 4]
def baseStart_195518 : Nat := 118140960795 + 195518 * 2 ^ 59
def prefixEnd_195518 : Nat := 4983230072969 + 3 ^ 40 * 195518 * 2
def baseEnd_195518 : Nat := 100394710605871268625835

theorem tailTrace_195518 : CollatzResearch.WordTrace tailWord_195518 prefixEnd_195518 100394710605871268625835 := by
  unfold tailWord_195518
  simp only [CollatzResearch.WordTrace]
  refine ⟨891390913209894082631401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4754084870452768440700805 891390913209894082631401)
  ·
    refine ⟨668543184907420561973551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 891390913209894082631401 668543184907420561973551)
    ·
      refine ⟨1002814777361130842960327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 668543184907420561973551 1002814777361130842960327)
      ·
        refine ⟨1504222166041696264440491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1002814777361130842960327 1504222166041696264440491)
        ·
          refine ⟨2256333249062544396660737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1504222166041696264440491 2256333249062544396660737)
          ·
            refine ⟨1692249936796908297495553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2256333249062544396660737 1692249936796908297495553)
            ·
              refine ⟨1269187452597681223121665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1692249936796908297495553 1269187452597681223121665)
              ·
                refine ⟨951890589448260917341249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1269187452597681223121665 951890589448260917341249)
                ·
                  refine ⟨713917942086195688005937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 951890589448260917341249 713917942086195688005937)
                  ·
                    refine ⟨535438456564646766004453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 713917942086195688005937 535438456564646766004453)
                    ·
                      refine ⟨100394710605871268625835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 535438456564646766004453 100394710605871268625835)
                      ·
                        rfl

theorem cell23_195518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 2, 2, 2, 4].length) (baseStart_195518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_195518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_195518 prefixEnd_195518 := by exact prefixLift 195518
  have htrace : WordTrace (prefixWord ++ tailWord_195518) baseStart_195518 baseEnd_195518 := by
    simpa [prefixWord, tailWord_195518, baseEnd_195518] using wordTrace_append hprefix tailTrace_195518
  have hstable : (prefixWord ++ tailWord_195518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195518).length < 2 ^ (prefixWord ++ tailWord_195518).sum := by decide
  have hdescent : baseEnd_195518 < baseStart_195518 := by decide
  rcases family_descends (prefixWord ++ tailWord_195518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195573 : List Nat := [1, 3, 5, 2, 1, 2, 1, 2, 2, 2, 2]
def baseStart_195573 : Nat := 118140960795 + 195573 * 2 ^ 59
def prefixEnd_195573 : Nat := 4983230072969 + 3 ^ 40 * 195573 * 2
def baseEnd_195573 : Nat := 100422952041868553438083

theorem tailTrace_195573 : CollatzResearch.WordTrace tailWord_195573 prefixEnd_195573 100422952041868553438083 := by
  unfold tailWord_195573
  simp only [CollatzResearch.WordTrace]
  refine ⟨7133133320479897054303373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4755422213653264702868915 7133133320479897054303373)
  ·
    refine ⟨2674924995179961395363765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7133133320479897054303373 2674924995179961395363765)
    ·
      refine ⟨250774218298121380815353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2674924995179961395363765 250774218298121380815353)
      ·
        refine ⟨188080663723591035611515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 250774218298121380815353 188080663723591035611515)
        ·
          refine ⟨282120995585386553417273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 188080663723591035611515 282120995585386553417273)
          ·
            refine ⟨211590746689039915062955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 282120995585386553417273 211590746689039915062955)
            ·
              refine ⟨317386120033559872594433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 211590746689039915062955 317386120033559872594433)
              ·
                refine ⟨238039590025169904445825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 317386120033559872594433 238039590025169904445825)
                ·
                  refine ⟨178529692518877428334369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 238039590025169904445825 178529692518877428334369)
                  ·
                    refine ⟨133897269389158071250777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 178529692518877428334369 133897269389158071250777)
                    ·
                      refine ⟨100422952041868553438083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 133897269389158071250777 100422952041868553438083)
                      ·
                        rfl

theorem cell23_195573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_195573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_195573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_195573 prefixEnd_195573 := by exact prefixLift 195573
  have htrace : WordTrace (prefixWord ++ tailWord_195573) baseStart_195573 baseEnd_195573 := by
    simpa [prefixWord, tailWord_195573, baseEnd_195573] using wordTrace_append hprefix tailTrace_195573
  have hstable : (prefixWord ++ tailWord_195573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195573).length < 2 ^ (prefixWord ++ tailWord_195573).sum := by decide
  have hdescent : baseEnd_195573 < baseStart_195573 := by decide
  rcases family_descends (prefixWord ++ tailWord_195573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195578 : List Nat := [3, 1, 1, 1, 1, 2, 1, 6, 2, 1, 4]
def baseStart_195578 : Nat := 118140960795 + 195578 * 2 ^ 59
def prefixEnd_195578 : Nat := 4983230072969 + 3 ^ 40 * 195578 * 2
def baseEnd_195578 : Nat := 100425519445141033875559

theorem tailTrace_195578 : CollatzResearch.WordTrace tailWord_195578 prefixEnd_195578 100425519445141033875559 := by
  unfold tailWord_195578
  simp only [CollatzResearch.WordTrace]
  refine ⟨1783328921365445727058847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4755543790307855272156925 1783328921365445727058847)
  ·
    refine ⟨2674993382048168590588271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1783328921365445727058847 2674993382048168590588271)
    ·
      refine ⟨4012490073072252885882407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2674993382048168590588271 4012490073072252885882407)
      ·
        refine ⟨6018735109608379328823611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4012490073072252885882407 6018735109608379328823611)
        ·
          refine ⟨9028102664412568993235417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6018735109608379328823611 9028102664412568993235417)
          ·
            refine ⟨6771076998309426744926563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9028102664412568993235417 6771076998309426744926563)
            ·
              refine ⟨10156615497464140117389845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6771076998309426744926563 10156615497464140117389845)
              ·
                refine ⟨476091351443631568002649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10156615497464140117389845 476091351443631568002649)
                ·
                  refine ⟨357068513582723676001987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 476091351443631568002649 357068513582723676001987)
                  ·
                    refine ⟨535602770374085514002981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 357068513582723676001987 535602770374085514002981)
                    ·
                      refine ⟨100425519445141033875559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 535602770374085514002981 100425519445141033875559)
                      ·
                        rfl

theorem cell23_195578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 6, 2, 1, 4].length) (baseStart_195578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_195578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_195578 prefixEnd_195578 := by exact prefixLift 195578
  have htrace : WordTrace (prefixWord ++ tailWord_195578) baseStart_195578 baseEnd_195578 := by
    simpa [prefixWord, tailWord_195578, baseEnd_195578] using wordTrace_append hprefix tailTrace_195578
  have hstable : (prefixWord ++ tailWord_195578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195578).length < 2 ^ (prefixWord ++ tailWord_195578).sum := by decide
  have hdescent : baseEnd_195578 < baseStart_195578 := by decide
  rcases family_descends (prefixWord ++ tailWord_195578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195595 : List Nat := [1, 1, 1, 1, 6, 2, 2, 1, 2, 4, 2]
def baseStart_195595 : Nat := 118140960795 + 195595 * 2 ^ 59
def prefixEnd_195595 : Nat := 4983230072969 + 3 ^ 40 * 195595 * 2
def baseEnd_195595 : Nat := 100434248616267467362981

theorem tailTrace_195595 : CollatzResearch.WordTrace tailWord_195595 prefixEnd_195595 100434248616267467362981 := by
  unfold tailWord_195595
  simp only [CollatzResearch.WordTrace]
  refine ⟨7133935726400194811604239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4755957150933463207736159 7133935726400194811604239)
  ·
    refine ⟨10700903589600292217406359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7133935726400194811604239 10700903589600292217406359)
    ·
      refine ⟨16051355384400438326109539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10700903589600292217406359 16051355384400438326109539)
      ·
        refine ⟨24077033076600657489164309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16051355384400438326109539 24077033076600657489164309)
        ·
          refine ⟨1128610925465655819804577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 24077033076600657489164309 1128610925465655819804577)
          ·
            refine ⟨846458194099241864853433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1128610925465655819804577 846458194099241864853433)
            ·
              refine ⟨634843645574431398640075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 846458194099241864853433 634843645574431398640075)
              ·
                refine ⟨952265468361647097960113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 634843645574431398640075 952265468361647097960113)
                ·
                  refine ⟨714199101271235323470085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 952265468361647097960113 714199101271235323470085)
                  ·
                    refine ⟨133912331488356623150641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 714199101271235323470085 133912331488356623150641)
                    ·
                      refine ⟨100434248616267467362981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 133912331488356623150641 100434248616267467362981)
                      ·
                        rfl

theorem cell23_195595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 1, 2, 4, 2].length) (baseStart_195595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_195595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_195595 prefixEnd_195595 := by exact prefixLift 195595
  have htrace : WordTrace (prefixWord ++ tailWord_195595) baseStart_195595 baseEnd_195595 := by
    simpa [prefixWord, tailWord_195595, baseEnd_195595] using wordTrace_append hprefix tailTrace_195595
  have hstable : (prefixWord ++ tailWord_195595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195595).length < 2 ^ (prefixWord ++ tailWord_195595).sum := by decide
  have hdescent : baseEnd_195595 < baseStart_195595 := by decide
  rcases family_descends (prefixWord ++ tailWord_195595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195605 : List Nat := [1, 3, 2, 1, 4, 1, 2, 2, 3, 4]
def baseStart_195605 : Nat := 118140960795 + 195605 * 2 ^ 59
def prefixEnd_195605 : Nat := 4983230072969 + 3 ^ 40 * 195605 * 2
def baseEnd_195605 : Nat := 33479794474270809412645

theorem tailTrace_195605 : CollatzResearch.WordTrace tailWord_195605 prefixEnd_195605 33479794474270809412645 := by
  unfold tailWord_195605
  simp only [CollatzResearch.WordTrace]
  refine ⟨7134300456363966519468269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4756200304242644346312179 7134300456363966519468269)
  ·
    refine ⟨2675362671136487444800601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7134300456363966519468269 2675362671136487444800601)
    ·
      refine ⟨2006522003352365583600451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2675362671136487444800601 2006522003352365583600451)
      ·
        refine ⟨3009783005028548375400677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2006522003352365583600451 3009783005028548375400677)
        ·
          refine ⟨564334313442852820387627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3009783005028548375400677 564334313442852820387627)
          ·
            refine ⟨846501470164279230581441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 564334313442852820387627 846501470164279230581441)
            ·
              refine ⟨634876102623209422936081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 846501470164279230581441 634876102623209422936081)
              ·
                refine ⟨476157076967407067202061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 634876102623209422936081 476157076967407067202061)
                ·
                  refine ⟨178558903862777650200773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 476157076967407067202061 178558903862777650200773)
                  ·
                    refine ⟨33479794474270809412645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 178558903862777650200773 33479794474270809412645)
                    ·
                      rfl

theorem cell23_195605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 2, 3, 4].length) (baseStart_195605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_195605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_195605 prefixEnd_195605 := by exact prefixLift 195605
  have htrace : WordTrace (prefixWord ++ tailWord_195605) baseStart_195605 baseEnd_195605 := by
    simpa [prefixWord, tailWord_195605, baseEnd_195605] using wordTrace_append hprefix tailTrace_195605
  have hstable : (prefixWord ++ tailWord_195605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195605).length < 2 ^ (prefixWord ++ tailWord_195605).sum := by decide
  have hdescent : baseEnd_195605 < baseStart_195605 := by decide
  rcases family_descends (prefixWord ++ tailWord_195605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195618 : List Nat := [3, 3, 1, 1, 1, 3, 1, 2, 8]
def baseStart_195618 : Nat := 118140960795 + 195618 * 2 ^ 59
def prefixEnd_195618 : Nat := 4983230072969 + 3 ^ 40 * 195618 * 2
def baseEnd_195618 : Nat := 11160673185702319708375

theorem tailTrace_195618 : CollatzResearch.WordTrace tailWord_195618 prefixEnd_195618 11160673185702319708375 := by
  unfold tailWord_195618
  simp only [CollatzResearch.WordTrace]
  refine ⟨1783693651329217434922877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4756516403544579826461005 1783693651329217434922877)
  ·
    refine ⟨668885119248456538096079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1783693651329217434922877 668885119248456538096079)
    ·
      refine ⟨1003327678872684807144119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 668885119248456538096079 1003327678872684807144119)
      ·
        refine ⟨1504991518309027210716179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1003327678872684807144119 1504991518309027210716179)
        ·
          refine ⟨2257487277463540816074269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1504991518309027210716179 2257487277463540816074269)
          ·
            refine ⟨846557729048827806027851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2257487277463540816074269 846557729048827806027851)
            ·
              refine ⟨1269836593573241709041777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 846557729048827806027851 1269836593573241709041777)
              ·
                refine ⟨952377445179931281781333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1269836593573241709041777 952377445179931281781333)
                ·
                  refine ⟨11160673185702319708375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 952377445179931281781333 11160673185702319708375)
                  ·
                    rfl

theorem cell23_195618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 2, 8].length) (baseStart_195618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_195618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_195618 prefixEnd_195618 := by exact prefixLift 195618
  have htrace : WordTrace (prefixWord ++ tailWord_195618) baseStart_195618 baseEnd_195618 := by
    simpa [prefixWord, tailWord_195618, baseEnd_195618] using wordTrace_append hprefix tailTrace_195618
  have hstable : (prefixWord ++ tailWord_195618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195618).length < 2 ^ (prefixWord ++ tailWord_195618).sum := by decide
  have hdescent : baseEnd_195618 < baseStart_195618 := by decide
  rcases family_descends (prefixWord ++ tailWord_195618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195631 : List Nat := [1, 1, 2, 1, 2, 1, 1, 2, 1, 11]
def baseStart_195631 : Nat := 118140960795 + 195631 * 2 ^ 59
def prefixEnd_195631 : Nat := 4983230072969 + 3 ^ 40 * 195631 * 2
def baseEnd_195631 : Nat := 33484244639943108837605

theorem tailTrace_195631 : CollatzResearch.WordTrace tailWord_195631 prefixEnd_195631 33484244639943108837605 := by
  unfold tailWord_195631
  simp only [CollatzResearch.WordTrace]
  refine ⟨7135248754269772959914747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4756832502846515306609831 7135248754269772959914747)
  ·
    refine ⟨10702873131404659439872121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7135248754269772959914747 10702873131404659439872121)
    ·
      refine ⟨8027154848553494579904091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10702873131404659439872121 8027154848553494579904091)
      ·
        refine ⟨12040732272830241869856137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8027154848553494579904091 12040732272830241869856137)
        ·
          refine ⟨9030549204622681402392103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12040732272830241869856137 9030549204622681402392103)
          ·
            refine ⟨13545823806934022103588155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9030549204622681402392103 13545823806934022103588155)
            ·
              refine ⟨20318735710401033155382233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13545823806934022103588155 20318735710401033155382233)
              ·
                refine ⟨15239051782800774866536675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20318735710401033155382233 15239051782800774866536675)
                ·
                  refine ⟨22858577674201162299805013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15239051782800774866536675 22858577674201162299805013)
                  ·
                    refine ⟨33484244639943108837605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 22858577674201162299805013 33484244639943108837605)
                    ·
                      rfl

theorem cell23_195631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 11].length) (baseStart_195631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_195631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_195631 prefixEnd_195631 := by exact prefixLift 195631
  have htrace : WordTrace (prefixWord ++ tailWord_195631) baseStart_195631 baseEnd_195631 := by
    simpa [prefixWord, tailWord_195631, baseEnd_195631] using wordTrace_append hprefix tailTrace_195631
  have hstable : (prefixWord ++ tailWord_195631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195631).length < 2 ^ (prefixWord ++ tailWord_195631).sum := by decide
  have hdescent : baseEnd_195631 < baseStart_195631 := by decide
  rcases family_descends (prefixWord ++ tailWord_195631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195648 : List Nat := [2, 1, 1, 2, 2, 3, 2, 2, 3, 5]
def baseStart_195648 : Nat := 118140960795 + 195648 * 2 ^ 59
def prefixEnd_195648 : Nat := 4983230072969 + 3 ^ 40 * 195648 * 2
def baseEnd_195648 : Nat := 33487154363651920000079

theorem tailTrace_195648 : CollatzResearch.WordTrace tailWord_195648 prefixEnd_195648 33487154363651920000079 := by
  unfold tailWord_195648
  simp only [CollatzResearch.WordTrace]
  refine ⟨3567934397604092431641799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4757245863472123242189065 3567934397604092431641799)
  ·
    refine ⟨5351901596406138647462699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3567934397604092431641799 5351901596406138647462699)
    ·
      refine ⟨8027852394609207971194049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5351901596406138647462699 8027852394609207971194049)
      ·
        refine ⟨6020889295956905978395537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8027852394609207971194049 6020889295956905978395537)
        ·
          refine ⟨4515666971967679483796653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6020889295956905978395537 4515666971967679483796653)
          ·
            refine ⟨1693375114487879806423745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4515666971967679483796653 1693375114487879806423745)
            ·
              refine ⟨1270031335865909854817809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1693375114487879806423745 1270031335865909854817809)
              ·
                refine ⟨952523501899432391113357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1270031335865909854817809 952523501899432391113357)
                ·
                  refine ⟨357196313212287146667509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 952523501899432391113357 357196313212287146667509)
                  ·
                    refine ⟨33487154363651920000079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 357196313212287146667509 33487154363651920000079)
                    ·
                      rfl

theorem cell23_195648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 2, 3, 5].length) (baseStart_195648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_195648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_195648 prefixEnd_195648 := by exact prefixLift 195648
  have htrace : WordTrace (prefixWord ++ tailWord_195648) baseStart_195648 baseEnd_195648 := by
    simpa [prefixWord, tailWord_195648, baseEnd_195648] using wordTrace_append hprefix tailTrace_195648
  have hstable : (prefixWord ++ tailWord_195648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195648).length < 2 ^ (prefixWord ++ tailWord_195648).sum := by decide
  have hdescent : baseEnd_195648 < baseStart_195648 := by decide
  rcases family_descends (prefixWord ++ tailWord_195648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195665 : List Nat := [1, 2, 2, 1, 3, 1, 5, 2, 1, 5]
def baseStart_195665 : Nat := 118140960795 + 195665 * 2 ^ 59
def prefixEnd_195665 : Nat := 4983230072969 + 3 ^ 40 * 195665 * 2
def baseEnd_195665 : Nat := 33490064087360731162553

theorem tailTrace_195665 : CollatzResearch.WordTrace tailWord_195665 prefixEnd_195665 33490064087360731162553 := by
  unfold tailWord_195665
  simp only [CollatzResearch.WordTrace]
  refine ⟨7136488836146596766652449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4757659224097731177768299 7136488836146596766652449)
  ·
    refine ⟨5352366627109947574989337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7136488836146596766652449 5352366627109947574989337)
    ·
      refine ⟨4014274970332460681242003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5352366627109947574989337 4014274970332460681242003)
      ·
        refine ⟨6021412455498691021863005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4014274970332460681242003 6021412455498691021863005)
        ·
          refine ⟨2258029670812009133198627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6021412455498691021863005 2258029670812009133198627)
          ·
            refine ⟨3387044506218013699797941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2258029670812009133198627 3387044506218013699797941)
            ·
              refine ⟨317535422457938784356057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3387044506218013699797941 317535422457938784356057)
              ·
                refine ⟨238151566843454088267043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 317535422457938784356057 238151566843454088267043)
                ·
                  refine ⟨357227350265181132400565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 238151566843454088267043 357227350265181132400565)
                  ·
                    refine ⟨33490064087360731162553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 357227350265181132400565 33490064087360731162553)
                    ·
                      rfl

theorem cell23_195665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 5, 2, 1, 5].length) (baseStart_195665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_195665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_195665 prefixEnd_195665 := by exact prefixLift 195665
  have htrace : WordTrace (prefixWord ++ tailWord_195665) baseStart_195665 baseEnd_195665 := by
    simpa [prefixWord, tailWord_195665, baseEnd_195665] using wordTrace_append hprefix tailTrace_195665
  have hstable : (prefixWord ++ tailWord_195665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195665).length < 2 ^ (prefixWord ++ tailWord_195665).sum := by decide
  have hdescent : baseEnd_195665 < baseStart_195665 := by decide
  rcases family_descends (prefixWord ++ tailWord_195665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195672 : List Nat := [2, 1, 2, 2, 1, 3, 4, 1, 2, 3, 2]
def baseStart_195672 : Nat := 118140960795 + 195672 * 2 ^ 59
def prefixEnd_195672 : Nat := 4983230072969 + 3 ^ 40 * 195672 * 2
def baseEnd_195672 : Nat := 100473786626663666100127

theorem tailTrace_195672 : CollatzResearch.WordTrace tailWord_195672 prefixEnd_195672 100473786626663666100127 := by
  unfold tailWord_195672
  simp only [CollatzResearch.WordTrace]
  refine ⟨3568372073560618481078635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4757829431414157974771513 3568372073560618481078635)
  ·
    refine ⟨5352558110340927721617953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3568372073560618481078635 5352558110340927721617953)
    ·
      refine ⟨4014418582755695791213465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5352558110340927721617953 4014418582755695791213465)
      ·
        refine ⟨3010813937066771843410099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4014418582755695791213465 3010813937066771843410099)
        ·
          refine ⟨4516220905600157765115149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3010813937066771843410099 4516220905600157765115149)
          ·
            refine ⟨1693582839600059161918181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4516220905600157765115149 1693582839600059161918181)
            ·
              refine ⟨317546782425011092859659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1693582839600059161918181 317546782425011092859659)
              ·
                refine ⟨476320173637516639289489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 317546782425011092859659 476320173637516639289489)
                ·
                  refine ⟨357240130228137479467117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 476320173637516639289489 357240130228137479467117)
                  ·
                    refine ⟨133965048835551554800169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 357240130228137479467117 133965048835551554800169)
                    ·
                      refine ⟨100473786626663666100127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 133965048835551554800169 100473786626663666100127)
                      ·
                        rfl

theorem cell23_195672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 4, 1, 2, 3, 2].length) (baseStart_195672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_195672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_195672 prefixEnd_195672 := by exact prefixLift 195672
  have htrace : WordTrace (prefixWord ++ tailWord_195672) baseStart_195672 baseEnd_195672 := by
    simpa [prefixWord, tailWord_195672, baseEnd_195672] using wordTrace_append hprefix tailTrace_195672
  have hstable : (prefixWord ++ tailWord_195672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195672).length < 2 ^ (prefixWord ++ tailWord_195672).sum := by decide
  have hdescent : baseEnd_195672 < baseStart_195672 := by decide
  rcases family_descends (prefixWord ++ tailWord_195672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195715 : List Nat := [1, 1, 1, 3, 3, 2, 4, 1, 1, 2, 4]
def baseStart_195715 : Nat := 118140960795 + 195715 * 2 ^ 59
def prefixEnd_195715 : Nat := 4983230072969 + 3 ^ 40 * 195715 * 2
def baseEnd_195715 : Nat := 100495866294806997862429

theorem tailTrace_195715 : CollatzResearch.WordTrace tailWord_195715 prefixEnd_195715 100495866294806997862429 := by
  unfold tailWord_195715
  simp only [CollatzResearch.WordTrace]
  refine ⟨7138312485965455305972599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4758874990643636870648399 7138312485965455305972599)
  ·
    refine ⟨10707468728948182958958899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7138312485965455305972599 10707468728948182958958899)
    ·
      refine ⟨16061203093422274438438349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10707468728948182958958899 16061203093422274438438349)
      ·
        refine ⟨6022951160033352914414381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16061203093422274438438349 6022951160033352914414381)
        ·
          refine ⟨2258606685012507342905393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6022951160033352914414381 2258606685012507342905393)
          ·
            refine ⟨1693955013759380507179045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2258606685012507342905393 1693955013759380507179045)
            ·
              refine ⟨317616565079883845096071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1693955013759380507179045 317616565079883845096071)
              ·
                refine ⟨476424847619825767644107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 317616565079883845096071 476424847619825767644107)
                ·
                  refine ⟨714637271429738651466161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 476424847619825767644107 714637271429738651466161)
                  ·
                    refine ⟨535977953572303988599621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 714637271429738651466161 535977953572303988599621)
                    ·
                      refine ⟨100495866294806997862429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 535977953572303988599621 100495866294806997862429)
                      ·
                        rfl

theorem cell23_195715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 4, 1, 1, 2, 4].length) (baseStart_195715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_195715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_195715 prefixEnd_195715 := by exact prefixLift 195715
  have htrace : WordTrace (prefixWord ++ tailWord_195715) baseStart_195715 baseEnd_195715 := by
    simpa [prefixWord, tailWord_195715, baseEnd_195715] using wordTrace_append hprefix tailTrace_195715
  have hstable : (prefixWord ++ tailWord_195715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195715).length < 2 ^ (prefixWord ++ tailWord_195715).sum := by decide
  have hdescent : baseEnd_195715 < baseStart_195715 := by decide
  rcases family_descends (prefixWord ++ tailWord_195715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_195722 : List Nat := [3, 1, 2, 3, 1, 1, 2, 4, 1, 2, 3]
def baseStart_195722 : Nat := 118140960795 + 195722 * 2 ^ 59
def prefixEnd_195722 : Nat := 4983230072969 + 3 ^ 40 * 195722 * 2
def baseEnd_195722 : Nat := 100499460659388470474897

theorem tailTrace_195722 : CollatzResearch.WordTrace tailWord_195722 prefixEnd_195722 100499460659388470474897 := by
  unfold tailWord_195722
  simp only [CollatzResearch.WordTrace]
  refine ⟨1784641949235023875369355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4759045197960063667651613 1784641949235023875369355)
  ·
    refine ⟨2676962923852535813054033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1784641949235023875369355 2676962923852535813054033)
    ·
      refine ⟨2007722192889401859790525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2676962923852535813054033 2007722192889401859790525)
      ·
        refine ⟨752895822333525697421447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2007722192889401859790525 752895822333525697421447)
        ·
          refine ⟨1129343733500288546132171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 752895822333525697421447 1129343733500288546132171)
          ·
            refine ⟨1694015600250432819198257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1129343733500288546132171 1694015600250432819198257)
            ·
              refine ⟨1270511700187824614398693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1694015600250432819198257 1270511700187824614398693)
              ·
                refine ⟨238220943785217115199755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1270511700187824614398693 238220943785217115199755)
                ·
                  refine ⟨357331415677825672799633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 238220943785217115199755 357331415677825672799633)
                  ·
                    refine ⟨267998561758369254599725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 357331415677825672799633 267998561758369254599725)
                    ·
                      refine ⟨100499460659388470474897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 267998561758369254599725 100499460659388470474897)
                      ·
                        rfl

theorem cell23_195722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 4, 1, 2, 3].length) (baseStart_195722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_195722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_195722 prefixEnd_195722 := by exact prefixLift 195722
  have htrace : WordTrace (prefixWord ++ tailWord_195722) baseStart_195722 baseEnd_195722 := by
    simpa [prefixWord, tailWord_195722, baseEnd_195722] using wordTrace_append hprefix tailTrace_195722
  have hstable : (prefixWord ++ tailWord_195722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_195722).length < 2 ^ (prefixWord ++ tailWord_195722).sum := by decide
  have hdescent : baseEnd_195722 < baseStart_195722 := by decide
  rcases family_descends (prefixWord ++ tailWord_195722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
