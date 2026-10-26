import V185TrunkScan20Chunk148

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_905930 : List Nat := [3, 1, 2, 1, 4, 1, 3, 3, 2]
def baseStart_905930 : Nat := 118140960795 + 905930 * 2 ^ 59
def prefixEnd_905930 : Nat := 4983230072969 + 3 ^ 40 * 905930 * 2
def baseEnd_905930 : Nat := 413491137180218469696631

theorem tailTrace_905930 : CollatzResearch.WordTrace tailWord_905930 prefixEnd_905930 413491137180218469696631 := by
  unfold tailWord_905930
  simp only [CollatzResearch.WordTrace]
  refine ⟨8260495401994451342794811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22027987738651870247452829 8260495401994451342794811)
  ·
    refine ⟨12390743102991677014192217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8260495401994451342794811 12390743102991677014192217)
    ·
      refine ⟨9293057327243757760644163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12390743102991677014192217 9293057327243757760644163)
      ·
        refine ⟨13939585990865636640966245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9293057327243757760644163 13939585990865636640966245)
        ·
          refine ⟨2613672373287306870181171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13939585990865636640966245 2613672373287306870181171)
          ·
            refine ⟨3920508559930960305271757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2613672373287306870181171 3920508559930960305271757)
            ·
              refine ⟨1470190709974110114476909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3920508559930960305271757 1470190709974110114476909)
              ·
                refine ⟨551321516240291292928841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1470190709974110114476909 551321516240291292928841)
                ·
                  refine ⟨413491137180218469696631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 551321516240291292928841 413491137180218469696631)
                  ·
                    rfl

theorem cell20_905930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 3, 3, 2].length) (baseStart_905930 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_905930 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_905930 prefixEnd_905930 := by exact prefixLift 905930
  have htrace : WordTrace (prefixWord ++ tailWord_905930) baseStart_905930 baseEnd_905930 := by
    simpa [prefixWord, tailWord_905930, baseEnd_905930] using wordTrace_append hprefix tailTrace_905930
  have hstable : (prefixWord ++ tailWord_905930).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905930).length < 2 ^ (prefixWord ++ tailWord_905930).sum := by decide
  have hdescent : baseEnd_905930 < baseStart_905930 := by decide
  rcases family_descends (prefixWord ++ tailWord_905930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_905951 : List Nat := [1, 1, 2, 3, 2, 5, 1, 1, 4]
def baseStart_905951 : Nat := 118140960795 + 905951 * 2 ^ 59
def prefixEnd_905951 : Nat := 4983230072969 + 3 ^ 40 * 905951 * 2
def baseEnd_905951 : Nat := 413500722152435729996545

theorem tailTrace_905951 : CollatzResearch.WordTrace tailWord_905951 prefixEnd_905951 413500722152435729996545 := by
  unfold tailWord_905951
  simp only [CollatzResearch.WordTrace]
  refine ⟨33042747540901725957693707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22028498360601150638462471 33042747540901725957693707)
  ·
    refine ⟨49564121311352588936540561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33042747540901725957693707 49564121311352588936540561)
    ·
      refine ⟨37173090983514441702405421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49564121311352588936540561 37173090983514441702405421)
      ·
        refine ⟨13939909118817915638402033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37173090983514441702405421 13939909118817915638402033)
        ·
          refine ⟨10454931839113436728801525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13939909118817915638402033 10454931839113436728801525)
          ·
            refine ⟨980149859916884693325143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10454931839113436728801525 980149859916884693325143)
            ·
              refine ⟨1470224789875327039987715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 980149859916884693325143 1470224789875327039987715)
              ·
                refine ⟨2205337184812990559981573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1470224789875327039987715 2205337184812990559981573)
                ·
                  refine ⟨413500722152435729996545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2205337184812990559981573 413500722152435729996545)
                  ·
                    rfl

theorem cell20_905951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 1, 1, 4].length) (baseStart_905951 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_905951 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_905951 prefixEnd_905951 := by exact prefixLift 905951
  have htrace : WordTrace (prefixWord ++ tailWord_905951) baseStart_905951 baseEnd_905951 := by
    simpa [prefixWord, tailWord_905951, baseEnd_905951] using wordTrace_append hprefix tailTrace_905951
  have hstable : (prefixWord ++ tailWord_905951).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_905951).length < 2 ^ (prefixWord ++ tailWord_905951).sum := by decide
  have hdescent : baseEnd_905951 < baseStart_905951 := by decide
  rcases family_descends (prefixWord ++ tailWord_905951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906003 : List Nat := [1, 1, 1, 2, 1, 3, 6, 2, 3]
def baseStart_906003 : Nat := 118140960795 + 906003 * 2 ^ 59
def prefixEnd_906003 : Nat := 4983230072969 + 3 ^ 40 * 906003 * 2
def baseEnd_906003 : Nat := 413524456369354660262999

theorem tailTrace_906003 : CollatzResearch.WordTrace tailWord_906003 prefixEnd_906003 413524456369354660262999 := by
  unfold tailWord_906003
  simp only [CollatzResearch.WordTrace]
  refine ⟨33044644136713338838586663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22029762757808892559057775 33044644136713338838586663)
  ·
    refine ⟨49566966205070008257879995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33044644136713338838586663 49566966205070008257879995)
    ·
      refine ⟨74350449307605012386819993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49566966205070008257879995 74350449307605012386819993)
      ·
        refine ⟨55762836980703759290114995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74350449307605012386819993 55762836980703759290114995)
        ·
          refine ⟨83644255471055638935172493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55762836980703759290114995 83644255471055638935172493)
          ·
            refine ⟨31366595801645864600689685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83644255471055638935172493 31366595801645864600689685)
            ·
              refine ⟨1470309178202149903157329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 31366595801645864600689685 1470309178202149903157329)
              ·
                refine ⟨1102731883651612427367997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1470309178202149903157329 1102731883651612427367997)
                ·
                  refine ⟨413524456369354660262999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1102731883651612427367997 413524456369354660262999)
                  ·
                    rfl

theorem cell20_906003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 6, 2, 3].length) (baseStart_906003 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_906003 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_906003 prefixEnd_906003 := by exact prefixLift 906003
  have htrace : WordTrace (prefixWord ++ tailWord_906003) baseStart_906003 baseEnd_906003 := by
    simpa [prefixWord, tailWord_906003, baseEnd_906003] using wordTrace_append hprefix tailTrace_906003
  have hstable : (prefixWord ++ tailWord_906003).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906003).length < 2 ^ (prefixWord ++ tailWord_906003).sum := by decide
  have hdescent : baseEnd_906003 < baseStart_906003 := by decide
  rcases family_descends (prefixWord ++ tailWord_906003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906010 : List Nat := [3, 1, 1, 3, 2, 1, 2, 3, 4]
def baseStart_906010 : Nat := 118140960795 + 906010 * 2 ^ 59
def prefixEnd_906010 : Nat := 4983230072969 + 3 ^ 40 * 906010 * 2
def baseEnd_906010 : Nat := 413527651360093747029637

theorem tailTrace_906010 : CollatzResearch.WordTrace tailWord_906010 prefixEnd_906010 413527651360093747029637 := by
  unfold tailWord_906010
  simp only [CollatzResearch.WordTrace]
  refine ⟨8261224861921994758522871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22029932965125319356060989 8261224861921994758522871)
  ·
    refine ⟨12391837292882992137784307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8261224861921994758522871 12391837292882992137784307)
    ·
      refine ⟨18587755939324488206676461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12391837292882992137784307 18587755939324488206676461)
      ·
        refine ⟨6970408477246683077503673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18587755939324488206676461 6970408477246683077503673)
        ·
          refine ⟨5227806357935012308127755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6970408477246683077503673 5227806357935012308127755)
          ·
            refine ⟨7841709536902518462191633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5227806357935012308127755 7841709536902518462191633)
            ·
              refine ⟨5881282152676888846643725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7841709536902518462191633 5881282152676888846643725)
              ·
                refine ⟨2205480807253833317491397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5881282152676888846643725 2205480807253833317491397)
                ·
                  refine ⟨413527651360093747029637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2205480807253833317491397 413527651360093747029637)
                  ·
                    rfl

theorem cell20_906010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 3, 4].length) (baseStart_906010 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_906010 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_906010 prefixEnd_906010 := by exact prefixLift 906010
  have htrace : WordTrace (prefixWord ++ tailWord_906010) baseStart_906010 baseEnd_906010 := by
    simpa [prefixWord, tailWord_906010, baseEnd_906010] using wordTrace_append hprefix tailTrace_906010
  have hstable : (prefixWord ++ tailWord_906010).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906010).length < 2 ^ (prefixWord ++ tailWord_906010).sum := by decide
  have hdescent : baseEnd_906010 < baseStart_906010 := by decide
  rcases family_descends (prefixWord ++ tailWord_906010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906034 : List Nat := [3, 2, 1, 1, 3, 1, 5, 4]
def baseStart_906034 : Nat := 118140960795 + 906034 * 2 ^ 59
def prefixEnd_906034 : Nat := 4983230072969 + 3 ^ 40 * 906034 * 2
def baseEnd_906034 : Nat := 137846201871352110076513

theorem tailTrace_906034 : CollatzResearch.WordTrace tailWord_906034 prefixEnd_906034 137846201871352110076513 := by
  unfold tailWord_906034
  simp only [CollatzResearch.WordTrace]
  refine ⟨8261443699900257783241289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22030516533067354088643437 8261443699900257783241289)
  ·
    refine ⟨6196082774925193337430967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8261443699900257783241289 6196082774925193337430967)
    ·
      refine ⟨9294124162387790006146451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6196082774925193337430967 9294124162387790006146451)
      ·
        refine ⟨13941186243581685009219677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9294124162387790006146451 13941186243581685009219677)
        ·
          refine ⟨5227944841343131878457379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13941186243581685009219677 5227944841343131878457379)
          ·
            refine ⟨7841917262014697817686069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5227944841343131878457379 7841917262014697817686069)
            ·
              refine ⟨735179743313877920408069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7841917262014697817686069 735179743313877920408069)
              ·
                refine ⟨137846201871352110076513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 735179743313877920408069 137846201871352110076513)
                ·
                  rfl

theorem cell20_906034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 5, 4].length) (baseStart_906034 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_906034 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_906034 prefixEnd_906034 := by exact prefixLift 906034
  have htrace : WordTrace (prefixWord ++ tailWord_906034) baseStart_906034 baseEnd_906034 := by
    simpa [prefixWord, tailWord_906034, baseEnd_906034] using wordTrace_append hprefix tailTrace_906034
  have hstable : (prefixWord ++ tailWord_906034).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906034).length < 2 ^ (prefixWord ++ tailWord_906034).sum := by decide
  have hdescent : baseEnd_906034 < baseStart_906034 := by decide
  rcases family_descends (prefixWord ++ tailWord_906034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906065 : List Nat := [1, 2, 2, 1, 6, 1, 2, 1, 4]
def baseStart_906065 : Nat := 118140960795 + 906065 * 2 ^ 59
def prefixEnd_906065 : Nat := 4983230072969 + 3 ^ 40 * 906065 * 2
def baseEnd_906065 : Nat := 413552754858758000196079

theorem tailTrace_906065 : CollatzResearch.WordTrace tailWord_906065 prefixEnd_906065 413552754858758000196079 := by
  unfold tailWord_906065
  simp only [CollatzResearch.WordTrace]
  refine ⟨33046905462488723427343649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22031270308325815618229099 33046905462488723427343649)
  ·
    refine ⟨24785179096866542570507737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33046905462488723427343649 24785179096866542570507737)
    ·
      refine ⟨18588884322649906927880803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24785179096866542570507737 18588884322649906927880803)
      ·
        refine ⟨27883326483974860391821205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18588884322649906927880803 27883326483974860391821205)
        ·
          refine ⟨1307030928936321580866619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 27883326483974860391821205 1307030928936321580866619)
          ·
            refine ⟨1960546393404482371299929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1307030928936321580866619 1960546393404482371299929)
            ·
              refine ⟨1470409795053361778474947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1960546393404482371299929 1470409795053361778474947)
              ·
                refine ⟨2205614692580042667712421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1470409795053361778474947 2205614692580042667712421)
                ·
                  refine ⟨413552754858758000196079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2205614692580042667712421 413552754858758000196079)
                  ·
                    rfl

theorem cell20_906065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 2, 1, 4].length) (baseStart_906065 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_906065 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_906065 prefixEnd_906065 := by exact prefixLift 906065
  have htrace : WordTrace (prefixWord ++ tailWord_906065) baseStart_906065 baseEnd_906065 := by
    simpa [prefixWord, tailWord_906065, baseEnd_906065] using wordTrace_append hprefix tailTrace_906065
  have hstable : (prefixWord ++ tailWord_906065).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906065).length < 2 ^ (prefixWord ++ tailWord_906065).sum := by decide
  have hdescent : baseEnd_906065 < baseStart_906065 := by decide
  rcases family_descends (prefixWord ++ tailWord_906065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906107 : List Nat := [1, 1, 1, 1, 1, 5, 2, 2, 6]
def baseStart_906107 : Nat := 118140960795 + 906107 * 2 ^ 59
def prefixEnd_906107 : Nat := 4983230072969 + 3 ^ 40 * 906107 * 2
def baseEnd_906107 : Nat := 413571924803192520795907

theorem tailTrace_906107 : CollatzResearch.WordTrace tailWord_906107 prefixEnd_906107 413571924803192520795907 := by
  unfold tailWord_906107
  simp only [CollatzResearch.WordTrace]
  refine ⟨33048437328336564600372575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22032291552224376400248383 33048437328336564600372575)
  ·
    refine ⟨49572655992504846900558863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33048437328336564600372575 49572655992504846900558863)
    ·
      refine ⟨74358983988757270350838295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49572655992504846900558863 74358983988757270350838295)
      ·
        refine ⟨111538475983135905526257443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74358983988757270350838295 111538475983135905526257443)
        ·
          refine ⟨167307713974703858289386165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111538475983135905526257443 167307713974703858289386165)
          ·
            refine ⟨15685098185128486714629953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 167307713974703858289386165 15685098185128486714629953)
            ·
              refine ⟨11763823638846365035972465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15685098185128486714629953 11763823638846365035972465)
              ·
                refine ⟨8822867729134773776979349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11763823638846365035972465 8822867729134773776979349)
                ·
                  refine ⟨413571924803192520795907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8822867729134773776979349 413571924803192520795907)
                  ·
                    rfl

theorem cell20_906107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 2, 6].length) (baseStart_906107 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_906107 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_906107 prefixEnd_906107 := by exact prefixLift 906107
  have htrace : WordTrace (prefixWord ++ tailWord_906107) baseStart_906107 baseEnd_906107 := by
    simpa [prefixWord, tailWord_906107, baseEnd_906107] using wordTrace_append hprefix tailTrace_906107
  have hstable : (prefixWord ++ tailWord_906107).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906107).length < 2 ^ (prefixWord ++ tailWord_906107).sum := by decide
  have hdescent : baseEnd_906107 < baseStart_906107 := by decide
  rcases family_descends (prefixWord ++ tailWord_906107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906124 : List Nat := [2, 2, 1, 2, 1, 2, 5, 1, 4]
def baseStart_906124 : Nat := 118140960795 + 906124 * 2 ^ 59
def prefixEnd_906124 : Nat := 4983230072969 + 3 ^ 40 * 906124 * 2
def baseEnd_906124 : Nat := 413579684066416017229171

theorem tailTrace_906124 : CollatzResearch.WordTrace tailWord_906124 prefixEnd_906124 413579684066416017229171 := by
  unfold tailWord_906124
  simp only [CollatzResearch.WordTrace]
  refine ⟨16524528684637488251870713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22032704912849984335827617 16524528684637488251870713)
  ·
    refine ⟨12393396513478116188903035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16524528684637488251870713 12393396513478116188903035)
    ·
      refine ⟨18590094770217174283354553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12393396513478116188903035 18590094770217174283354553)
      ·
        refine ⟨13942571077662880712515915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18590094770217174283354553 13942571077662880712515915)
        ·
          refine ⟨20913856616494321068773873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13942571077662880712515915 20913856616494321068773873)
          ·
            refine ⟨15685392462370740801580405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20913856616494321068773873 15685392462370740801580405)
            ·
              refine ⟨1470505543347256950148163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15685392462370740801580405 1470505543347256950148163)
              ·
                refine ⟨2205758315020885425222245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1470505543347256950148163 2205758315020885425222245)
                ·
                  refine ⟨413579684066416017229171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2205758315020885425222245 413579684066416017229171)
                  ·
                    rfl

theorem cell20_906124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 5, 1, 4].length) (baseStart_906124 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_906124 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_906124 prefixEnd_906124 := by exact prefixLift 906124
  have htrace : WordTrace (prefixWord ++ tailWord_906124) baseStart_906124 baseEnd_906124 := by
    simpa [prefixWord, tailWord_906124, baseEnd_906124] using wordTrace_append hprefix tailTrace_906124
  have hstable : (prefixWord ++ tailWord_906124).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906124).length < 2 ^ (prefixWord ++ tailWord_906124).sum := by decide
  have hdescent : baseEnd_906124 < baseStart_906124 := by decide
  rcases family_descends (prefixWord ++ tailWord_906124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906130 : List Nat := [3, 2, 3, 2, 2, 2, 2, 1, 3]
def baseStart_906130 : Nat := 118140960795 + 906130 * 2 ^ 59
def prefixEnd_906130 : Nat := 4983230072969 + 3 ^ 40 * 906130 * 2
def baseEnd_906130 : Nat := 413582422629906663029147

theorem tailTrace_906130 : CollatzResearch.WordTrace tailWord_906130 prefixEnd_906130 413582422629906663029147 := by
  unfold tailWord_906130
  simp only [CollatzResearch.WordTrace]
  refine ⟨8262319051813309882114961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22032850804835493018973229 8262319051813309882114961)
  ·
    refine ⟨6196739288859982411586221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8262319051813309882114961 6196739288859982411586221)
    ·
      refine ⟨2323777233322493404344833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6196739288859982411586221 2323777233322493404344833)
      ·
        refine ⟨1742832924991870053258625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2323777233322493404344833 1742832924991870053258625)
        ·
          refine ⟨1307124693743902539943969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1742832924991870053258625 1307124693743902539943969)
          ·
            refine ⟨980343520307926904957977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1307124693743902539943969 980343520307926904957977)
            ·
              refine ⟨735257640230945178718483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 980343520307926904957977 735257640230945178718483)
              ·
                refine ⟨1102886460346417768077725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 735257640230945178718483 1102886460346417768077725)
                ·
                  refine ⟨413582422629906663029147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1102886460346417768077725 413582422629906663029147)
                  ·
                    rfl

theorem cell20_906130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 2, 1, 3].length) (baseStart_906130 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_906130 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_906130 prefixEnd_906130 := by exact prefixLift 906130
  have htrace : WordTrace (prefixWord ++ tailWord_906130) baseStart_906130 baseEnd_906130 := by
    simpa [prefixWord, tailWord_906130, baseEnd_906130] using wordTrace_append hprefix tailTrace_906130
  have hstable : (prefixWord ++ tailWord_906130).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906130).length < 2 ^ (prefixWord ++ tailWord_906130).sum := by decide
  have hdescent : baseEnd_906130 < baseStart_906130 := by decide
  rcases family_descends (prefixWord ++ tailWord_906130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906200 : List Nat := [2, 1, 2, 2, 2, 4, 1, 2, 4]
def baseStart_906200 : Nat := 118140960795 + 906200 * 2 ^ 59
def prefixEnd_906200 : Nat := 4983230072969 + 3 ^ 40 * 906200 * 2
def baseEnd_906200 : Nat := 413614372537297530695527

theorem tailTrace_906200 : CollatzResearch.WordTrace tailWord_906200 prefixEnd_906200 413614372537297530695527 := by
  unfold tailWord_906200
  simp only [CollatzResearch.WordTrace]
  refine ⟨16525914658499820741754027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22034552877999760989005369 16525914658499820741754027)
  ·
    refine ⟨24788871987749731112631041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16525914658499820741754027 24788871987749731112631041)
    ·
      refine ⟨18591653990812298334473281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24788871987749731112631041 18591653990812298334473281)
      ·
        refine ⟨13943740493109223750854961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18591653990812298334473281 13943740493109223750854961)
        ·
          refine ⟨10457805369831917813141221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13943740493109223750854961 10457805369831917813141221)
          ·
            refine ⟨1960838506843484589963979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10457805369831917813141221 1960838506843484589963979)
            ·
              refine ⟨2941257760265226884945969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1960838506843484589963979 2941257760265226884945969)
              ·
                refine ⟨2205943320198920163709477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2941257760265226884945969 2205943320198920163709477)
                ·
                  refine ⟨413614372537297530695527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2205943320198920163709477 413614372537297530695527)
                  ·
                    rfl

theorem cell20_906200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 2, 4].length) (baseStart_906200 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_906200 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_906200 prefixEnd_906200 := by exact prefixLift 906200
  have htrace : WordTrace (prefixWord ++ tailWord_906200) baseStart_906200 baseEnd_906200 := by
    simpa [prefixWord, tailWord_906200, baseEnd_906200] using wordTrace_append hprefix tailTrace_906200
  have hstable : (prefixWord ++ tailWord_906200).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906200).length < 2 ^ (prefixWord ++ tailWord_906200).sum := by decide
  have hdescent : baseEnd_906200 < baseStart_906200 := by decide
  rcases family_descends (prefixWord ++ tailWord_906200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906213 : List Nat := [1, 3, 1, 6, 1, 1, 2, 3, 2]
def baseStart_906213 : Nat := 118140960795 + 906213 * 2 ^ 59
def prefixEnd_906213 : Nat := 4983230072969 + 3 ^ 40 * 906213 * 2
def baseEnd_906213 : Nat := 413620306091527263262141

theorem tailTrace_906213 : CollatzResearch.WordTrace tailWord_906213 prefixEnd_906213 413620306091527263262141 := by
  unfold tailWord_906213
  simp only [CollatzResearch.WordTrace]
  refine ⟨33052303465952544703731293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22034868977301696469154195 33052303465952544703731293)
  ·
    refine ⟨12394613799732204263899235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33052303465952544703731293 12394613799732204263899235)
    ·
      refine ⟨18591920699598306395848853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12394613799732204263899235 18591920699598306395848853)
      ·
        refine ⟨871496282793670612305415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 18591920699598306395848853 871496282793670612305415)
        ·
          refine ⟨1307244424190505918458123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 871496282793670612305415 1307244424190505918458123)
          ·
            refine ⟨1960866636285758877687185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1307244424190505918458123 1960866636285758877687185)
            ·
              refine ⟨1470649977214319158265389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1960866636285758877687185 1470649977214319158265389)
              ·
                refine ⟨551493741455369684349521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1470649977214319158265389 551493741455369684349521)
                ·
                  refine ⟨413620306091527263262141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 551493741455369684349521 413620306091527263262141)
                  ·
                    rfl

theorem cell20_906213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 2, 3, 2].length) (baseStart_906213 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_906213 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_906213 prefixEnd_906213 := by exact prefixLift 906213
  have htrace : WordTrace (prefixWord ++ tailWord_906213) baseStart_906213 baseEnd_906213 := by
    simpa [prefixWord, tailWord_906213, baseEnd_906213] using wordTrace_append hprefix tailTrace_906213
  have hstable : (prefixWord ++ tailWord_906213).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906213).length < 2 ^ (prefixWord ++ tailWord_906213).sum := by decide
  have hdescent : baseEnd_906213 < baseStart_906213 := by decide
  rcases family_descends (prefixWord ++ tailWord_906213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906248 : List Nat := [2, 1, 3, 2, 1, 4, 3, 1, 3]
def baseStart_906248 : Nat := 118140960795 + 906248 * 2 ^ 59
def prefixEnd_906248 : Nat := 4983230072969 + 3 ^ 40 * 906248 * 2
def baseEnd_906248 : Nat := 413636281045222697095331

theorem tailTrace_906248 : CollatzResearch.WordTrace tailWord_906248 prefixEnd_906248 413636281045222697095331 := by
  unfold tailWord_906248
  simp only [CollatzResearch.WordTrace]
  refine ⟨16526790010412872840627699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22035720013883830454170265 16526790010412872840627699)
  ·
    refine ⟨24790185015619309260941549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16526790010412872840627699 24790185015619309260941549)
    ·
      refine ⟨9296319380857240972853081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24790185015619309260941549 9296319380857240972853081)
      ·
        refine ⟨6972239535642930729639811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9296319380857240972853081 6972239535642930729639811)
        ·
          refine ⟨10458359303464396094459717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6972239535642930729639811 10458359303464396094459717)
          ·
            refine ⟨1960942369399574267711197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10458359303464396094459717 1960942369399574267711197)
            ·
              refine ⟨735353388524840350391699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1960942369399574267711197 735353388524840350391699)
              ·
                refine ⟨1103030082787260525587549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 735353388524840350391699 1103030082787260525587549)
                ·
                  refine ⟨413636281045222697095331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1103030082787260525587549 413636281045222697095331)
                  ·
                    rfl

theorem cell20_906248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 3, 1, 3].length) (baseStart_906248 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_906248 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_906248 prefixEnd_906248 := by exact prefixLift 906248
  have htrace : WordTrace (prefixWord ++ tailWord_906248) baseStart_906248 baseEnd_906248 := by
    simpa [prefixWord, tailWord_906248, baseEnd_906248] using wordTrace_append hprefix tailTrace_906248
  have hstable : (prefixWord ++ tailWord_906248).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906248).length < 2 ^ (prefixWord ++ tailWord_906248).sum := by decide
  have hdescent : baseEnd_906248 < baseStart_906248 := by decide
  rcases family_descends (prefixWord ++ tailWord_906248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906258 : List Nat := [3, 2, 5, 1, 1, 1, 1, 6]
def baseStart_906258 : Nat := 118140960795 + 906258 * 2 ^ 59
def prefixEnd_906258 : Nat := 4983230072969 + 3 ^ 40 * 906258 * 2
def baseEnd_906258 : Nat := 137880281772569035587319

theorem tailTrace_906258 : CollatzResearch.WordTrace tailWord_906258 prefixEnd_906258 137880281772569035587319 := by
  unfold tailWord_906258
  simp only [CollatzResearch.WordTrace]
  refine ⟨8263486187697379347279857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22035963167193011592746285 8263486187697379347279857)
  ·
    refine ⟨6197614640773034510459893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8263486187697379347279857 6197614640773034510459893)
    ·
      refine ⟨581026372572471985355615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6197614640773034510459893 581026372572471985355615)
      ·
        refine ⟨871539558858707978033423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 581026372572471985355615 871539558858707978033423)
        ·
          refine ⟨1307309338288061967050135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 871539558858707978033423 1307309338288061967050135)
          ·
            refine ⟨1960964007432092950575203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1307309338288061967050135 1960964007432092950575203)
            ·
              refine ⟨2941446011148139425862805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1960964007432092950575203 2941446011148139425862805)
              ·
                refine ⟨137880281772569035587319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2941446011148139425862805 137880281772569035587319)
                ·
                  rfl

theorem cell20_906258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 6].length) (baseStart_906258 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_906258 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_906258 prefixEnd_906258 := by exact prefixLift 906258
  have htrace : WordTrace (prefixWord ++ tailWord_906258) baseStart_906258 baseEnd_906258 := by
    simpa [prefixWord, tailWord_906258, baseEnd_906258] using wordTrace_append hprefix tailTrace_906258
  have hstable : (prefixWord ++ tailWord_906258).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906258).length < 2 ^ (prefixWord ++ tailWord_906258).sum := by decide
  have hdescent : baseEnd_906258 < baseStart_906258 := by decide
  rcases family_descends (prefixWord ++ tailWord_906258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906290 : List Nat := [3, 2, 1, 1, 2, 2, 1, 3, 5]
def baseStart_906290 : Nat := 118140960795 + 906290 * 2 ^ 59
def prefixEnd_906290 : Nat := 4983230072969 + 3 ^ 40 * 906290 * 2
def baseEnd_906290 : Nat := 413655450989657217695159

theorem tailTrace_906290 : CollatzResearch.WordTrace tailWord_906290 prefixEnd_906290 413655450989657217695159 := by
  unfold tailWord_906290
  simp only [CollatzResearch.WordTrace]
  refine ⟨8263777971668396713571081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22036741257782391236189549 8263777971668396713571081)
  ·
    refine ⟨6197833478751297535178311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8263777971668396713571081 6197833478751297535178311)
    ·
      refine ⟨9296750218126946302767467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6197833478751297535178311 9296750218126946302767467)
      ·
        refine ⟨13945125327190419454151201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9296750218126946302767467 13945125327190419454151201)
        ·
          refine ⟨10458843995392814590613401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13945125327190419454151201 10458843995392814590613401)
          ·
            refine ⟨7844132996544610942960051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10458843995392814590613401 7844132996544610942960051)
            ·
              refine ⟨11766199494816916414440077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7844132996544610942960051 11766199494816916414440077)
              ·
                refine ⟨4412324810556343655415029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11766199494816916414440077 4412324810556343655415029)
                ·
                  refine ⟨413655450989657217695159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4412324810556343655415029 413655450989657217695159)
                  ·
                    rfl

theorem cell20_906290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 3, 5].length) (baseStart_906290 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_906290 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_906290 prefixEnd_906290 := by exact prefixLift 906290
  have htrace : WordTrace (prefixWord ++ tailWord_906290) baseStart_906290 baseEnd_906290 := by
    simpa [prefixWord, tailWord_906290, baseEnd_906290] using wordTrace_append hprefix tailTrace_906290
  have hstable : (prefixWord ++ tailWord_906290).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906290).length < 2 ^ (prefixWord ++ tailWord_906290).sum := by decide
  have hdescent : baseEnd_906290 < baseStart_906290 := by decide
  rcases family_descends (prefixWord ++ tailWord_906290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906344 : List Nat := [2, 1, 4, 4, 1, 2, 2, 2, 2]
def baseStart_906344 : Nat := 118140960795 + 906344 * 2 ^ 59
def prefixEnd_906344 : Nat := 4983230072969 + 3 ^ 40 * 906344 * 2
def baseEnd_906344 : Nat := 413680098061073029894939

theorem tailTrace_906344 : CollatzResearch.WordTrace tailWord_906344 prefixEnd_906344 413680098061073029894939 := by
  unfold tailWord_906344
  simp only [CollatzResearch.WordTrace]
  refine ⟨16528540714238977038375043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22038054285651969384500057 16528540714238977038375043)
  ·
    refine ⟨24792811071358465557562565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16528540714238977038375043 24792811071358465557562565)
    ·
      refine ⟨4648652075879712292042981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24792811071358465557562565 4648652075879712292042981)
      ·
        refine ⟨871622264227446054758059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4648652075879712292042981 871622264227446054758059)
        ·
          refine ⟨1307433396341169082137089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 871622264227446054758059 1307433396341169082137089)
          ·
            refine ⟨980575047255876811602817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1307433396341169082137089 980575047255876811602817)
            ·
              refine ⟨735431285441907608702113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 980575047255876811602817 735431285441907608702113)
              ·
                refine ⟨551573464081430706526585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 735431285441907608702113 551573464081430706526585)
                ·
                  refine ⟨413680098061073029894939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 551573464081430706526585 413680098061073029894939)
                  ·
                    rfl

theorem cell20_906344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 2, 2, 2].length) (baseStart_906344 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_906344 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_906344 prefixEnd_906344 := by exact prefixLift 906344
  have htrace : WordTrace (prefixWord ++ tailWord_906344) baseStart_906344 baseEnd_906344 := by
    simpa [prefixWord, tailWord_906344, baseEnd_906344] using wordTrace_append hprefix tailTrace_906344
  have hstable : (prefixWord ++ tailWord_906344).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906344).length < 2 ^ (prefixWord ++ tailWord_906344).sum := by decide
  have hdescent : baseEnd_906344 < baseStart_906344 := by decide
  rcases family_descends (prefixWord ++ tailWord_906344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906345 : List Nat := [1, 2, 1, 1, 1, 7, 2, 2, 3]
def baseStart_906345 : Nat := 118140960795 + 906345 * 2 ^ 59
def prefixEnd_906345 : Nat := 4983230072969 + 3 ^ 40 * 906345 * 2
def baseEnd_906345 : Nat := 413680554488321470861601

theorem tailTrace_906345 : CollatzResearch.WordTrace tailWord_906345 prefixEnd_906345 413680554488321470861601 := by
  unfold tailWord_906345
  simp only [CollatzResearch.WordTrace]
  refine ⟨33057117901474331247536489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22038078600982887498357659 33057117901474331247536489)
  ·
    refine ⟨24792838426105748435652367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33057117901474331247536489 24792838426105748435652367)
    ·
      refine ⟨37189257639158622653478551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24792838426105748435652367 37189257639158622653478551)
      ·
        refine ⟨55783886458737933980217827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37189257639158622653478551 55783886458737933980217827)
        ·
          refine ⟨83675829688106900970326741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55783886458737933980217827 83675829688106900970326741)
          ·
            refine ⟨1961152258315005491492033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 83675829688106900970326741 1961152258315005491492033)
            ·
              refine ⟨1470864193736254118619025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1961152258315005491492033 1470864193736254118619025)
              ·
                refine ⟨1103148145302190588964269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1470864193736254118619025 1103148145302190588964269)
                ·
                  refine ⟨413680554488321470861601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1103148145302190588964269 413680554488321470861601)
                  ·
                    rfl

theorem cell20_906345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 2, 2, 3].length) (baseStart_906345 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_906345 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_906345 prefixEnd_906345 := by exact prefixLift 906345
  have htrace : WordTrace (prefixWord ++ tailWord_906345) baseStart_906345 baseEnd_906345 := by
    simpa [prefixWord, tailWord_906345, baseEnd_906345] using wordTrace_append hprefix tailTrace_906345
  have hstable : (prefixWord ++ tailWord_906345).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906345).length < 2 ^ (prefixWord ++ tailWord_906345).sum := by decide
  have hdescent : baseEnd_906345 < baseStart_906345 := by decide
  rcases family_descends (prefixWord ++ tailWord_906345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906380 : List Nat := [2, 2, 1, 2, 1, 1, 1, 10]
def baseStart_906380 : Nat := 118140960795 + 906380 * 2 ^ 59
def prefixEnd_906380 : Nat := 4983230072969 + 3 ^ 40 * 906380 * 2
def baseEnd_906380 : Nat := 137898843147338968231597

theorem tailTrace_906380 : CollatzResearch.WordTrace tailWord_906380 prefixEnd_906380 137898843147338968231597 := by
  unfold tailWord_906380
  simp only [CollatzResearch.WordTrace]
  refine ⟨16529197228173766112530297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22038929637565021483373729 16529197228173766112530297)
  ·
    refine ⟨12396897921130324584397723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16529197228173766112530297 12396897921130324584397723)
    ·
      refine ⟨18595346881695486876596585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12396897921130324584397723 18595346881695486876596585)
      ·
        refine ⟨13946510161271615157447439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18595346881695486876596585 13946510161271615157447439)
        ·
          refine ⟨20919765241907422736171159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13946510161271615157447439 20919765241907422736171159)
          ·
            refine ⟨31379647862861134104256739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20919765241907422736171159 31379647862861134104256739)
            ·
              refine ⟨47069471794291701156385109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31379647862861134104256739 47069471794291701156385109)
              ·
                refine ⟨137898843147338968231597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 47069471794291701156385109 137898843147338968231597)
                ·
                  rfl

theorem cell20_906380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 10].length) (baseStart_906380 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_906380 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_906380 prefixEnd_906380 := by exact prefixLift 906380
  have htrace : WordTrace (prefixWord ++ tailWord_906380) baseStart_906380 baseEnd_906380 := by
    simpa [prefixWord, tailWord_906380, baseEnd_906380] using wordTrace_append hprefix tailTrace_906380
  have hstable : (prefixWord ++ tailWord_906380).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906380).length < 2 ^ (prefixWord ++ tailWord_906380).sum := by decide
  have hdescent : baseEnd_906380 < baseStart_906380 := by decide
  rcases family_descends (prefixWord ++ tailWord_906380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906386 : List Nat := [3, 2, 3, 1, 1, 3, 2, 3, 2]
def baseStart_906386 : Nat := 118140960795 + 906386 * 2 ^ 59
def prefixEnd_906386 : Nat := 4983230072969 + 3 ^ 40 * 906386 * 2
def baseEnd_906386 : Nat := 413699268005507550494767

theorem tailTrace_906386 : CollatzResearch.WordTrace tailWord_906386 prefixEnd_906386 413699268005507550494767 := by
  unfold tailWord_906386
  simp only [CollatzResearch.WordTrace]
  refine ⟨8264653323581448812444753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22039075529550530166519341 8264653323581448812444753)
  ·
    refine ⟨6198489992686086609333565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8264653323581448812444753 6198489992686086609333565)
    ·
      refine ⟨2324433747257282478500087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6198489992686086609333565 2324433747257282478500087)
      ·
        refine ⟨3486650620885923717750131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2324433747257282478500087 3486650620885923717750131)
        ·
          refine ⟨5229975931328885576625197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3486650620885923717750131 5229975931328885576625197)
          ·
            refine ⟨1961240974248332091234449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5229975931328885576625197 1961240974248332091234449)
            ·
              refine ⟨1470930730686249068425837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1961240974248332091234449 1470930730686249068425837)
              ·
                refine ⟨551599024007343400659689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1470930730686249068425837 551599024007343400659689)
                ·
                  refine ⟨413699268005507550494767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 551599024007343400659689 413699268005507550494767)
                  ·
                    rfl

theorem cell20_906386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 2, 3, 2].length) (baseStart_906386 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_906386 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_906386 prefixEnd_906386 := by exact prefixLift 906386
  have htrace : WordTrace (prefixWord ++ tailWord_906386) baseStart_906386 baseEnd_906386 := by
    simpa [prefixWord, tailWord_906386, baseEnd_906386] using wordTrace_append hprefix tailTrace_906386
  have hstable : (prefixWord ++ tailWord_906386).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906386).length < 2 ^ (prefixWord ++ tailWord_906386).sum := by decide
  have hdescent : baseEnd_906386 < baseStart_906386 := by decide
  rcases family_descends (prefixWord ++ tailWord_906386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906407 : List Nat := [1, 1, 6, 2, 1, 2, 2, 1, 4]
def baseStart_906407 : Nat := 118140960795 + 906407 * 2 ^ 59
def prefixEnd_906407 : Nat := 4983230072969 + 3 ^ 40 * 906407 * 2
def baseEnd_906407 : Nat := 413708852977724810794681

theorem tailTrace_906407 : CollatzResearch.WordTrace tailWord_906407 prefixEnd_906407 413708852977724810794681 := by
  unfold tailWord_906407
  simp only [CollatzResearch.WordTrace]
  refine ⟨33059379227249715836293475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22039586151499810557528983 33059379227249715836293475)
  ·
    refine ⟨49589068840874573754440213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33059379227249715836293475 49589068840874573754440213)
    ·
      refine ⟨2324487601915995644739385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 49589068840874573754440213 2324487601915995644739385)
      ·
        refine ⟨1743365701436996733554539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2324487601915995644739385 1743365701436996733554539)
        ·
          refine ⟨2615048552155495100331809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1743365701436996733554539 2615048552155495100331809)
          ·
            refine ⟨1961286414116621325248857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2615048552155495100331809 1961286414116621325248857)
            ·
              refine ⟨1470964810587465993936643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1961286414116621325248857 1470964810587465993936643)
              ·
                refine ⟨2206447215881198990904965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1470964810587465993936643 2206447215881198990904965)
                ·
                  refine ⟨413708852977724810794681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2206447215881198990904965 413708852977724810794681)
                  ·
                    rfl

theorem cell20_906407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 2, 1, 4].length) (baseStart_906407 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_906407 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_906407 prefixEnd_906407 := by exact prefixLift 906407
  have htrace : WordTrace (prefixWord ++ tailWord_906407) baseStart_906407 baseEnd_906407 := by
    simpa [prefixWord, tailWord_906407, baseEnd_906407] using wordTrace_append hprefix tailTrace_906407
  have hstable : (prefixWord ++ tailWord_906407).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906407).length < 2 ^ (prefixWord ++ tailWord_906407).sum := by decide
  have hdescent : baseEnd_906407 < baseStart_906407 := by decide
  rcases family_descends (prefixWord ++ tailWord_906407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906428 : List Nat := [2, 2, 2, 3, 2, 1, 2, 2, 4]
def baseStart_906428 : Nat := 118140960795 + 906428 * 2 ^ 59
def prefixEnd_906428 : Nat := 4983230072969 + 3 ^ 40 * 906428 * 2
def baseEnd_906428 : Nat := 413718437949942071094595

theorem tailTrace_906428 : CollatzResearch.WordTrace tailWord_906428 prefixEnd_906428 413718437949942071094595 := by
  unfold tailWord_906428
  simp only [CollatzResearch.WordTrace]
  refine ⟨16530072580086818211403969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22040096773449090948538625 16530072580086818211403969)
  ·
    refine ⟨12397554435065113658552977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16530072580086818211403969 12397554435065113658552977)
    ·
      refine ⟨9298165826298835243914733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12397554435065113658552977 9298165826298835243914733)
      ·
        refine ⟨3486812184862063216468025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9298165826298835243914733 3486812184862063216468025)
        ·
          refine ⟨2615109138646547412351019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3486812184862063216468025 2615109138646547412351019)
          ·
            refine ⟨3922663707969821118526529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2615109138646547412351019 3922663707969821118526529)
            ·
              refine ⟨2941997780977365838894897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3922663707969821118526529 2941997780977365838894897)
              ·
                refine ⟨2206498335733024379171173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2941997780977365838894897 2206498335733024379171173)
                ·
                  refine ⟨413718437949942071094595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2206498335733024379171173 413718437949942071094595)
                  ·
                    rfl

theorem cell20_906428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 2, 4].length) (baseStart_906428 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_906428 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_906428 prefixEnd_906428 := by exact prefixLift 906428
  have htrace : WordTrace (prefixWord ++ tailWord_906428) baseStart_906428 baseEnd_906428 := by
    simpa [prefixWord, tailWord_906428, baseEnd_906428] using wordTrace_append hprefix tailTrace_906428
  have hstable : (prefixWord ++ tailWord_906428).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906428).length < 2 ^ (prefixWord ++ tailWord_906428).sum := by decide
  have hdescent : baseEnd_906428 < baseStart_906428 := by decide
  rcases family_descends (prefixWord ++ tailWord_906428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906442 : List Nat := [3, 1, 2, 1, 3, 2, 1, 2, 5]
def baseStart_906442 : Nat := 118140960795 + 906442 * 2 ^ 59
def prefixEnd_906442 : Nat := 4983230072969 + 3 ^ 40 * 906442 * 2
def baseEnd_906442 : Nat := 413724827931420244627871

theorem tailTrace_906442 : CollatzResearch.WordTrace tailWord_906442 prefixEnd_906442 413724827931420244627871 := by
  unfold tailWord_906442
  simp only [CollatzResearch.WordTrace]
  refine ⟨8265163945530729203454395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22040437188081944542545053 8265163945530729203454395)
  ·
    refine ⟨12397745918296093805181593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8265163945530729203454395 12397745918296093805181593)
    ·
      refine ⟨9298309438722070353886195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12397745918296093805181593 9298309438722070353886195)
      ·
        refine ⟨13947464158083105530829293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9298309438722070353886195 13947464158083105530829293)
        ·
          refine ⟨5230299059281164574060985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13947464158083105530829293 5230299059281164574060985)
          ·
            refine ⟨3922724294460873430545739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5230299059281164574060985 3922724294460873430545739)
            ·
              refine ⟨5884086441691310145818609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3922724294460873430545739 5884086441691310145818609)
              ·
                refine ⟨4413064831268482609363957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5884086441691310145818609 4413064831268482609363957)
                ·
                  refine ⟨413724827931420244627871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4413064831268482609363957 413724827931420244627871)
                  ·
                    rfl

theorem cell20_906442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 2, 5].length) (baseStart_906442 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_906442 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_906442 prefixEnd_906442 := by exact prefixLift 906442
  have htrace : WordTrace (prefixWord ++ tailWord_906442) baseStart_906442 baseEnd_906442 := by
    simpa [prefixWord, tailWord_906442, baseEnd_906442] using wordTrace_append hprefix tailTrace_906442
  have hstable : (prefixWord ++ tailWord_906442).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906442).length < 2 ^ (prefixWord ++ tailWord_906442).sum := by decide
  have hdescent : baseEnd_906442 < baseStart_906442 := by decide
  rcases family_descends (prefixWord ++ tailWord_906442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906476 : List Nat := [2, 2, 1, 1, 2, 6, 2, 1, 3]
def baseStart_906476 : Nat := 118140960795 + 906476 * 2 ^ 59
def prefixEnd_906476 : Nat := 4983230072969 + 3 ^ 40 * 906476 * 2
def baseEnd_906476 : Nat := 413740346457867237494399

theorem tailTrace_906476 : CollatzResearch.WordTrace tailWord_906476 prefixEnd_906476 413740346457867237494399 := by
  unfold tailWord_906476
  simp only [CollatzResearch.WordTrace]
  refine ⟨16530947931999870310277641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22041263909333160413703521 16530947931999870310277641)
  ·
    refine ⟨12398210948999902732708231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16530947931999870310277641 12398210948999902732708231)
    ·
      refine ⟨18597316423499854099062347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12398210948999902732708231 18597316423499854099062347)
      ·
        refine ⟨27895974635249781148593521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18597316423499854099062347 27895974635249781148593521)
        ·
          refine ⟨20921980976437335861445141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27895974635249781148593521 20921980976437335861445141)
          ·
            refine ⟨980717858270500118505241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 20921980976437335861445141 980717858270500118505241)
            ·
              refine ⟨735538393702875088878931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 980717858270500118505241 735538393702875088878931)
              ·
                refine ⟨1103307590554312633318397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 735538393702875088878931 1103307590554312633318397)
                ·
                  refine ⟨413740346457867237494399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1103307590554312633318397 413740346457867237494399)
                  ·
                    rfl

theorem cell20_906476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 3].length) (baseStart_906476 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_906476 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_906476 prefixEnd_906476 := by exact prefixLift 906476
  have htrace : WordTrace (prefixWord ++ tailWord_906476) baseStart_906476 baseEnd_906476 := by
    simpa [prefixWord, tailWord_906476, baseEnd_906476] using wordTrace_append hprefix tailTrace_906476
  have hstable : (prefixWord ++ tailWord_906476).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906476).length < 2 ^ (prefixWord ++ tailWord_906476).sum := by decide
  have hdescent : baseEnd_906476 < baseStart_906476 := by decide
  rcases family_descends (prefixWord ++ tailWord_906476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906528 : List Nat := [2, 1, 1, 5, 3, 2, 1, 5]
def baseStart_906528 : Nat := 118140960795 + 906528 * 2 ^ 59
def prefixEnd_906528 : Nat := 4983230072969 + 3 ^ 40 * 906528 * 2
def baseEnd_906528 : Nat := 137921360224928722586951

theorem tailTrace_906528 : CollatzResearch.WordTrace tailWord_906528 prefixEnd_906528 137921360224928722586951 := by
  unfold tailWord_906528
  simp only [CollatzResearch.WordTrace]
  refine ⟨16531896229905676750724119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22042528306540902334298825 16531896229905676750724119)
  ·
    refine ⟨24797844344858515126086179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16531896229905676750724119 24797844344858515126086179)
    ·
      refine ⟨37196766517287772689129269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24797844344858515126086179 37196766517287772689129269)
      ·
        refine ⟨3487196860995728689605869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37196766517287772689129269 3487196860995728689605869)
        ·
          refine ⟨1307698822873398258602201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3487196860995728689605869 1307698822873398258602201)
          ·
            refine ⟨980774117155048693951651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1307698822873398258602201 980774117155048693951651)
            ·
              refine ⟨1471161175732573040927477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 980774117155048693951651 1471161175732573040927477)
              ·
                refine ⟨137921360224928722586951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1471161175732573040927477 137921360224928722586951)
                ·
                  rfl

theorem cell20_906528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 1, 5].length) (baseStart_906528 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_906528 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_906528 prefixEnd_906528 := by exact prefixLift 906528
  have htrace : WordTrace (prefixWord ++ tailWord_906528) baseStart_906528 baseEnd_906528 := by
    simpa [prefixWord, tailWord_906528, baseEnd_906528] using wordTrace_append hprefix tailTrace_906528
  have hstable : (prefixWord ++ tailWord_906528).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906528).length < 2 ^ (prefixWord ++ tailWord_906528).sum := by decide
  have hdescent : baseEnd_906528 < baseStart_906528 := by decide
  rcases family_descends (prefixWord ++ tailWord_906528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906559 : List Nat := [1, 1, 2, 2, 4, 3, 2, 3, 2]
def baseStart_906559 : Nat := 118140960795 + 906559 * 2 ^ 59
def prefixEnd_906559 : Nat := 4983230072969 + 3 ^ 40 * 906559 * 2
def baseEnd_906559 : Nat := 413778229919487837727393

theorem tailTrace_906559 : CollatzResearch.WordTrace tailWord_906559 prefixEnd_906559 413778229919487837727393 := by
  unfold tailWord_906559
  simp only [CollatzResearch.WordTrace]
  refine ⟨33064923122699045795826731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22043282081799363863884487 33064923122699045795826731)
  ·
    refine ⟨49597384684048568693740097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33064923122699045795826731 49597384684048568693740097)
    ·
      refine ⟨37198038513036426520305073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49597384684048568693740097 37198038513036426520305073)
      ·
        refine ⟨27898528884777319890228805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37198038513036426520305073 27898528884777319890228805)
        ·
          refine ⟨5230974165895747479417901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27898528884777319890228805 5230974165895747479417901)
          ·
            refine ⟨1961615312210905304781713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5230974165895747479417901 1961615312210905304781713)
            ·
              refine ⟨1471211484158178978586285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1961615312210905304781713 1471211484158178978586285)
              ·
                refine ⟨551704306559317116969857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1471211484158178978586285 551704306559317116969857)
                ·
                  refine ⟨413778229919487837727393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 551704306559317116969857 413778229919487837727393)
                  ·
                    rfl

theorem cell20_906559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 2, 3, 2].length) (baseStart_906559 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_906559 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_906559 prefixEnd_906559 := by exact prefixLift 906559
  have htrace : WordTrace (prefixWord ++ tailWord_906559) baseStart_906559 baseEnd_906559 := by
    simpa [prefixWord, tailWord_906559, baseEnd_906559] using wordTrace_append hprefix tailTrace_906559
  have hstable : (prefixWord ++ tailWord_906559).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906559).length < 2 ^ (prefixWord ++ tailWord_906559).sum := by decide
  have hdescent : baseEnd_906559 < baseStart_906559 := by decide
  rcases family_descends (prefixWord ++ tailWord_906559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906580 : List Nat := [2, 4, 1, 1, 2, 1, 4, 1, 4]
def baseStart_906580 : Nat := 118140960795 + 906580 * 2 ^ 59
def prefixEnd_906580 : Nat := 4983230072969 + 3 ^ 40 * 906580 * 2
def baseEnd_906580 : Nat := 413787814891705098027307

theorem tailTrace_906580 : CollatzResearch.WordTrace tailWord_906580 prefixEnd_906580 413787814891705098027307 := by
  unfold tailWord_906580
  simp only [CollatzResearch.WordTrace]
  refine ⟨16532844527811483191170597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22043792703748644254894129 16532844527811483191170597)
  ·
    refine ⟨3099908348964653098344487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16532844527811483191170597 3099908348964653098344487)
    ·
      refine ⟨4649862523446979647516731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3099908348964653098344487 4649862523446979647516731)
      ·
        refine ⟨6974793785170469471275097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4649862523446979647516731 6974793785170469471275097)
        ·
          refine ⟨5231095338877852103456323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6974793785170469471275097 5231095338877852103456323)
          ·
            refine ⟨7846643008316778155184485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5231095338877852103456323 7846643008316778155184485)
            ·
              refine ⟨1471245564059395904097091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7846643008316778155184485 1471245564059395904097091)
              ·
                refine ⟨2206868346089093856145637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1471245564059395904097091 2206868346089093856145637)
                ·
                  refine ⟨413787814891705098027307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2206868346089093856145637 413787814891705098027307)
                  ·
                    rfl

theorem cell20_906580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_906580 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_906580 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_906580 prefixEnd_906580 := by exact prefixLift 906580
  have htrace : WordTrace (prefixWord ++ tailWord_906580) baseStart_906580 baseEnd_906580 := by
    simpa [prefixWord, tailWord_906580, baseEnd_906580] using wordTrace_append hprefix tailTrace_906580
  have hstable : (prefixWord ++ tailWord_906580).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906580).length < 2 ^ (prefixWord ++ tailWord_906580).sum := by decide
  have hdescent : baseEnd_906580 < baseStart_906580 := by decide
  rcases family_descends (prefixWord ++ tailWord_906580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906604 : List Nat := [2, 2, 1, 1, 5, 3, 2, 4]
def baseStart_906604 : Nat := 118140960795 + 906604 * 2 ^ 59
def prefixEnd_906604 : Nat := 4983230072969 + 3 ^ 40 * 906604 * 2
def baseEnd_906604 : Nat := 137932923048555893742403

theorem tailTrace_906604 : CollatzResearch.WordTrace tailWord_906604 prefixEnd_906604 137932923048555893742403 := by
  unfold tailWord_906604
  simp only [CollatzResearch.WordTrace]
  refine ⟨16533282203768009240607433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22044376271690678987476577 16533282203768009240607433)
  ·
    refine ⟨12399961652826006930455575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16533282203768009240607433 12399961652826006930455575)
    ·
      refine ⟨18599942479239010395683363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12399961652826006930455575 18599942479239010395683363)
      ·
        refine ⟨27899913718858515593525045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18599942479239010395683363 27899913718858515593525045)
        ·
          refine ⟨2615616911142985836892973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27899913718858515593525045 2615616911142985836892973)
          ·
            refine ⟨980856341678619688834865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2615616911142985836892973 980856341678619688834865)
            ·
              refine ⟨735642256258964766626149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 980856341678619688834865 735642256258964766626149)
              ·
                refine ⟨137932923048555893742403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 735642256258964766626149 137932923048555893742403)
                ·
                  rfl

theorem cell20_906604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 2, 4].length) (baseStart_906604 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_906604 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_906604 prefixEnd_906604 := by exact prefixLift 906604
  have htrace : WordTrace (prefixWord ++ tailWord_906604) baseStart_906604 baseEnd_906604 := by
    simpa [prefixWord, tailWord_906604, baseEnd_906604] using wordTrace_append hprefix tailTrace_906604
  have hstable : (prefixWord ++ tailWord_906604).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906604).length < 2 ^ (prefixWord ++ tailWord_906604).sum := by decide
  have hdescent : baseEnd_906604 < baseStart_906604 := by decide
  rcases family_descends (prefixWord ++ tailWord_906604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906608 : List Nat := [2, 1, 1, 1, 4, 2, 3, 6]
def baseStart_906608 : Nat := 118140960795 + 906608 * 2 ^ 59
def prefixEnd_906608 : Nat := 4983230072969 + 3 ^ 40 * 906608 * 2
def baseEnd_906608 : Nat := 137933531618220481697953

theorem tailTrace_906608 : CollatzResearch.WordTrace tailWord_906608 prefixEnd_906608 137933531618220481697953 := by
  unfold tailWord_906608
  simp only [CollatzResearch.WordTrace]
  refine ⟨16533355149760763582180239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22044473533014351442906985 16533355149760763582180239)
  ·
    refine ⟨24800032724641145373270359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16533355149760763582180239 24800032724641145373270359)
    ·
      refine ⟨37200049086961718059905539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24800032724641145373270359 37200049086961718059905539)
      ·
        refine ⟨55800073630442577089858309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37200049086961718059905539 55800073630442577089858309)
        ·
          refine ⟨10462513805707983204348433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55800073630442577089858309 10462513805707983204348433)
          ·
            refine ⟨7846885354280987403261325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10462513805707983204348433 7846885354280987403261325)
            ·
              refine ⟨2942582007855370276222997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7846885354280987403261325 2942582007855370276222997)
              ·
                refine ⟨137933531618220481697953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2942582007855370276222997 137933531618220481697953)
                ·
                  rfl

theorem cell20_906608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 6].length) (baseStart_906608 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_906608 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_906608 prefixEnd_906608 := by exact prefixLift 906608
  have htrace : WordTrace (prefixWord ++ tailWord_906608) baseStart_906608 baseEnd_906608 := by
    simpa [prefixWord, tailWord_906608, baseEnd_906608] using wordTrace_append hprefix tailTrace_906608
  have hstable : (prefixWord ++ tailWord_906608).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906608).length < 2 ^ (prefixWord ++ tailWord_906608).sum := by decide
  have hdescent : baseEnd_906608 < baseStart_906608 := by decide
  rcases family_descends (prefixWord ++ tailWord_906608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906615 : List Nat := [1, 1, 3, 1, 1, 2, 3, 1, 7]
def baseStart_906615 : Nat := 118140960795 + 906615 * 2 ^ 59
def prefixEnd_906615 : Nat := 4983230072969 + 3 ^ 40 * 906615 * 2
def baseEnd_906615 : Nat := 413803789845400531860497

theorem tailTrace_906615 : CollatzResearch.WordTrace tailWord_906615 prefixEnd_906615 413803789845400531860497 := by
  unfold tailWord_906615
  simp only [CollatzResearch.WordTrace]
  refine ⟨33066965610496167359865299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22044643740330778239910199 33066965610496167359865299)
  ·
    refine ⟨49600448415744251039797949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33066965610496167359865299 49600448415744251039797949)
    ·
      refine ⟨18600168155904094139924231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49600448415744251039797949 18600168155904094139924231)
      ·
        refine ⟨27900252233856141209886347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18600168155904094139924231 27900252233856141209886347)
        ·
          refine ⟨41850378350784211814829521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27900252233856141209886347 41850378350784211814829521)
          ·
            refine ⟨31387783763088158861122141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41850378350784211814829521 31387783763088158861122141)
            ·
              refine ⟨11770418911158059572920803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31387783763088158861122141 11770418911158059572920803)
              ·
                refine ⟨17655628366737089359381205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11770418911158059572920803 17655628366737089359381205)
                ·
                  refine ⟨413803789845400531860497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17655628366737089359381205 413803789845400531860497)
                  ·
                    rfl

theorem cell20_906615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 1, 7].length) (baseStart_906615 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_906615 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_906615 prefixEnd_906615 := by exact prefixLift 906615
  have htrace : WordTrace (prefixWord ++ tailWord_906615) baseStart_906615 baseEnd_906615 := by
    simpa [prefixWord, tailWord_906615, baseEnd_906615] using wordTrace_append hprefix tailTrace_906615
  have hstable : (prefixWord ++ tailWord_906615).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906615).length < 2 ^ (prefixWord ++ tailWord_906615).sum := by decide
  have hdescent : baseEnd_906615 < baseStart_906615 := by decide
  rcases family_descends (prefixWord ++ tailWord_906615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906632 : List Nat := [2, 1, 3, 3, 1, 2, 2, 1, 5]
def baseStart_906632 : Nat := 118140960795 + 906632 * 2 ^ 59
def prefixEnd_906632 : Nat := 4983230072969 + 3 ^ 40 * 906632 * 2
def baseEnd_906632 : Nat := 413811549108624028293761

theorem tailTrace_906632 : CollatzResearch.WordTrace tailWord_906632 prefixEnd_906632 413811549108624028293761 := by
  unfold tailWord_906632
  simp only [CollatzResearch.WordTrace]
  refine ⟨16533792825717289631617075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22045057100956386175489433 16533792825717289631617075)
  ·
    refine ⟨24800689238575934447425613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16533792825717289631617075 24800689238575934447425613)
    ·
      refine ⟨9300258464465975417784605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24800689238575934447425613 9300258464465975417784605)
      ·
        refine ⟨3487596924174740781669227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9300258464465975417784605 3487596924174740781669227)
        ·
          refine ⟨5231395386262111172503841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3487596924174740781669227 5231395386262111172503841)
          ·
            refine ⟨3923546539696583379377881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5231395386262111172503841 3923546539696583379377881)
            ·
              refine ⟨2942659904772437534533411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3923546539696583379377881 2942659904772437534533411)
              ·
                refine ⟨4413989857158656301800117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2942659904772437534533411 4413989857158656301800117)
                ·
                  refine ⟨413811549108624028293761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4413989857158656301800117 413811549108624028293761)
                  ·
                    rfl

theorem cell20_906632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 1, 5].length) (baseStart_906632 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_906632 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_906632 prefixEnd_906632 := by exact prefixLift 906632
  have htrace : WordTrace (prefixWord ++ tailWord_906632) baseStart_906632 baseEnd_906632 := by
    simpa [prefixWord, tailWord_906632, baseEnd_906632] using wordTrace_append hprefix tailTrace_906632
  have hstable : (prefixWord ++ tailWord_906632).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906632).length < 2 ^ (prefixWord ++ tailWord_906632).sum := by decide
  have hdescent : baseEnd_906632 < baseStart_906632 := by decide
  rcases family_descends (prefixWord ++ tailWord_906632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906635 : List Nat := [1, 1, 1, 1, 4, 3, 5, 2, 2]
def baseStart_906635 : Nat := 118140960795 + 906635 * 2 ^ 59
def prefixEnd_906635 : Nat := 4983230072969 + 3 ^ 40 * 906635 * 2
def baseEnd_906635 : Nat := 413812918390369351193749

theorem tailTrace_906635 : CollatzResearch.WordTrace tailWord_906635 prefixEnd_906635 413812918390369351193749 := by
  unfold tailWord_906635
  simp only [CollatzResearch.WordTrace]
  refine ⟨33067695070423710775593359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22045130046949140517062239 33067695070423710775593359)
  ·
    refine ⟨49601542605635566163390039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33067695070423710775593359 49601542605635566163390039)
    ·
      refine ⟨74402313908453349245085059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49601542605635566163390039 74402313908453349245085059)
      ·
        refine ⟨111603470862680023867627589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74402313908453349245085059 111603470862680023867627589)
        ·
          refine ⟨20925650786752504475180173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 111603470862680023867627589 20925650786752504475180173)
          ·
            refine ⟨7847119045032189178192565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20925650786752504475180173 7847119045032189178192565)
            ·
              refine ⟨735667410471767735455553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7847119045032189178192565 735667410471767735455553)
              ·
                refine ⟨551750557853825801591665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 735667410471767735455553 551750557853825801591665)
                ·
                  refine ⟨413812918390369351193749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 551750557853825801591665 413812918390369351193749)
                  ·
                    rfl

theorem cell20_906635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 5, 2, 2].length) (baseStart_906635 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_906635 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_906635 prefixEnd_906635 := by exact prefixLift 906635
  have htrace : WordTrace (prefixWord ++ tailWord_906635) baseStart_906635 baseEnd_906635 := by
    simpa [prefixWord, tailWord_906635, baseEnd_906635] using wordTrace_append hprefix tailTrace_906635
  have hstable : (prefixWord ++ tailWord_906635).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906635).length < 2 ^ (prefixWord ++ tailWord_906635).sum := by decide
  have hdescent : baseEnd_906635 < baseStart_906635 := by decide
  rcases family_descends (prefixWord ++ tailWord_906635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906649 : List Nat := [1, 2, 1, 2, 1, 5, 4, 1, 3]
def baseStart_906649 : Nat := 118140960795 + 906649 * 2 ^ 59
def prefixEnd_906649 : Nat := 4983230072969 + 3 ^ 40 * 906649 * 2
def baseEnd_906649 : Nat := 413819308371847524727025

theorem tailTrace_906649 : CollatzResearch.WordTrace tailWord_906649 prefixEnd_906649 413819308371847524727025 := by
  unfold tailWord_906649
  simp only [CollatzResearch.WordTrace]
  refine ⟨33068205692372991166603001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22045470461581994111068667 33068205692372991166603001)
  ·
    refine ⟨24801154269279743374952251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33068205692372991166603001 24801154269279743374952251)
    ·
      refine ⟨37201731403919615062428377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24801154269279743374952251 37201731403919615062428377)
      ·
        refine ⟨27901298552939711296821283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37201731403919615062428377 27901298552939711296821283)
        ·
          refine ⟨41851947829409566945231925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27901298552939711296821283 41851947829409566945231925)
          ·
            refine ⟨3923620109007146901115493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41851947829409566945231925 3923620109007146901115493)
            ·
              refine ⟨735678770438840043959155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3923620109007146901115493 735678770438840043959155)
              ·
                refine ⟨1103518155658260065938733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 735678770438840043959155 1103518155658260065938733)
                ·
                  refine ⟨413819308371847524727025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1103518155658260065938733 413819308371847524727025)
                  ·
                    rfl

theorem cell20_906649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 4, 1, 3].length) (baseStart_906649 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_906649 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_906649 prefixEnd_906649 := by exact prefixLift 906649
  have htrace : WordTrace (prefixWord ++ tailWord_906649) baseStart_906649 baseEnd_906649 := by
    simpa [prefixWord, tailWord_906649, baseEnd_906649] using wordTrace_append hprefix tailTrace_906649
  have hstable : (prefixWord ++ tailWord_906649).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906649).length < 2 ^ (prefixWord ++ tailWord_906649).sum := by decide
  have hdescent : baseEnd_906649 < baseStart_906649 := by decide
  rcases family_descends (prefixWord ++ tailWord_906649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906684 : List Nat := [2, 2, 2, 4, 10]
def baseStart_906684 : Nat := 118140960795 + 906684 * 2 ^ 59
def prefixEnd_906684 : Nat := 4983230072969 + 3 ^ 40 * 906684 * 2
def baseEnd_906684 : Nat := 5109077571920283439015

theorem tailTrace_906684 : CollatzResearch.WordTrace tailWord_906684 prefixEnd_906684 5109077571920283439015 := by
  unfold tailWord_906684
  simp only [CollatzResearch.WordTrace]
  refine ⟨16534741123623096072063553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22046321498164128096084737 16534741123623096072063553)
  ·
    refine ⟨12401055842717322054047665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16534741123623096072063553 12401055842717322054047665)
    ·
      refine ⟨9300791882037991540535749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12401055842717322054047665 9300791882037991540535749)
      ·
        refine ⟨1743898477882123413850453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9300791882037991540535749 1743898477882123413850453)
        ·
          refine ⟨5109077571920283439015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1743898477882123413850453 5109077571920283439015)
          ·
            rfl

theorem cell20_906684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 10].length) (baseStart_906684 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_906684 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_906684 prefixEnd_906684 := by exact prefixLift 906684
  have htrace : WordTrace (prefixWord ++ tailWord_906684) baseStart_906684 baseEnd_906684 := by
    simpa [prefixWord, tailWord_906684, baseEnd_906684] using wordTrace_append hprefix tailTrace_906684
  have hstable : (prefixWord ++ tailWord_906684).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906684).length < 2 ^ (prefixWord ++ tailWord_906684).sum := by decide
  have hdescent : baseEnd_906684 < baseStart_906684 := by decide
  rcases family_descends (prefixWord ++ tailWord_906684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906691 : List Nat := [1, 1, 1, 3, 1, 1, 4, 3, 5]
def baseStart_906691 : Nat := 118140960795 + 906691 * 2 ^ 59
def prefixEnd_906691 : Nat := 4983230072969 + 3 ^ 40 * 906691 * 2
def baseEnd_906691 : Nat := 413838478316282045326853

theorem tailTrace_906691 : CollatzResearch.WordTrace tailWord_906691 prefixEnd_906691 413838478316282045326853 := by
  unfold tailWord_906691
  simp only [CollatzResearch.WordTrace]
  refine ⟨33069737558220832339631927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22046491705480554893087951 33069737558220832339631927)
  ·
    refine ⟨49604606337331248509447891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33069737558220832339631927 49604606337331248509447891)
    ·
      refine ⟨74406909505996872764171837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49604606337331248509447891 74406909505996872764171837)
      ·
        refine ⟨27902591064748827286564439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74406909505996872764171837 27902591064748827286564439)
        ·
          refine ⟨41853886597123240929846659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27902591064748827286564439 41853886597123240929846659)
          ·
            refine ⟨62780829895684861394769989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41853886597123240929846659 62780829895684861394769989)
            ·
              refine ⟨11771405605440911511519373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62780829895684861394769989 11771405605440911511519373)
              ·
                refine ⟨4414277102040341816819765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11771405605440911511519373 4414277102040341816819765)
                ·
                  refine ⟨413838478316282045326853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4414277102040341816819765 413838478316282045326853)
                  ·
                    rfl

theorem cell20_906691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 3, 5].length) (baseStart_906691 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_906691 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_906691 prefixEnd_906691 := by exact prefixLift 906691
  have htrace : WordTrace (prefixWord ++ tailWord_906691) baseStart_906691 baseEnd_906691 := by
    simpa [prefixWord, tailWord_906691, baseEnd_906691] using wordTrace_append hprefix tailTrace_906691
  have hstable : (prefixWord ++ tailWord_906691).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906691).length < 2 ^ (prefixWord ++ tailWord_906691).sum := by decide
  have hdescent : baseEnd_906691 < baseStart_906691 := by decide
  rcases family_descends (prefixWord ++ tailWord_906691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906742 : List Nat := [5, 1, 1, 1, 2, 4, 1, 2, 3]
def baseStart_906742 : Nat := 118140960795 + 906742 * 2 ^ 59
def prefixEnd_906742 : Nat := 4983230072969 + 3 ^ 40 * 906742 * 2
def baseEnd_906742 : Nat := 413861756105952534626645

theorem tailTrace_906742 : CollatzResearch.WordTrace tailWord_906742 prefixEnd_906742 413861756105952534626645 := by
  unfold tailWord_906742
  simp only [CollatzResearch.WordTrace]
  refine ⟨2066974855064754253108655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22047731787357378699825653 2066974855064754253108655)
  ·
    refine ⟨3100462282597131379662983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2066974855064754253108655 3100462282597131379662983)
    ·
      refine ⟨4650693423895697069494475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3100462282597131379662983 4650693423895697069494475)
      ·
        refine ⟨6976040135843545604241713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4650693423895697069494475 6976040135843545604241713)
        ·
          refine ⟨5232030101882659203181285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6976040135843545604241713 5232030101882659203181285)
          ·
            refine ⟨981005644102998600596491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5232030101882659203181285 981005644102998600596491)
            ·
              refine ⟨1471508466154497900894737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 981005644102998600596491 1471508466154497900894737)
              ·
                refine ⟨1103631349615873425671053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1471508466154497900894737 1103631349615873425671053)
                ·
                  refine ⟨413861756105952534626645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1103631349615873425671053 413861756105952534626645)
                  ·
                    rfl

theorem cell20_906742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 1, 2, 3].length) (baseStart_906742 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_906742 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_906742 prefixEnd_906742 := by exact prefixLift 906742
  have htrace : WordTrace (prefixWord ++ tailWord_906742) baseStart_906742 baseEnd_906742 := by
    simpa [prefixWord, tailWord_906742, baseEnd_906742] using wordTrace_append hprefix tailTrace_906742
  have hstable : (prefixWord ++ tailWord_906742).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906742).length < 2 ^ (prefixWord ++ tailWord_906742).sum := by decide
  have hdescent : baseEnd_906742 < baseStart_906742 := by decide
  rcases family_descends (prefixWord ++ tailWord_906742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906784 : List Nat := [2, 1, 1, 6, 1, 1, 1, 2, 5]
def baseStart_906784 : Nat := 118140960795 + 906784 * 2 ^ 59
def prefixEnd_906784 : Nat := 4983230072969 + 3 ^ 40 * 906784 * 2
def baseEnd_906784 : Nat := 413880926050387055226473

theorem tailTrace_906784 : CollatzResearch.WordTrace tailWord_906784 prefixEnd_906784 413880926050387055226473 := by
  unfold tailWord_906784
  simp only [CollatzResearch.WordTrace]
  refine ⟨16536564773441954611383703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22048753031255939481844937 16536564773441954611383703)
  ·
    refine ⟨24804847160162931917075555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16536564773441954611383703 24804847160162931917075555)
    ·
      refine ⟨37207270740244397875613333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24804847160162931917075555 37207270740244397875613333)
      ·
        refine ⟨1744090815948956150419375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 37207270740244397875613333 1744090815948956150419375)
        ·
          refine ⟨2616136223923434225629063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1744090815948956150419375 2616136223923434225629063)
          ·
            refine ⟨3924204335885151338443595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2616136223923434225629063 3924204335885151338443595)
            ·
              refine ⟨5886306503827727007665393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3924204335885151338443595 5886306503827727007665393)
              ·
                refine ⟨4414729877870795255749045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5886306503827727007665393 4414729877870795255749045)
                ·
                  refine ⟨413880926050387055226473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4414729877870795255749045 413880926050387055226473)
                  ·
                    rfl

theorem cell20_906784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 2, 5].length) (baseStart_906784 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_906784 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_906784 prefixEnd_906784 := by exact prefixLift 906784
  have htrace : WordTrace (prefixWord ++ tailWord_906784) baseStart_906784 baseEnd_906784 := by
    simpa [prefixWord, tailWord_906784, baseEnd_906784] using wordTrace_append hprefix tailTrace_906784
  have hstable : (prefixWord ++ tailWord_906784).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906784).length < 2 ^ (prefixWord ++ tailWord_906784).sum := by decide
  have hdescent : baseEnd_906784 < baseStart_906784 := by decide
  rcases family_descends (prefixWord ++ tailWord_906784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906808 : List Nat := [2, 1, 2, 1, 4, 4, 1, 1, 4]
def baseStart_906808 : Nat := 118140960795 + 906808 * 2 ^ 59
def prefixEnd_906808 : Nat := 4983230072969 + 3 ^ 40 * 906808 * 2
def baseEnd_906808 : Nat := 413891880304349638426375

theorem tailTrace_906808 : CollatzResearch.WordTrace tailWord_906808 prefixEnd_906808 413891880304349638426375 := by
  unfold tailWord_906808
  simp only [CollatzResearch.WordTrace]
  refine ⟨16537002449398480660820539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22049336599197974214427385 16537002449398480660820539)
  ·
    refine ⟨24805503674097720991230809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16537002449398480660820539 24805503674097720991230809)
    ·
      refine ⟨18604127755573290743423107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24805503674097720991230809 18604127755573290743423107)
      ·
        refine ⟨27906191633359936115134661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18604127755573290743423107 27906191633359936115134661)
        ·
          refine ⟨5232410931254988021587749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27906191633359936115134661 5232410931254988021587749)
          ·
            refine ⟨981077049610310254047703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5232410931254988021587749 981077049610310254047703)
            ·
              refine ⟨1471615574415465381071555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 981077049610310254047703 1471615574415465381071555)
              ·
                refine ⟨2207423361623198071607333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1471615574415465381071555 2207423361623198071607333)
                ·
                  refine ⟨413891880304349638426375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2207423361623198071607333 413891880304349638426375)
                  ·
                    rfl

theorem cell20_906808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 1, 1, 4].length) (baseStart_906808 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_906808 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_906808 prefixEnd_906808 := by exact prefixLift 906808
  have htrace : WordTrace (prefixWord ++ tailWord_906808) baseStart_906808 baseEnd_906808 := by
    simpa [prefixWord, tailWord_906808, baseEnd_906808] using wordTrace_append hprefix tailTrace_906808
  have hstable : (prefixWord ++ tailWord_906808).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906808).length < 2 ^ (prefixWord ++ tailWord_906808).sum := by decide
  have hdescent : baseEnd_906808 < baseStart_906808 := by decide
  rcases family_descends (prefixWord ++ tailWord_906808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906836 : List Nat := [2, 4, 1, 1, 1, 2, 1, 8]
def baseStart_906836 : Nat := 118140960795 + 906836 * 2 ^ 59
def prefixEnd_906836 : Nat := 4983230072969 + 3 ^ 40 * 906836 * 2
def baseEnd_906836 : Nat := 137968220089101995164309

theorem tailTrace_906836 : CollatzResearch.WordTrace tailWord_906836 prefixEnd_906836 137968220089101995164309 := by
  unfold tailWord_906836
  simp only [CollatzResearch.WordTrace]
  refine ⟨16537513071347761051830181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22050017428463681402440241 16537513071347761051830181)
  ·
    refine ⟨3100783700877705197218159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16537513071347761051830181 3100783700877705197218159)
    ·
      refine ⟨4651175551316557795827239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3100783700877705197218159 4651175551316557795827239)
      ·
        refine ⟨6976763326974836693740859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4651175551316557795827239 6976763326974836693740859)
        ·
          refine ⟨10465144990462255040611289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6976763326974836693740859 10465144990462255040611289)
          ·
            refine ⟨7848858742846691280458467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10465144990462255040611289 7848858742846691280458467)
            ·
              refine ⟨11773288114270036920687701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7848858742846691280458467 11773288114270036920687701)
              ·
                refine ⟨137968220089101995164309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11773288114270036920687701 137968220089101995164309)
                ·
                  rfl

theorem cell20_906836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 8].length) (baseStart_906836 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_906836 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_906836 prefixEnd_906836 := by exact prefixLift 906836
  have htrace : WordTrace (prefixWord ++ tailWord_906836) baseStart_906836 baseEnd_906836 := by
    simpa [prefixWord, tailWord_906836, baseEnd_906836] using wordTrace_append hprefix tailTrace_906836
  have hstable : (prefixWord ++ tailWord_906836).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906836).length < 2 ^ (prefixWord ++ tailWord_906836).sum := by decide
  have hdescent : baseEnd_906836 < baseStart_906836 := by decide
  rcases family_descends (prefixWord ++ tailWord_906836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906870 : List Nat := [5, 1, 1, 2, 2, 3, 1, 5]
def baseStart_906870 : Nat := 118140960795 + 906870 * 2 ^ 59
def prefixEnd_906870 : Nat := 4983230072969 + 3 ^ 40 * 906870 * 2
def baseEnd_906870 : Nat := 137973392931250992786485

theorem tailTrace_906870 : CollatzResearch.WordTrace tailWord_906870 prefixEnd_906870 137973392931250992786485 := by
  unfold tailWord_906870
  simp only [CollatzResearch.WordTrace]
  refine ⟨2067266639035771619399879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22050844149714897273598709 2067266639035771619399879)
  ·
    refine ⟨3100899958553657429099819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2067266639035771619399879 3100899958553657429099819)
    ·
      refine ⟨4651349937830486143649729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3100899958553657429099819 4651349937830486143649729)
      ·
        refine ⟨3488512453372864607737297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4651349937830486143649729 3488512453372864607737297)
        ·
          refine ⟨2616384340029648455802973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3488512453372864607737297 2616384340029648455802973)
          ·
            refine ⟨981144127511118170926115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2616384340029648455802973 981144127511118170926115)
            ·
              refine ⟨1471716191266677256389173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 981144127511118170926115 1471716191266677256389173)
              ·
                refine ⟨137973392931250992786485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1471716191266677256389173 137973392931250992786485)
                ·
                  rfl

theorem cell20_906870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 1, 5].length) (baseStart_906870 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_906870 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_906870 prefixEnd_906870 := by exact prefixLift 906870
  have htrace : WordTrace (prefixWord ++ tailWord_906870) baseStart_906870 baseEnd_906870 := by
    simpa [prefixWord, tailWord_906870, baseEnd_906870] using wordTrace_append hprefix tailTrace_906870
  have hstable : (prefixWord ++ tailWord_906870).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906870).length < 2 ^ (prefixWord ++ tailWord_906870).sum := by decide
  have hdescent : baseEnd_906870 < baseStart_906870 := by decide
  rcases family_descends (prefixWord ++ tailWord_906870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906884 : List Nat := [2, 3, 2, 1, 4, 1, 1, 2, 4]
def baseStart_906884 : Nat := 118140960795 + 906884 * 2 ^ 59
def prefixEnd_906884 : Nat := 4983230072969 + 3 ^ 40 * 906884 * 2
def baseEnd_906884 : Nat := 413926568775231151892731

theorem tailTrace_906884 : CollatzResearch.WordTrace tailWord_906884 prefixEnd_906884 413926568775231151892731 := by
  unfold tailWord_906884
  simp only [CollatzResearch.WordTrace]
  refine ⟨16538388423260813150703853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22051184564347750867605137 16538388423260813150703853)
  ·
    refine ⟨6201895658722804931513945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16538388423260813150703853 6201895658722804931513945)
    ·
      refine ⟨4651421744042103698635459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6201895658722804931513945 4651421744042103698635459)
      ·
        refine ⟨6977132616063155547953189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4651421744042103698635459 6977132616063155547953189)
        ·
          refine ⟨1308212365511841665241223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6977132616063155547953189 1308212365511841665241223)
          ·
            refine ⟨1962318548267762497861835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1308212365511841665241223 1962318548267762497861835)
            ·
              refine ⟨2943477822401643746792753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1962318548267762497861835 2943477822401643746792753)
              ·
                refine ⟨2207608366801232810094565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2943477822401643746792753 2207608366801232810094565)
                ·
                  refine ⟨413926568775231151892731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2207608366801232810094565 413926568775231151892731)
                  ·
                    rfl

theorem cell20_906884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 2, 4].length) (baseStart_906884 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_906884 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_906884 prefixEnd_906884 := by exact prefixLift 906884
  have htrace : WordTrace (prefixWord ++ tailWord_906884) baseStart_906884 baseEnd_906884 := by
    simpa [prefixWord, tailWord_906884, baseEnd_906884] using wordTrace_append hprefix tailTrace_906884
  have hstable : (prefixWord ++ tailWord_906884).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906884).length < 2 ^ (prefixWord ++ tailWord_906884).sum := by decide
  have hdescent : baseEnd_906884 < baseStart_906884 := by decide
  rcases family_descends (prefixWord ++ tailWord_906884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906911 : List Nat := [1, 1, 2, 7, 2, 1, 1, 2, 3]
def baseStart_906911 : Nat := 118140960795 + 906911 * 2 ^ 59
def prefixEnd_906911 : Nat := 4983230072969 + 3 ^ 40 * 906911 * 2
def baseEnd_906911 : Nat := 413938892310939057992621

theorem tailTrace_906911 : CollatzResearch.WordTrace tailWord_906911 prefixEnd_906911 413938892310939057992621 := by
  unfold tailWord_906911
  simp only [CollatzResearch.WordTrace]
  refine ⟨33077761617423809912640587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22051841078282539941760391 33077761617423809912640587)
  ·
    refine ⟨49616642426135714868960881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33077761617423809912640587 49616642426135714868960881)
    ·
      refine ⟨37212481819601786151720661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49616642426135714868960881 37212481819601786151720661)
      ·
        refine ⟨872167542646916862930953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 37212481819601786151720661 872167542646916862930953)
        ·
          refine ⟨654125656985187647198215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 872167542646916862930953 654125656985187647198215)
          ·
            refine ⟨981188485477781470797323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 654125656985187647198215 981188485477781470797323)
            ·
              refine ⟨1471782728216672206195985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 981188485477781470797323 1471782728216672206195985)
              ·
                refine ⟨1103837046162504154646989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1471782728216672206195985 1103837046162504154646989)
                ·
                  refine ⟨413938892310939057992621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1103837046162504154646989 413938892310939057992621)
                  ·
                    rfl

theorem cell20_906911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 1, 2, 3].length) (baseStart_906911 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_906911 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_906911 prefixEnd_906911 := by exact prefixLift 906911
  have htrace : WordTrace (prefixWord ++ tailWord_906911) baseStart_906911 baseEnd_906911 := by
    simpa [prefixWord, tailWord_906911, baseEnd_906911] using wordTrace_append hprefix tailTrace_906911
  have hstable : (prefixWord ++ tailWord_906911).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906911).length < 2 ^ (prefixWord ++ tailWord_906911).sum := by decide
  have hdescent : baseEnd_906911 < baseStart_906911 := by decide
  rcases family_descends (prefixWord ++ tailWord_906911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906912 : List Nat := [2, 1, 1, 4, 3, 2, 7]
def baseStart_906912 : Nat := 118140960795 + 906912 * 2 ^ 59
def prefixEnd_906912 : Nat := 4983230072969 + 3 ^ 40 * 906912 * 2
def baseEnd_906912 : Nat := 45993260970909722106587

theorem tailTrace_906912 : CollatzResearch.WordTrace tailWord_906912 prefixEnd_906912 45993260970909722106587 := by
  unfold tailWord_906912
  simp only [CollatzResearch.WordTrace]
  refine ⟨16538899045210093541713495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22051865393613458055617993 16538899045210093541713495)
  ·
    refine ⟨24808348567815140312570243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16538899045210093541713495 24808348567815140312570243)
    ·
      refine ⟨37212522851722710468855365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24808348567815140312570243 37212522851722710468855365)
      ·
        refine ⟨6977348034698008212910381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37212522851722710468855365 6977348034698008212910381)
        ·
          refine ⟨2616505513011753079841393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6977348034698008212910381 2616505513011753079841393)
          ·
            refine ⟨1962379134758814809881045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2616505513011753079841393 1962379134758814809881045)
            ·
              refine ⟨45993260970909722106587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1962379134758814809881045 45993260970909722106587)
              ·
                rfl

theorem cell20_906912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 7].length) (baseStart_906912 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_906912 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_906912 prefixEnd_906912 := by exact prefixLift 906912
  have htrace : WordTrace (prefixWord ++ tailWord_906912) baseStart_906912 baseEnd_906912 := by
    simpa [prefixWord, tailWord_906912, baseEnd_906912] using wordTrace_append hprefix tailTrace_906912
  have hstable : (prefixWord ++ tailWord_906912).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906912).length < 2 ^ (prefixWord ++ tailWord_906912).sum := by decide
  have hdescent : baseEnd_906912 < baseStart_906912 := by decide
  rcases family_descends (prefixWord ++ tailWord_906912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906956 : List Nat := [2, 2, 1, 5, 2, 2, 1, 3, 2]
def baseStart_906956 : Nat := 118140960795 + 906956 * 2 ^ 59
def prefixEnd_906956 : Nat := 4983230072969 + 3 ^ 40 * 906956 * 2
def baseEnd_906956 : Nat := 413959431537118901492437

theorem tailTrace_906956 : CollatzResearch.WordTrace tailWord_906956 prefixEnd_906956 413959431537118901492437 := by
  unfold tailWord_906956
  simp only [CollatzResearch.WordTrace]
  refine ⟨16539701451130391299014361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22052935268173855065352481 16539701451130391299014361)
  ·
    refine ⟨12404776088347793474260771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16539701451130391299014361 12404776088347793474260771)
    ·
      refine ⟨18607164132521690211391157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12404776088347793474260771 18607164132521690211391157)
      ·
        refine ⟨1744421637423908457317921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18607164132521690211391157 1744421637423908457317921)
        ·
          refine ⟨1308316228067931342988441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1744421637423908457317921 1308316228067931342988441)
          ·
            refine ⟨981237171050948507241331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1308316228067931342988441 981237171050948507241331)
            ·
              refine ⟨1471855756576422760861997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 981237171050948507241331 1471855756576422760861997)
              ·
                refine ⟨551945908716158535323249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1471855756576422760861997 551945908716158535323249)
                ·
                  refine ⟨413959431537118901492437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 551945908716158535323249 413959431537118901492437)
                  ·
                    rfl

theorem cell20_906956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 1, 3, 2].length) (baseStart_906956 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_906956 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_906956 prefixEnd_906956 := by exact prefixLift 906956
  have htrace : WordTrace (prefixWord ++ tailWord_906956) baseStart_906956 baseEnd_906956 := by
    simpa [prefixWord, tailWord_906956, baseEnd_906956] using wordTrace_append hprefix tailTrace_906956
  have hstable : (prefixWord ++ tailWord_906956).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906956).length < 2 ^ (prefixWord ++ tailWord_906956).sum := by decide
  have hdescent : baseEnd_906956 < baseStart_906956 := by decide
  rcases family_descends (prefixWord ++ tailWord_906956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906973 : List Nat := [1, 4, 3, 3, 1, 1, 3, 2, 2]
def baseStart_906973 : Nat := 118140960795 + 906973 * 2 ^ 59
def prefixEnd_906973 : Nat := 4983230072969 + 3 ^ 40 * 906973 * 2
def baseEnd_906973 : Nat := 413967190800342397925701

theorem tailTrace_906973 : CollatzResearch.WordTrace tailWord_906973 prefixEnd_906973 413967190800342397925701 := by
  unfold tailWord_906973
  simp only [CollatzResearch.WordTrace]
  refine ⟨33080022943199194501397573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22053348628799463000931715 33080022943199194501397573)
  ·
    refine ⟨6202504301849848969012045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33080022943199194501397573 6202504301849848969012045)
    ·
      refine ⟨2325939113193693363379517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6202504301849848969012045 2325939113193693363379517)
      ·
        refine ⟨872227167447635011267319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2325939113193693363379517 872227167447635011267319)
        ·
          refine ⟨1308340751171452516900979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 872227167447635011267319 1308340751171452516900979)
          ·
            refine ⟨1962511126757178775351469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1308340751171452516900979 1962511126757178775351469)
            ·
              refine ⟨735941672533942040756801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1962511126757178775351469 735941672533942040756801)
              ·
                refine ⟨551956254400456530567601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 735941672533942040756801 551956254400456530567601)
                ·
                  refine ⟨413967190800342397925701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 551956254400456530567601 413967190800342397925701)
                  ·
                    rfl

theorem cell20_906973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 3, 2, 2].length) (baseStart_906973 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_906973 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_906973 prefixEnd_906973 := by exact prefixLift 906973
  have htrace : WordTrace (prefixWord ++ tailWord_906973) baseStart_906973 baseEnd_906973 := by
    simpa [prefixWord, tailWord_906973, baseEnd_906973] using wordTrace_append hprefix tailTrace_906973
  have hstable : (prefixWord ++ tailWord_906973).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906973).length < 2 ^ (prefixWord ++ tailWord_906973).sum := by decide
  have hdescent : baseEnd_906973 < baseStart_906973 := by decide
  rcases family_descends (prefixWord ++ tailWord_906973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_906977 : List Nat := [1, 2, 3, 1, 6, 1, 1, 1, 4]
def baseStart_906977 : Nat := 118140960795 + 906977 * 2 ^ 59
def prefixEnd_906977 : Nat := 4983230072969 + 3 ^ 40 * 906977 * 2
def baseEnd_906977 : Nat := 413969016509336161792351

theorem tailTrace_906977 : CollatzResearch.WordTrace tailWord_906977 prefixEnd_906977 413969016509336161792351 := by
  unfold tailWord_906977
  simp only [CollatzResearch.WordTrace]
  refine ⟨33080168835184703184543185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22053445890123135456362123 33080168835184703184543185)
  ·
    refine ⟨24810126626388527388407389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33080168835184703184543185 24810126626388527388407389)
    ·
      refine ⟨9303797484895697770652771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24810126626388527388407389 9303797484895697770652771)
      ·
        refine ⟨13955696227343546655979157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9303797484895697770652771 13955696227343546655979157)
        ·
          refine ⟨654173260656728749499023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 13955696227343546655979157 654173260656728749499023)
          ·
            refine ⟨981259890985093124248535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 654173260656728749499023 981259890985093124248535)
            ·
              refine ⟨1471889836477639686372803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 981259890985093124248535 1471889836477639686372803)
              ·
                refine ⟨2207834754716459529559205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1471889836477639686372803 2207834754716459529559205)
                ·
                  refine ⟨413969016509336161792351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2207834754716459529559205 413969016509336161792351)
                  ·
                    rfl

theorem cell20_906977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 1, 1, 4].length) (baseStart_906977 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_906977 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_906977 prefixEnd_906977 := by exact prefixLift 906977
  have htrace : WordTrace (prefixWord ++ tailWord_906977) baseStart_906977 baseEnd_906977 := by
    simpa [prefixWord, tailWord_906977, baseEnd_906977] using wordTrace_append hprefix tailTrace_906977
  have hstable : (prefixWord ++ tailWord_906977).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_906977).length < 2 ^ (prefixWord ++ tailWord_906977).sum := by decide
  have hdescent : baseEnd_906977 < baseStart_906977 := by decide
  rcases family_descends (prefixWord ++ tailWord_906977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907002 : List Nat := [3, 1, 1, 1, 1, 3, 1, 3, 6]
def baseStart_907002 : Nat := 118140960795 + 907002 * 2 ^ 59
def prefixEnd_907002 : Nat := 4983230072969 + 3 ^ 40 * 907002 * 2
def baseEnd_907002 : Nat := 413980427190547185958915

theorem tailTrace_907002 : CollatzResearch.WordTrace tailWord_907002 prefixEnd_907002 413980427190547185958915 := by
  unfold tailWord_907002
  simp only [CollatzResearch.WordTrace]
  refine ⟨8270270165023533113550815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22054053773396088302802173 8270270165023533113550815)
  ·
    refine ⟨12405405247535299670326223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8270270165023533113550815 12405405247535299670326223)
    ·
      refine ⟨18608107871302949505489335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12405405247535299670326223 18608107871302949505489335)
      ·
        refine ⟨27912161806954424258234003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18608107871302949505489335 27912161806954424258234003)
        ·
          refine ⟨41868242710431636387351005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27912161806954424258234003 41868242710431636387351005)
          ·
            refine ⟨15700591016411863645256627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41868242710431636387351005 15700591016411863645256627)
            ·
              refine ⟨23550886524617795467884941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15700591016411863645256627 23550886524617795467884941)
              ·
                refine ⟨8831582446731673300456853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23550886524617795467884941 8831582446731673300456853)
                ·
                  refine ⟨413980427190547185958915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8831582446731673300456853 413980427190547185958915)
                  ·
                    rfl

theorem cell20_907002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 3, 6].length) (baseStart_907002 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_907002 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_907002 prefixEnd_907002 := by exact prefixLift 907002
  have htrace : WordTrace (prefixWord ++ tailWord_907002) baseStart_907002 baseEnd_907002 := by
    simpa [prefixWord, tailWord_907002, baseEnd_907002] using wordTrace_append hprefix tailTrace_907002
  have hstable : (prefixWord ++ tailWord_907002).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907002).length < 2 ^ (prefixWord ++ tailWord_907002).sum := by decide
  have hdescent : baseEnd_907002 < baseStart_907002 := by decide
  rcases family_descends (prefixWord ++ tailWord_907002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907036 : List Nat := [2, 2, 3, 1, 1, 2, 3, 4, 2]
def baseStart_907036 : Nat := 118140960795 + 907036 * 2 ^ 59
def prefixEnd_907036 : Nat := 4983230072969 + 3 ^ 40 * 907036 * 2
def baseEnd_907036 : Nat := 413995945716994178825443

theorem tailTrace_907036 : CollatzResearch.WordTrace tailWord_907036 prefixEnd_907036 413995945716994178825443 := by
  unfold tailWord_907036
  simp only [CollatzResearch.WordTrace]
  refine ⟨16541160370985478130470481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22054880494647304173960641 16541160370985478130470481)
  ·
    refine ⟨12405870278239108597852861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16541160370985478130470481 12405870278239108597852861)
    ·
      refine ⟨4652201354339665724194823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12405870278239108597852861 4652201354339665724194823)
      ·
        refine ⟨6978302031509498586292235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4652201354339665724194823 6978302031509498586292235)
        ·
          refine ⟨10467453047264247879438353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6978302031509498586292235 10467453047264247879438353)
          ·
            refine ⟨7850589785448185909578765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10467453047264247879438353 7850589785448185909578765)
            ·
              refine ⟨2943971169543069716092037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7850589785448185909578765 2943971169543069716092037)
              ·
                refine ⟨551994594289325571767257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2943971169543069716092037 551994594289325571767257)
                ·
                  refine ⟨413995945716994178825443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 551994594289325571767257 413995945716994178825443)
                  ·
                    rfl

theorem cell20_907036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 4, 2].length) (baseStart_907036 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_907036 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_907036 prefixEnd_907036 := by exact prefixLift 907036
  have htrace : WordTrace (prefixWord ++ tailWord_907036) baseStart_907036 baseEnd_907036 := by
    simpa [prefixWord, tailWord_907036, baseEnd_907036] using wordTrace_append hprefix tailTrace_907036
  have hstable : (prefixWord ++ tailWord_907036).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907036).length < 2 ^ (prefixWord ++ tailWord_907036).sum := by decide
  have hdescent : baseEnd_907036 < baseStart_907036 := by decide
  rcases family_descends (prefixWord ++ tailWord_907036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907057 : List Nat := [1, 2, 2, 3, 2, 3, 1, 2, 4]
def baseStart_907057 : Nat := 118140960795 + 907057 * 2 ^ 59
def prefixEnd_907057 : Nat := 4983230072969 + 3 ^ 40 * 907057 * 2
def baseEnd_907057 : Nat := 414005530689211439125357

theorem tailTrace_907057 : CollatzResearch.WordTrace tailWord_907057 prefixEnd_907057 414005530689211439125357 := by
  unfold tailWord_907057
  simp only [CollatzResearch.WordTrace]
  refine ⟨33083086674894876847455425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22055391116596584564970283 33083086674894876847455425)
  ·
    refine ⟨24812315006171157635591569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33083086674894876847455425 24812315006171157635591569)
    ·
      refine ⟨18609236254628368226693677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24812315006171157635591569 18609236254628368226693677)
      ·
        refine ⟨6978463595485638085010129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18609236254628368226693677 6978463595485638085010129)
        ·
          refine ⟨5233847696614228563757597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6978463595485638085010129 5233847696614228563757597)
          ·
            refine ⟨1962692886230335711409099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5233847696614228563757597 1962692886230335711409099)
            ·
              refine ⟨2944039329345503567113649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1962692886230335711409099 2944039329345503567113649)
              ·
                refine ⟨2208029497009127675335237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2944039329345503567113649 2208029497009127675335237)
                ·
                  refine ⟨414005530689211439125357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2208029497009127675335237 414005530689211439125357)
                  ·
                    rfl

theorem cell20_907057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 2, 4].length) (baseStart_907057 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_907057 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_907057 prefixEnd_907057 := by exact prefixLift 907057
  have htrace : WordTrace (prefixWord ++ tailWord_907057) baseStart_907057 baseEnd_907057 := by
    simpa [prefixWord, tailWord_907057, baseEnd_907057] using wordTrace_append hprefix tailTrace_907057
  have hstable : (prefixWord ++ tailWord_907057).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907057).length < 2 ^ (prefixWord ++ tailWord_907057).sum := by decide
  have hdescent : baseEnd_907057 < baseStart_907057 := by decide
  rcases family_descends (prefixWord ++ tailWord_907057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907060 : List Nat := [2, 5, 1, 1, 2, 2, 3, 4]
def baseStart_907060 : Nat := 118140960795 + 907060 * 2 ^ 59
def prefixEnd_907060 : Nat := 4983230072969 + 3 ^ 40 * 907060 * 2
def baseEnd_907060 : Nat := 138002299990318920675115

theorem tailTrace_907060 : CollatzResearch.WordTrace tailWord_907060 prefixEnd_907060 138002299990318920675115 := by
  unfold tailWord_907060
  simp only [CollatzResearch.WordTrace]
  refine ⟨16541598046942004179907317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22055464062589338906543089 16541598046942004179907317)
  ·
    refine ⟨1550774816900812891866311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16541598046942004179907317 1550774816900812891866311)
    ·
      refine ⟨2326162225351219337799467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1550774816900812891866311 2326162225351219337799467)
      ·
        refine ⟨3489243338026829006699201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2326162225351219337799467 3489243338026829006699201)
        ·
          refine ⟨2616932503520121755024401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3489243338026829006699201 2616932503520121755024401)
          ·
            refine ⟨1962699377640091316268301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2616932503520121755024401 1962699377640091316268301)
            ·
              refine ⟨736012266615034243600613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1962699377640091316268301 736012266615034243600613)
              ·
                refine ⟨138002299990318920675115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 736012266615034243600613 138002299990318920675115)
                ·
                  rfl

theorem cell20_907060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 3, 4].length) (baseStart_907060 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_907060 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_907060 prefixEnd_907060 := by exact prefixLift 907060
  have htrace : WordTrace (prefixWord ++ tailWord_907060) baseStart_907060 baseEnd_907060 := by
    simpa [prefixWord, tailWord_907060, baseEnd_907060] using wordTrace_append hprefix tailTrace_907060
  have hstable : (prefixWord ++ tailWord_907060).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907060).length < 2 ^ (prefixWord ++ tailWord_907060).sum := by decide
  have hdescent : baseEnd_907060 < baseStart_907060 := by decide
  rcases family_descends (prefixWord ++ tailWord_907060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907084 : List Nat := [2, 2, 1, 3, 5, 1, 1, 2, 3]
def baseStart_907084 : Nat := 118140960795 + 907084 * 2 ^ 59
def prefixEnd_907084 : Nat := 4983230072969 + 3 ^ 40 * 907084 * 2
def baseEnd_907084 : Nat := 414017854224919345225247

theorem tailTrace_907084 : CollatzResearch.WordTrace tailWord_907084 prefixEnd_907084 414017854224919345225247 := by
  unfold tailWord_907084
  simp only [CollatzResearch.WordTrace]
  refine ⟨16542035722898530229344153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22056047630531373639125537 16542035722898530229344153)
  ·
    refine ⟨12406526792173897672008115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16542035722898530229344153 12406526792173897672008115)
    ·
      refine ⟨18609790188260846508012173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12406526792173897672008115 18609790188260846508012173)
      ·
        refine ⟨6978671320597817440504565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18609790188260846508012173 6978671320597817440504565)
        ·
          refine ⟨654250436306045385047303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6978671320597817440504565 654250436306045385047303)
          ·
            refine ⟨981375654459068077570955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 654250436306045385047303 981375654459068077570955)
            ·
              refine ⟨1472063481688602116356433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 981375654459068077570955 1472063481688602116356433)
              ·
                refine ⟨1104047611266451587267325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1472063481688602116356433 1104047611266451587267325)
                ·
                  refine ⟨414017854224919345225247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1104047611266451587267325 414017854224919345225247)
                  ·
                    rfl

theorem cell20_907084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 1, 2, 3].length) (baseStart_907084 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_907084 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_907084 prefixEnd_907084 := by exact prefixLift 907084
  have htrace : WordTrace (prefixWord ++ tailWord_907084) baseStart_907084 baseEnd_907084 := by
    simpa [prefixWord, tailWord_907084, baseEnd_907084] using wordTrace_append hprefix tailTrace_907084
  have hstable : (prefixWord ++ tailWord_907084).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907084).length < 2 ^ (prefixWord ++ tailWord_907084).sum := by decide
  have hdescent : baseEnd_907084 < baseStart_907084 := by decide
  rcases family_descends (prefixWord ++ tailWord_907084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907146 : List Nat := [3, 1, 2, 4, 2, 1, 3, 2, 2]
def baseStart_907146 : Nat := 118140960795 + 907146 * 2 ^ 59
def prefixEnd_907146 : Nat := 4983230072969 + 3 ^ 40 * 907146 * 2
def baseEnd_907146 : Nat := 414046152714322685158327

theorem tailTrace_907146 : CollatzResearch.WordTrace tailWord_907146 prefixEnd_907146 414046152714322685158327 := by
  unfold tailWord_907146
  simp only [CollatzResearch.WordTrace]
  refine ⟨8271583192893111261861323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22057555181048296698296861 8271583192893111261861323)
  ·
    refine ⟨12407374789339666892791985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8271583192893111261861323 12407374789339666892791985)
    ·
      refine ⟨9305531092004750169593989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12407374789339666892791985 9305531092004750169593989)
      ·
        refine ⟨1744787079750890656798873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9305531092004750169593989 1744787079750890656798873)
        ·
          refine ⟨1308590309813167992599155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1744787079750890656798873 1308590309813167992599155)
          ·
            refine ⟨1962885464719751988898733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1308590309813167992599155 1962885464719751988898733)
            ·
              refine ⟨736082049269906995837025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1962885464719751988898733 736082049269906995837025)
              ·
                refine ⟨552061536952430246877769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 736082049269906995837025 552061536952430246877769)
                ·
                  refine ⟨414046152714322685158327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 552061536952430246877769 414046152714322685158327)
                  ·
                    rfl

theorem cell20_907146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 3, 2, 2].length) (baseStart_907146 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_907146 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_907146 prefixEnd_907146 := by exact prefixLift 907146
  have htrace : WordTrace (prefixWord ++ tailWord_907146) baseStart_907146 baseEnd_907146 := by
    simpa [prefixWord, tailWord_907146, baseEnd_907146] using wordTrace_append hprefix tailTrace_907146
  have hstable : (prefixWord ++ tailWord_907146).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907146).length < 2 ^ (prefixWord ++ tailWord_907146).sum := by decide
  have hdescent : baseEnd_907146 < baseStart_907146 := by decide
  rcases family_descends (prefixWord ++ tailWord_907146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907147 : List Nat := [1, 1, 1, 1, 4, 2, 1, 6, 3]
def baseStart_907147 : Nat := 118140960795 + 907147 * 2 ^ 59
def prefixEnd_907147 : Nat := 4983230072969 + 3 ^ 40 * 907147 * 2
def baseEnd_907147 : Nat := 414046609141571126124989

theorem tailTrace_907147 : CollatzResearch.WordTrace tailWord_907147 prefixEnd_907147 414046609141571126124989 := by
  unfold tailWord_907147
  simp only [CollatzResearch.WordTrace]
  refine ⟨33086369244568822218231695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22057579496379214812154463 33086369244568822218231695)
  ·
    refine ⟨49629553866853233327347543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33086369244568822218231695 49629553866853233327347543)
    ·
      refine ⟨74444330800279849991021315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49629553866853233327347543 74444330800279849991021315)
      ·
        refine ⟨111666496200419774986531973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74444330800279849991021315 111666496200419774986531973)
        ·
          refine ⟨20937468037578707809974745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 111666496200419774986531973 20937468037578707809974745)
          ·
            refine ⟨15703101028184030857481059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20937468037578707809974745 15703101028184030857481059)
            ·
              refine ⟨23554651542276046286221589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15703101028184030857481059 23554651542276046286221589)
              ·
                refine ⟨1104124291044189669666637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 23554651542276046286221589 1104124291044189669666637)
                ·
                  refine ⟨414046609141571126124989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1104124291044189669666637 414046609141571126124989)
                  ·
                    rfl

theorem cell20_907147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 6, 3].length) (baseStart_907147 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_907147 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_907147 prefixEnd_907147 := by exact prefixLift 907147
  have htrace : WordTrace (prefixWord ++ tailWord_907147) baseStart_907147 baseEnd_907147 := by
    simpa [prefixWord, tailWord_907147, baseEnd_907147] using wordTrace_append hprefix tailTrace_907147
  have hstable : (prefixWord ++ tailWord_907147).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907147).length < 2 ^ (prefixWord ++ tailWord_907147).sum := by decide
  have hdescent : baseEnd_907147 < baseStart_907147 := by decide
  rcases family_descends (prefixWord ++ tailWord_907147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907161 : List Nat := [1, 2, 1, 2, 1, 3, 3, 7]
def baseStart_907161 : Nat := 118140960795 + 907161 * 2 ^ 59
def prefixEnd_907161 : Nat := 4983230072969 + 3 ^ 40 * 907161 * 2
def baseEnd_907161 : Nat := 138017666374349766552755

theorem tailTrace_907161 : CollatzResearch.WordTrace tailWord_907161 prefixEnd_907161 138017666374349766552755 := by
  unfold tailWord_907161
  simp only [CollatzResearch.WordTrace]
  refine ⟨33086879866518102609241337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22057919911012068406160891 33086879866518102609241337)
  ·
    refine ⟨24815159899888576956931003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33086879866518102609241337 24815159899888576956931003)
    ·
      refine ⟨37222739849832865435396505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24815159899888576956931003 37222739849832865435396505)
      ·
        refine ⟨27917054887374649076547379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37222739849832865435396505 27917054887374649076547379)
        ·
          refine ⟨41875582331061973614821069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27917054887374649076547379 41875582331061973614821069)
          ·
            refine ⟨15703343374148240105557901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41875582331061973614821069 15703343374148240105557901)
            ·
              refine ⟨5888753765305590039584213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15703343374148240105557901 5888753765305590039584213)
              ·
                refine ⟨138017666374349766552755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5888753765305590039584213 138017666374349766552755)
                ·
                  rfl

theorem cell20_907161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 7].length) (baseStart_907161 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_907161 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_907161 prefixEnd_907161 := by exact prefixLift 907161
  have htrace : WordTrace (prefixWord ++ tailWord_907161) baseStart_907161 baseEnd_907161 := by
    simpa [prefixWord, tailWord_907161, baseEnd_907161] using wordTrace_append hprefix tailTrace_907161
  have hstable : (prefixWord ++ tailWord_907161).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907161).length < 2 ^ (prefixWord ++ tailWord_907161).sum := by decide
  have hdescent : baseEnd_907161 < baseStart_907161 := by decide
  rcases family_descends (prefixWord ++ tailWord_907161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907209 : List Nat := [1, 2, 1, 1, 2, 1, 2, 8, 2]
def baseStart_907209 : Nat := 118140960795 + 907209 * 2 ^ 59
def prefixEnd_907209 : Nat := 4983230072969 + 3 ^ 40 * 907209 * 2
def baseEnd_907209 : Nat := 414074907630974466058069

theorem tailTrace_907209 : CollatzResearch.WordTrace tailWord_907209 prefixEnd_907209 414074907630974466058069 := by
  unfold tailWord_907209
  simp only [CollatzResearch.WordTrace]
  refine ⟨33088630570344206806988681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22059087046896137871325787 33088630570344206806988681)
  ·
    refine ⟨24816472927758155105241511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33088630570344206806988681 24816472927758155105241511)
    ·
      refine ⟨37224709391637232657862267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24816472927758155105241511 37224709391637232657862267)
      ·
        refine ⟨55837064087455848986793401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37224709391637232657862267 55837064087455848986793401)
        ·
          refine ⟨41877798065591886740095051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55837064087455848986793401 41877798065591886740095051)
          ·
            refine ⟨62816697098387830110142577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41877798065591886740095051 62816697098387830110142577)
            ·
              refine ⟨47112522823790872582606933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62816697098387830110142577 47112522823790872582606933)
              ·
                refine ⟨552099876841299288077425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 47112522823790872582606933 552099876841299288077425)
                ·
                  refine ⟨414074907630974466058069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 552099876841299288077425 414074907630974466058069)
                  ·
                    rfl

theorem cell20_907209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 8, 2].length) (baseStart_907209 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_907209 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_907209 prefixEnd_907209 := by exact prefixLift 907209
  have htrace : WordTrace (prefixWord ++ tailWord_907209) baseStart_907209 baseEnd_907209 := by
    simpa [prefixWord, tailWord_907209, baseEnd_907209] using wordTrace_append hprefix tailTrace_907209
  have hstable : (prefixWord ++ tailWord_907209).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907209).length < 2 ^ (prefixWord ++ tailWord_907209).sum := by decide
  have hdescent : baseEnd_907209 < baseStart_907209 := by decide
  rcases family_descends (prefixWord ++ tailWord_907209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907223 : List Nat := [1, 1, 3, 2, 1, 1, 3, 5, 3]
def baseStart_907223 : Nat := 118140960795 + 907223 * 2 ^ 59
def prefixEnd_907223 : Nat := 4983230072969 + 3 ^ 40 * 907223 * 2
def baseEnd_907223 : Nat := 414081297612452639591345

theorem tailTrace_907223 : CollatzResearch.WordTrace tailWord_907223 prefixEnd_907223 414081297612452639591345 := by
  unfold tailWord_907223
  simp only [CollatzResearch.WordTrace]
  refine ⟨33089141192293487197998323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22059427461528991465332215 33089141192293487197998323)
  ·
    refine ⟨49633711788440230796997485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33089141192293487197998323 49633711788440230796997485)
    ·
      refine ⟨18612641920665086548874057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49633711788440230796997485 18612641920665086548874057)
      ·
        refine ⟨13959481440498814911655543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18612641920665086548874057 13959481440498814911655543)
        ·
          refine ⟨20939222160748222367483315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13959481440498814911655543 20939222160748222367483315)
          ·
            refine ⟨31408833241122333551224973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20939222160748222367483315 31408833241122333551224973)
            ·
              refine ⟨11778312465420875081709365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31408833241122333551224973 11778312465420875081709365)
              ·
                refine ⟨1104216793633207038910253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11778312465420875081709365 1104216793633207038910253)
                ·
                  refine ⟨414081297612452639591345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1104216793633207038910253 414081297612452639591345)
                  ·
                    rfl

theorem cell20_907223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 5, 3].length) (baseStart_907223 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_907223 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_907223 prefixEnd_907223 := by exact prefixLift 907223
  have htrace : WordTrace (prefixWord ++ tailWord_907223) baseStart_907223 baseEnd_907223 := by
    simpa [prefixWord, tailWord_907223, baseEnd_907223] using wordTrace_append hprefix tailTrace_907223
  have hstable : (prefixWord ++ tailWord_907223).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907223).length < 2 ^ (prefixWord ++ tailWord_907223).sum := by decide
  have hdescent : baseEnd_907223 < baseStart_907223 := by decide
  rcases family_descends (prefixWord ++ tailWord_907223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907275 : List Nat := [1, 1, 1, 1, 6, 1, 2, 7]
def baseStart_907275 : Nat := 118140960795 + 907275 * 2 ^ 59
def prefixEnd_907275 : Nat := 4983230072969 + 3 ^ 40 * 907275 * 2
def baseEnd_907275 : Nat := 138035010609790523285933

theorem tailTrace_907275 : CollatzResearch.WordTrace tailWord_907275 prefixEnd_907275 138035010609790523285933 := by
  unfold tailWord_907275
  simp only [CollatzResearch.WordTrace]
  refine ⟨33091037788105100078891279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22060691858736733385927519 33091037788105100078891279)
  ·
    refine ⟨49636556682157650118336919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33091037788105100078891279 49636556682157650118336919)
    ·
      refine ⟨74454835023236475177505379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49636556682157650118336919 74454835023236475177505379)
      ·
        refine ⟨111682252534854712766258069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74454835023236475177505379 111682252534854712766258069)
        ·
          refine ⟨5235105587571314660918347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 111682252534854712766258069 5235105587571314660918347)
          ·
            refine ⟨7852658381356971991377521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5235105587571314660918347 7852658381356971991377521)
            ·
              refine ⟨5889493786017728993533141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7852658381356971991377521 5889493786017728993533141)
              ·
                refine ⟨138035010609790523285933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5889493786017728993533141 138035010609790523285933)
                ·
                  rfl

theorem cell20_907275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 7].length) (baseStart_907275 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_907275 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_907275 prefixEnd_907275 := by exact prefixLift 907275
  have htrace : WordTrace (prefixWord ++ tailWord_907275) baseStart_907275 baseEnd_907275 := by
    simpa [prefixWord, tailWord_907275, baseEnd_907275] using wordTrace_append hprefix tailTrace_907275
  have hstable : (prefixWord ++ tailWord_907275).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907275).length < 2 ^ (prefixWord ++ tailWord_907275).sum := by decide
  have hdescent : baseEnd_907275 < baseStart_907275 := by decide
  rcases family_descends (prefixWord ++ tailWord_907275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907284 : List Nat := [2, 4, 3, 2, 2, 1, 2, 4]
def baseStart_907284 : Nat := 118140960795 + 907284 * 2 ^ 59
def prefixEnd_907284 : Nat := 4983230072969 + 3 ^ 40 * 907284 * 2
def baseEnd_907284 : Nat := 138036379891535846185921

theorem tailTrace_907284 : CollatzResearch.WordTrace tailWord_907284 prefixEnd_907284 138036379891535846185921 := by
  unfold tailWord_907284
  simp only [CollatzResearch.WordTrace]
  refine ⟨16545683022536247307984453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22060910696714996410645937 16545683022536247307984453)
  ·
    refine ⟨3102315566725546370247085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16545683022536247307984453 3102315566725546370247085)
    ·
      refine ⟨1163368337522079888842657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3102315566725546370247085 1163368337522079888842657)
      ·
        refine ⟨872526253141559916631993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1163368337522079888842657 872526253141559916631993)
        ·
          refine ⟨654394689856169937473995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 872526253141559916631993 654394689856169937473995)
          ·
            refine ⟨981592034784254906210993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 654394689856169937473995 981592034784254906210993)
            ·
              refine ⟨736194026088191179658245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 981592034784254906210993 736194026088191179658245)
              ·
                refine ⟨138036379891535846185921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 736194026088191179658245 138036379891535846185921)
                ·
                  rfl

theorem cell20_907284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 2, 4].length) (baseStart_907284 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_907284 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_907284 prefixEnd_907284 := by exact prefixLift 907284
  have htrace : WordTrace (prefixWord ++ tailWord_907284) baseStart_907284 baseEnd_907284 := by
    simpa [prefixWord, tailWord_907284, baseEnd_907284] using wordTrace_append hprefix tailTrace_907284
  have hstable : (prefixWord ++ tailWord_907284).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907284).length < 2 ^ (prefixWord ++ tailWord_907284).sum := by decide
  have hdescent : baseEnd_907284 < baseStart_907284 := by decide
  rcases family_descends (prefixWord ++ tailWord_907284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907292 : List Nat := [2, 2, 3, 1, 3, 2, 1, 6]
def baseStart_907292 : Nat := 118140960795 + 907292 * 2 ^ 59
def prefixEnd_907292 : Nat := 4983230072969 + 3 ^ 40 * 907292 * 2
def baseEnd_907292 : Nat := 138037597030865022097021

theorem tailTrace_907292 : CollatzResearch.WordTrace tailWord_907292 prefixEnd_907292 138037597030865022097021 := by
  unfold tailWord_907292
  simp only [CollatzResearch.WordTrace]
  refine ⟨16545828914521755991130065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22061105219362341321506753 16545828914521755991130065)
  ·
    refine ⟨12409371685891316993347549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16545828914521755991130065 12409371685891316993347549)
    ·
      refine ⟨4653514382209243872505331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12409371685891316993347549 4653514382209243872505331)
      ·
        refine ⟨6980271573313865808757997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4653514382209243872505331 6980271573313865808757997)
        ·
          refine ⟨2617601839992699678284249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6980271573313865808757997 2617601839992699678284249)
          ·
            refine ⟨1963201379994524758713187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2617601839992699678284249 1963201379994524758713187)
            ·
              refine ⟨2944802069991787138069781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1963201379994524758713187 2944802069991787138069781)
              ·
                refine ⟨138037597030865022097021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2944802069991787138069781 138037597030865022097021)
                ·
                  rfl

theorem cell20_907292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 1, 6].length) (baseStart_907292 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_907292 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_907292 prefixEnd_907292 := by exact prefixLift 907292
  have htrace : WordTrace (prefixWord ++ tailWord_907292) baseStart_907292 baseEnd_907292 := by
    simpa [prefixWord, tailWord_907292, baseEnd_907292] using wordTrace_append hprefix tailTrace_907292
  have hstable : (prefixWord ++ tailWord_907292).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907292).length < 2 ^ (prefixWord ++ tailWord_907292).sum := by decide
  have hdescent : baseEnd_907292 < baseStart_907292 := by decide
  rcases family_descends (prefixWord ++ tailWord_907292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907313 : List Nat := [1, 2, 2, 3, 1, 3, 8]
def baseStart_907313 : Nat := 118140960795 + 907313 * 2 ^ 59
def prefixEnd_907313 : Nat := 4983230072969 + 3 ^ 40 * 907313 * 2
def baseEnd_907313 : Nat := 46013597340534702954553

theorem tailTrace_907313 : CollatzResearch.WordTrace tailWord_907313 prefixEnd_907313 46013597340534702954553 := by
  unfold tailWord_907313
  simp only [CollatzResearch.WordTrace]
  refine ⟨33092423761967432568774593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22061615841311621712516395 33092423761967432568774593)
  ·
    refine ⟨24819317821475574426580945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33092423761967432568774593 24819317821475574426580945)
    ·
      refine ⟨18614488366106680819935709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24819317821475574426580945 18614488366106680819935709)
      ·
        refine ⟨6980433137290005307475891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18614488366106680819935709 6980433137290005307475891)
        ·
          refine ⟨10470649705935007961213837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6980433137290005307475891 10470649705935007961213837)
          ·
            refine ⟨3926493639725627985455189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10470649705935007961213837 3926493639725627985455189)
            ·
              refine ⟨46013597340534702954553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3926493639725627985455189 46013597340534702954553)
              ·
                rfl

theorem cell20_907313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 8].length) (baseStart_907313 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_907313 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_907313 prefixEnd_907313 := by exact prefixLift 907313
  have htrace : WordTrace (prefixWord ++ tailWord_907313) baseStart_907313 baseEnd_907313 := by
    simpa [prefixWord, tailWord_907313, baseEnd_907313] using wordTrace_append hprefix tailTrace_907313
  have hstable : (prefixWord ++ tailWord_907313).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907313).length < 2 ^ (prefixWord ++ tailWord_907313).sum := by decide
  have hdescent : baseEnd_907313 < baseStart_907313 := by decide
  rcases family_descends (prefixWord ++ tailWord_907313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907337 : List Nat := [1, 2, 1, 1, 2, 2, 5, 3, 3]
def baseStart_907337 : Nat := 118140960795 + 907337 * 2 ^ 59
def prefixEnd_907337 : Nat := 4983230072969 + 3 ^ 40 * 907337 * 2
def baseEnd_907337 : Nat := 414133330318774909790879

theorem tailTrace_907337 : CollatzResearch.WordTrace tailWord_907337 prefixEnd_907337 414133330318774909790879 := by
  unfold tailWord_907337
  simp only [CollatzResearch.WordTrace]
  refine ⟨33093299113880484667648265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22062199409253656445098843 33093299113880484667648265)
  ·
    refine ⟨24819974335410363500736199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33093299113880484667648265 24819974335410363500736199)
    ·
      refine ⟨37229961503115545251104299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24819974335410363500736199 37229961503115545251104299)
      ·
        refine ⟨55844942254673317876656449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37229961503115545251104299 55844942254673317876656449)
        ·
          refine ⟨41883706691004988407492337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55844942254673317876656449 41883706691004988407492337)
          ·
            refine ⟨31412780018253741305619253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41883706691004988407492337 31412780018253741305619253)
            ·
              refine ⟨2944948126711288247401805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31412780018253741305619253 2944948126711288247401805)
              ·
                refine ⟨1104355547516733092775677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2944948126711288247401805 1104355547516733092775677)
                ·
                  refine ⟨414133330318774909790879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1104355547516733092775677 414133330318774909790879)
                  ·
                    rfl

theorem cell20_907337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 3, 3].length) (baseStart_907337 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_907337 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_907337 prefixEnd_907337 := by exact prefixLift 907337
  have htrace : WordTrace (prefixWord ++ tailWord_907337) baseStart_907337 baseEnd_907337 := by
    simpa [prefixWord, tailWord_907337, baseEnd_907337] using wordTrace_append hprefix tailTrace_907337
  have hstable : (prefixWord ++ tailWord_907337).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907337).length < 2 ^ (prefixWord ++ tailWord_907337).sum := by decide
  have hdescent : baseEnd_907337 < baseStart_907337 := by decide
  rcases family_descends (prefixWord ++ tailWord_907337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907351 : List Nat := [1, 1, 3, 2, 2, 1, 4, 6]
def baseStart_907351 : Nat := 118140960795 + 907351 * 2 ^ 59
def prefixEnd_907351 : Nat := 4983230072969 + 3 ^ 40 * 907351 * 2
def baseEnd_907351 : Nat := 138046573433417694441385

theorem tailTrace_907351 : CollatzResearch.WordTrace tailWord_907351 prefixEnd_907351 138046573433417694441385 := by
  unfold tailWord_907351
  simp only [CollatzResearch.WordTrace]
  refine ⟨33093809735829765058657907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22062539823886510039105271 33093809735829765058657907)
  ·
    refine ⟨49640714603744647587986861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33093809735829765058657907 49640714603744647587986861)
    ·
      refine ⟨18615267976404242845495073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49640714603744647587986861 18615267976404242845495073)
      ·
        refine ⟨13961450982303182134121305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18615267976404242845495073 13961450982303182134121305)
        ·
          refine ⟨10471088236727386600590979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13961450982303182134121305 10471088236727386600590979)
          ·
            refine ⟨15706632355091079900886469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10471088236727386600590979 15706632355091079900886469)
            ·
              refine ⟨2944993566579577481416213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15706632355091079900886469 2944993566579577481416213)
              ·
                refine ⟨138046573433417694441385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2944993566579577481416213 138046573433417694441385)
                ·
                  rfl

theorem cell20_907351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 6].length) (baseStart_907351 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_907351 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_907351 prefixEnd_907351 := by exact prefixLift 907351
  have htrace : WordTrace (prefixWord ++ tailWord_907351) baseStart_907351 baseEnd_907351 := by
    simpa [prefixWord, tailWord_907351, baseEnd_907351] using wordTrace_append hprefix tailTrace_907351
  have hstable : (prefixWord ++ tailWord_907351).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907351).length < 2 ^ (prefixWord ++ tailWord_907351).sum := by decide
  have hdescent : baseEnd_907351 < baseStart_907351 := by decide
  rcases family_descends (prefixWord ++ tailWord_907351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907361 : List Nat := [1, 2, 3, 1, 1, 2, 1, 7, 2]
def baseStart_907361 : Nat := 118140960795 + 907361 * 2 ^ 59
def prefixEnd_907361 : Nat := 4983230072969 + 3 ^ 40 * 907361 * 2
def baseEnd_907361 : Nat := 414144284572737492990781

theorem tailTrace_907361 : CollatzResearch.WordTrace tailWord_907361 prefixEnd_907361 414144284572737492990781 := by
  unfold tailWord_907361
  simp only [CollatzResearch.WordTrace]
  refine ⟨33094174465793536766521937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22062782977195691177681291 33094174465793536766521937)
  ·
    refine ⟨24820630849345152574891453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33094174465793536766521937 24820630849345152574891453)
    ·
      refine ⟨9307736568504432215584295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24820630849345152574891453 9307736568504432215584295)
      ·
        refine ⟨13961604852756648323376443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9307736568504432215584295 13961604852756648323376443)
        ·
          refine ⟨20942407279134972485064665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13961604852756648323376443 20942407279134972485064665)
          ·
            refine ⟨15706805459351229363798499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20942407279134972485064665 15706805459351229363798499)
            ·
              refine ⟨23560208189026844045697749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15706805459351229363798499 23560208189026844045697749)
              ·
                refine ⟨552192379430316657321041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 23560208189026844045697749 552192379430316657321041)
                ·
                  refine ⟨414144284572737492990781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 552192379430316657321041 414144284572737492990781)
                  ·
                    rfl

theorem cell20_907361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 7, 2].length) (baseStart_907361 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_907361 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_907361 prefixEnd_907361 := by exact prefixLift 907361
  have htrace : WordTrace (prefixWord ++ tailWord_907361) baseStart_907361 baseEnd_907361 := by
    simpa [prefixWord, tailWord_907361, baseEnd_907361] using wordTrace_append hprefix tailTrace_907361
  have hstable : (prefixWord ++ tailWord_907361).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907361).length < 2 ^ (prefixWord ++ tailWord_907361).sum := by decide
  have hdescent : baseEnd_907361 < baseStart_907361 := by decide
  rcases family_descends (prefixWord ++ tailWord_907361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907375 : List Nat := [1, 1, 2, 1, 3, 4, 1, 4, 3]
def baseStart_907375 : Nat := 118140960795 + 907375 * 2 ^ 59
def prefixEnd_907375 : Nat := 4983230072969 + 3 ^ 40 * 907375 * 2
def baseEnd_907375 : Nat := 414150674554215666524057

theorem tailTrace_907375 : CollatzResearch.WordTrace tailWord_907375 prefixEnd_907375 414150674554215666524057 := by
  unfold tailWord_907375
  simp only [CollatzResearch.WordTrace]
  refine ⟨33094685087742817157531579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22063123391828544771687719 33094685087742817157531579)
  ·
    refine ⟨49642027631614225736297369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33094685087742817157531579 49642027631614225736297369)
    ·
      refine ⟨37231520723710669302223027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49642027631614225736297369 37231520723710669302223027)
      ·
        refine ⟨55847281085566003953334541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37231520723710669302223027 55847281085566003953334541)
        ·
          refine ⟨20942730407087251482500453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55847281085566003953334541 20942730407087251482500453)
          ·
            refine ⟨3926761951328859652968835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20942730407087251482500453 3926761951328859652968835)
            ·
              refine ⟨5890142926993289479453253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3926761951328859652968835 5890142926993289479453253)
              ·
                refine ⟨1104401798811241777397485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5890142926993289479453253 1104401798811241777397485)
                ·
                  refine ⟨414150674554215666524057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1104401798811241777397485 414150674554215666524057)
                  ·
                    rfl

theorem cell20_907375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 4, 3].length) (baseStart_907375 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_907375 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_907375 prefixEnd_907375 := by exact prefixLift 907375
  have htrace : WordTrace (prefixWord ++ tailWord_907375) baseStart_907375 baseEnd_907375 := by
    simpa [prefixWord, tailWord_907375, baseEnd_907375] using wordTrace_append hprefix tailTrace_907375
  have hstable : (prefixWord ++ tailWord_907375).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907375).length < 2 ^ (prefixWord ++ tailWord_907375).sum := by decide
  have hdescent : baseEnd_907375 < baseStart_907375 := by decide
  rcases family_descends (prefixWord ++ tailWord_907375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907378 : List Nat := [3, 2, 1, 2, 2, 3, 1, 4, 2]
def baseStart_907378 : Nat := 118140960795 + 907378 * 2 ^ 59
def prefixEnd_907378 : Nat := 4983230072969 + 3 ^ 40 * 907378 * 2
def baseEnd_907378 : Nat := 414152043835960989424045

theorem tailTrace_907378 : CollatzResearch.WordTrace tailWord_907378 prefixEnd_907378 414152043835960989424045 := by
  unfold tailWord_907378
  simp only [CollatzResearch.WordTrace]
  refine ⟨8273698626682987167472697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22063196337821299113260525 8273698626682987167472697)
  ·
    refine ⟨6205273970012240375604523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8273698626682987167472697 6205273970012240375604523)
    ·
      refine ⟨9307910955018360563406785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6205273970012240375604523 9307910955018360563406785)
      ·
        refine ⟨6980933216263770422555089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9307910955018360563406785 6980933216263770422555089)
        ·
          refine ⟨5235699912197827816916317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6980933216263770422555089 5235699912197827816916317)
          ·
            refine ⟨1963387467074185431343619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5235699912197827816916317 1963387467074185431343619)
            ·
              refine ⟨2945081200611278147015429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1963387467074185431343619 2945081200611278147015429)
              ·
                refine ⟨552202725114614652565393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2945081200611278147015429 552202725114614652565393)
                ·
                  refine ⟨414152043835960989424045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 552202725114614652565393 414152043835960989424045)
                  ·
                    rfl

theorem cell20_907378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 4, 2].length) (baseStart_907378 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_907378 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_907378 prefixEnd_907378 := by exact prefixLift 907378
  have htrace : WordTrace (prefixWord ++ tailWord_907378) baseStart_907378 baseEnd_907378 := by
    simpa [prefixWord, tailWord_907378, baseEnd_907378] using wordTrace_append hprefix tailTrace_907378
  have hstable : (prefixWord ++ tailWord_907378).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907378).length < 2 ^ (prefixWord ++ tailWord_907378).sum := by decide
  have hdescent : baseEnd_907378 < baseStart_907378 := by decide
  rcases family_descends (prefixWord ++ tailWord_907378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907412 : List Nat := [2, 4, 2, 3, 1, 1, 2, 3, 2]
def baseStart_907412 : Nat := 118140960795 + 907412 * 2 ^ 59
def prefixEnd_907412 : Nat := 4983230072969 + 3 ^ 40 * 907412 * 2
def baseEnd_907412 : Nat := 414167562362407982290573

theorem tailTrace_907412 : CollatzResearch.WordTrace tailWord_907412 prefixEnd_907412 414167562362407982290573 := by
  unfold tailWord_907412
  simp only [CollatzResearch.WordTrace]
  refine ⟨16548017294304386238314245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22064023059072514984418993 16548017294304386238314245)
  ·
    refine ⟨3102753242682072419683921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16548017294304386238314245 3102753242682072419683921)
    ·
      refine ⟨2327064932011554314762941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3102753242682072419683921 2327064932011554314762941)
      ·
        refine ⟨872649349504332868036103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2327064932011554314762941 872649349504332868036103)
        ·
          refine ⟨1308974024256499302054155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 872649349504332868036103 1308974024256499302054155)
          ·
            refine ⟨1963461036384748953081233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1308974024256499302054155 1963461036384748953081233)
            ·
              refine ⟨1472595777288561714810925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1963461036384748953081233 1472595777288561714810925)
              ·
                refine ⟨552223416483210643054097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1472595777288561714810925 552223416483210643054097)
                ·
                  refine ⟨414167562362407982290573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 552223416483210643054097 414167562362407982290573)
                  ·
                    rfl

theorem cell20_907412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 2, 3, 2].length) (baseStart_907412 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_907412 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_907412 prefixEnd_907412 := by exact prefixLift 907412
  have htrace : WordTrace (prefixWord ++ tailWord_907412) baseStart_907412 baseEnd_907412 := by
    simpa [prefixWord, tailWord_907412, baseEnd_907412] using wordTrace_append hprefix tailTrace_907412
  have hstable : (prefixWord ++ tailWord_907412).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907412).length < 2 ^ (prefixWord ++ tailWord_907412).sum := by decide
  have hdescent : baseEnd_907412 < baseStart_907412 := by decide
  rcases family_descends (prefixWord ++ tailWord_907412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907420 : List Nat := [2, 2, 3, 2, 1, 1, 1, 2, 6]
def baseStart_907420 : Nat := 118140960795 + 907420 * 2 ^ 59
def prefixEnd_907420 : Nat := 4983230072969 + 3 ^ 40 * 907420 * 2
def baseEnd_907420 : Nat := 414171213780395510023873

theorem tailTrace_907420 : CollatzResearch.WordTrace tailWord_907420 prefixEnd_907420 414171213780395510023873 := by
  unfold tailWord_907420
  simp only [CollatzResearch.WordTrace]
  refine ⟨16548163186289894921459857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22064217581719859895279809 16548163186289894921459857)
  ·
    refine ⟨12411122389717421191094893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16548163186289894921459857 12411122389717421191094893)
    ·
      refine ⟨4654170896144032946660585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12411122389717421191094893 4654170896144032946660585)
      ·
        refine ⟨3490628172108024709995439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4654170896144032946660585 3490628172108024709995439)
        ·
          refine ⟨5235942258162037064993159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3490628172108024709995439 5235942258162037064993159)
          ·
            refine ⟨7853913387243055597489739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5235942258162037064993159 7853913387243055597489739)
            ·
              refine ⟨11780870080864583396234609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7853913387243055597489739 11780870080864583396234609)
              ·
                refine ⟨8835652560648437547175957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11780870080864583396234609 8835652560648437547175957)
                ·
                  refine ⟨414171213780395510023873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8835652560648437547175957 414171213780395510023873)
                  ·
                    rfl

theorem cell20_907420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 2, 6].length) (baseStart_907420 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_907420 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_907420 prefixEnd_907420 := by exact prefixLift 907420
  have htrace : WordTrace (prefixWord ++ tailWord_907420) baseStart_907420 baseEnd_907420 := by
    simpa [prefixWord, tailWord_907420, baseEnd_907420] using wordTrace_append hprefix tailTrace_907420
  have hstable : (prefixWord ++ tailWord_907420).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907420).length < 2 ^ (prefixWord ++ tailWord_907420).sum := by decide
  have hdescent : baseEnd_907420 < baseStart_907420 := by decide
  rcases family_descends (prefixWord ++ tailWord_907420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907437 : List Nat := [1, 5, 2, 1, 2, 1, 1, 3, 4]
def baseStart_907437 : Nat := 118140960795 + 907437 * 2 ^ 59
def prefixEnd_907437 : Nat := 4983230072969 + 3 ^ 40 * 907437 * 2
def baseEnd_907437 : Nat := 414178973043619006457137

theorem tailTrace_907437 : CollatzResearch.WordTrace tailWord_907437 prefixEnd_907437 414178973043619006457137 := by
  unfold tailWord_907437
  simp only [CollatzResearch.WordTrace]
  refine ⟨33096946413518201746288565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22064630942345467830859043 33096946413518201746288565)
  ·
    refine ⟨3102838726267331413714553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33096946413518201746288565 3102838726267331413714553)
    ·
      refine ⟨2327129044700498560285915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3102838726267331413714553 2327129044700498560285915)
      ·
        refine ⟨3490693567050747840428873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2327129044700498560285915 3490693567050747840428873)
        ·
          refine ⟨2618020175288060880321655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3490693567050747840428873 2618020175288060880321655)
          ·
            refine ⟨3927030262932091320482483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2618020175288060880321655 3927030262932091320482483)
            ·
              refine ⟨5890545394398136980723725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3927030262932091320482483 5890545394398136980723725)
              ·
                refine ⟨2208954522899301367771397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5890545394398136980723725 2208954522899301367771397)
                ·
                  refine ⟨414178973043619006457137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2208954522899301367771397 414178973043619006457137)
                  ·
                    rfl

theorem cell20_907437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_907437 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_907437 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_907437 prefixEnd_907437 := by exact prefixLift 907437
  have htrace : WordTrace (prefixWord ++ tailWord_907437) baseStart_907437 baseEnd_907437 := by
    simpa [prefixWord, tailWord_907437, baseEnd_907437] using wordTrace_append hprefix tailTrace_907437
  have hstable : (prefixWord ++ tailWord_907437).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907437).length < 2 ^ (prefixWord ++ tailWord_907437).sum := by decide
  have hdescent : baseEnd_907437 < baseStart_907437 := by decide
  rcases family_descends (prefixWord ++ tailWord_907437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907457 : List Nat := [1, 2, 6, 1, 3, 1, 2, 4]
def baseStart_907457 : Nat := 118140960795 + 907457 * 2 ^ 59
def prefixEnd_907457 : Nat := 4983230072969 + 3 ^ 40 * 907457 * 2
def baseEnd_907457 : Nat := 138062700529529275263463

theorem tailTrace_907457 : CollatzResearch.WordTrace tailWord_907457 prefixEnd_907457 138062700529529275263463 := by
  unfold tailWord_907457
  simp only [CollatzResearch.WordTrace]
  refine ⟨33097675873445745162016625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22065117248963830108011083 33097675873445745162016625)
  ·
    refine ⟨24823256905084308871512469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33097675873445745162016625 24823256905084308871512469)
    ·
      refine ⟨1163590167425826978352147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 24823256905084308871512469 1163590167425826978352147)
      ·
        refine ⟨1745385251138740467528221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1163590167425826978352147 1745385251138740467528221)
        ·
          refine ⟨654519469177027675323083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1745385251138740467528221 654519469177027675323083)
          ·
            refine ⟨981779203765541512984625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 654519469177027675323083 981779203765541512984625)
            ·
              refine ⟨736334402824156134738469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 981779203765541512984625 736334402824156134738469)
              ·
                refine ⟨138062700529529275263463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 736334402824156134738469 138062700529529275263463)
                ·
                  rfl

theorem cell20_907457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 2, 4].length) (baseStart_907457 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_907457 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_907457 prefixEnd_907457 := by exact prefixLift 907457
  have htrace : WordTrace (prefixWord ++ tailWord_907457) baseStart_907457 baseEnd_907457 := by
    simpa [prefixWord, tailWord_907457, baseEnd_907457] using wordTrace_append hprefix tailTrace_907457
  have hstable : (prefixWord ++ tailWord_907457).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907457).length < 2 ^ (prefixWord ++ tailWord_907457).sum := by decide
  have hdescent : baseEnd_907457 < baseStart_907457 := by decide
  rcases family_descends (prefixWord ++ tailWord_907457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907489 : List Nat := [1, 2, 3, 1, 3, 1, 2, 4, 3]
def baseStart_907489 : Nat := 118140960795 + 907489 * 2 ^ 59
def prefixEnd_907489 : Nat := 4983230072969 + 3 ^ 40 * 907489 * 2
def baseEnd_907489 : Nat := 414202707260537936723591

theorem tailTrace_907489 : CollatzResearch.WordTrace tailWord_907489 prefixEnd_907489 414202707260537936723591 := by
  unfold tailWord_907489
  simp only [CollatzResearch.WordTrace]
  refine ⟨33098843009329814627181521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22065895339553209751454347 33098843009329814627181521)
  ·
    refine ⟨24824132256997360970386141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33098843009329814627181521 24824132256997360970386141)
    ·
      refine ⟨9309049596374010363894803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24824132256997360970386141 9309049596374010363894803)
      ·
        refine ⟨13963574394561015545842205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9309049596374010363894803 13963574394561015545842205)
        ·
          refine ⟨5236340397960380829690827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13963574394561015545842205 5236340397960380829690827)
          ·
            refine ⟨7854510596940571244536241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5236340397960380829690827 7854510596940571244536241)
            ·
              refine ⟨5890882947705428433402181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7854510596940571244536241 5890882947705428433402181)
              ·
                refine ⟨1104540552694767831262909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5890882947705428433402181 1104540552694767831262909)
                ·
                  refine ⟨414202707260537936723591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1104540552694767831262909 414202707260537936723591)
                  ·
                    rfl

theorem cell20_907489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 4, 3].length) (baseStart_907489 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_907489 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_907489 prefixEnd_907489 := by exact prefixLift 907489
  have htrace : WordTrace (prefixWord ++ tailWord_907489) baseStart_907489 baseEnd_907489 := by
    simpa [prefixWord, tailWord_907489, baseEnd_907489] using wordTrace_append hprefix tailTrace_907489
  have hstable : (prefixWord ++ tailWord_907489).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907489).length < 2 ^ (prefixWord ++ tailWord_907489).sum := by decide
  have hdescent : baseEnd_907489 < baseStart_907489 := by decide
  rcases family_descends (prefixWord ++ tailWord_907489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907503 : List Nat := [1, 1, 2, 1, 6, 1, 1, 7]
def baseStart_907503 : Nat := 118140960795 + 907503 * 2 ^ 59
def prefixEnd_907503 : Nat := 4983230072969 + 3 ^ 40 * 907503 * 2
def baseEnd_907503 : Nat := 138069699080672036752289

theorem tailTrace_907503 : CollatzResearch.WordTrace tailWord_907503 prefixEnd_907503 138069699080672036752289 := by
  unfold tailWord_907503
  simp only [CollatzResearch.WordTrace]
  refine ⟨33099353631279095018191163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22066235754186063345460775 33099353631279095018191163)
  ·
    refine ⟨49649030446918642527286745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33099353631279095018191163 49649030446918642527286745)
    ·
      refine ⟨37236772835188981895465059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49649030446918642527286745 37236772835188981895465059)
      ·
        refine ⟨55855159252783472843197589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37236772835188981895465059 55855159252783472843197589)
        ·
          refine ⟨2618210589974225289524887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 55855159252783472843197589 2618210589974225289524887)
          ·
            refine ⟨3927315884961337934287331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2618210589974225289524887 3927315884961337934287331)
            ·
              refine ⟨5890973827442006901430997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3927315884961337934287331 5890973827442006901430997)
              ·
                refine ⟨138069699080672036752289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5890973827442006901430997 138069699080672036752289)
                ·
                  rfl

theorem cell20_907503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 7].length) (baseStart_907503 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_907503 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_907503 prefixEnd_907503 := by exact prefixLift 907503
  have htrace : WordTrace (prefixWord ++ tailWord_907503) baseStart_907503 baseEnd_907503 := by
    simpa [prefixWord, tailWord_907503, baseEnd_907503] using wordTrace_append hprefix tailTrace_907503
  have hstable : (prefixWord ++ tailWord_907503).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907503).length < 2 ^ (prefixWord ++ tailWord_907503).sum := by decide
  have hdescent : baseEnd_907503 < baseStart_907503 := by decide
  rcases family_descends (prefixWord ++ tailWord_907503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907506 : List Nat := [3, 2, 1, 3, 2, 2, 1, 3, 3]
def baseStart_907506 : Nat := 118140960795 + 907506 * 2 ^ 59
def prefixEnd_907506 : Nat := 4983230072969 + 3 ^ 40 * 907506 * 2
def baseEnd_907506 : Nat := 414210466523761433156855

theorem tailTrace_907506 : CollatzResearch.WordTrace tailWord_907506 prefixEnd_907506 414210466523761433156855 := by
  unfold tailWord_907506
  simp only [CollatzResearch.WordTrace]
  refine ⟨8274865762567056632637593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22066308700178817687033581 8274865762567056632637593)
  ·
    refine ⟨6206149321925292474478195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8274865762567056632637593 6206149321925292474478195)
    ·
      refine ⟨9309223982887938711717293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6206149321925292474478195 9309223982887938711717293)
      ·
        refine ⟨3490958993582977016893985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9309223982887938711717293 3490958993582977016893985)
        ·
          refine ⟨2618219245187232762670489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3490958993582977016893985 2618219245187232762670489)
          ·
            refine ⟨1963664433890424572002867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2618219245187232762670489 1963664433890424572002867)
            ·
              refine ⟨2945496650835636858004301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1963664433890424572002867 2945496650835636858004301)
              ·
                refine ⟨1104561244063363821751613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2945496650835636858004301 1104561244063363821751613)
                ·
                  refine ⟨414210466523761433156855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1104561244063363821751613 414210466523761433156855)
                  ·
                    rfl

theorem cell20_907506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 3, 3].length) (baseStart_907506 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_907506 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_907506 prefixEnd_907506 := by exact prefixLift 907506
  have htrace : WordTrace (prefixWord ++ tailWord_907506) baseStart_907506 baseEnd_907506 := by
    simpa [prefixWord, tailWord_907506, baseEnd_907506] using wordTrace_append hprefix tailTrace_907506
  have hstable : (prefixWord ++ tailWord_907506).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907506).length < 2 ^ (prefixWord ++ tailWord_907506).sum := by decide
  have hdescent : baseEnd_907506 < baseStart_907506 := by decide
  rcases family_descends (prefixWord ++ tailWord_907506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907585 : List Nat := [1, 2, 5, 2, 2, 1, 2, 3, 2]
def baseStart_907585 : Nat := 118140960795 + 907585 * 2 ^ 59
def prefixEnd_907585 : Nat := 4983230072969 + 3 ^ 40 * 907585 * 2
def baseEnd_907585 : Nat := 414246524276388269523199

theorem tailTrace_907585 : CollatzResearch.WordTrace tailWord_907585 prefixEnd_907585 414246524276388269523199 := by
  unfold tailWord_907585
  simp only [CollatzResearch.WordTrace]
  refine ⟨33102344416982023022676209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22068229611321348681784139 33102344416982023022676209)
  ·
    refine ⟨24826758312736517267007157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33102344416982023022676209 24826758312736517267007157)
    ·
      refine ⟨2327508591819048493781921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24826758312736517267007157 2327508591819048493781921)
      ·
        refine ⟨1745631443864286370336441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2327508591819048493781921 1745631443864286370336441)
        ·
          refine ⟨1309223582898214777752331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1745631443864286370336441 1309223582898214777752331)
          ·
            refine ⟨1963835374347322166628497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1309223582898214777752331 1963835374347322166628497)
            ·
              refine ⟨1472876530760491624971373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1963835374347322166628497 1472876530760491624971373)
              ·
                refine ⟨552328699035184359364265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1472876530760491624971373 552328699035184359364265)
                ·
                  refine ⟨414246524276388269523199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 552328699035184359364265 414246524276388269523199)
                  ·
                    rfl

theorem cell20_907585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 2, 3, 2].length) (baseStart_907585 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_907585 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_907585 prefixEnd_907585 := by exact prefixLift 907585
  have htrace : WordTrace (prefixWord ++ tailWord_907585) baseStart_907585 baseEnd_907585 := by
    simpa [prefixWord, tailWord_907585, baseEnd_907585] using wordTrace_append hprefix tailTrace_907585
  have hstable : (prefixWord ++ tailWord_907585).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907585).length < 2 ^ (prefixWord ++ tailWord_907585).sum := by decide
  have hdescent : baseEnd_907585 < baseStart_907585 := by decide
  rcases family_descends (prefixWord ++ tailWord_907585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907593 : List Nat := [1, 2, 1, 1, 2, 3, 1, 1, 8]
def baseStart_907593 : Nat := 118140960795 + 907593 * 2 ^ 59
def prefixEnd_907593 : Nat := 4983230072969 + 3 ^ 40 * 907593 * 2
def baseEnd_907593 : Nat := 414250175694375797256499

theorem tailTrace_907593 : CollatzResearch.WordTrace tailWord_907593 prefixEnd_907593 414250175694375797256499 := by
  unfold tailWord_907593
  simp only [CollatzResearch.WordTrace]
  refine ⟨33102636200953040388967433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22068424133968693592644955 33102636200953040388967433)
  ·
    refine ⟨24826977150714780291725575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33102636200953040388967433 24826977150714780291725575)
    ·
      refine ⟨37240465726072170437588363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24826977150714780291725575 37240465726072170437588363)
      ·
        refine ⟨55860698589108255656382545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37240465726072170437588363 55860698589108255656382545)
        ·
          refine ⟨41895523941831191742286909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55860698589108255656382545 41895523941831191742286909)
          ·
            refine ⟨15710821478186696903357591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41895523941831191742286909 15710821478186696903357591)
            ·
              refine ⟨23566232217280045355036387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15710821478186696903357591 23566232217280045355036387)
              ·
                refine ⟨35349348325920068032554581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23566232217280045355036387 35349348325920068032554581)
                ·
                  refine ⟨414250175694375797256499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35349348325920068032554581 414250175694375797256499)
                  ·
                    rfl

theorem cell20_907593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 8].length) (baseStart_907593 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_907593 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_907593 prefixEnd_907593 := by exact prefixLift 907593
  have htrace : WordTrace (prefixWord ++ tailWord_907593) baseStart_907593 baseEnd_907593 := by
    simpa [prefixWord, tailWord_907593, baseEnd_907593] using wordTrace_append hprefix tailTrace_907593
  have hstable : (prefixWord ++ tailWord_907593).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907593).length < 2 ^ (prefixWord ++ tailWord_907593).sum := by decide
  have hdescent : baseEnd_907593 < baseStart_907593 := by decide
  rcases family_descends (prefixWord ++ tailWord_907593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907620 : List Nat := [2, 3, 1, 1, 3, 1, 5, 1, 3]
def baseStart_907620 : Nat := 118140960795 + 907620 * 2 ^ 59
def prefixEnd_907620 : Nat := 4983230072969 + 3 ^ 40 * 907620 * 2
def baseEnd_907620 : Nat := 414262499230083703356389

theorem tailTrace_907620 : CollatzResearch.WordTrace tailWord_907620 prefixEnd_907620 414262499230083703356389 := by
  unfold tailWord_907620
  simp only [CollatzResearch.WordTrace]
  refine ⟨16551810485927612000100157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22069080647903482666800209 16551810485927612000100157)
  ·
    refine ⟨6206928932222854500037559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16551810485927612000100157 6206928932222854500037559)
    ·
      refine ⟨9310393398334281750056339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6206928932222854500037559 9310393398334281750056339)
      ·
        refine ⟨13965590097501422625084509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9310393398334281750056339 13965590097501422625084509)
        ·
          refine ⟨5237096286563033484406691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13965590097501422625084509 5237096286563033484406691)
          ·
            refine ⟨7855644429844550226610037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5237096286563033484406691 7855644429844550226610037)
            ·
              refine ⟨736466665297926583744691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7855644429844550226610037 736466665297926583744691)
              ·
                refine ⟨1104699997946889875617037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 736466665297926583744691 1104699997946889875617037)
                ·
                  refine ⟨414262499230083703356389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1104699997946889875617037 414262499230083703356389)
                  ·
                    rfl

theorem cell20_907620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 5, 1, 3].length) (baseStart_907620 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_907620 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_907620 prefixEnd_907620 := by exact prefixLift 907620
  have htrace : WordTrace (prefixWord ++ tailWord_907620) baseStart_907620 baseEnd_907620 := by
    simpa [prefixWord, tailWord_907620, baseEnd_907620] using wordTrace_append hprefix tailTrace_907620
  have hstable : (prefixWord ++ tailWord_907620).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907620).length < 2 ^ (prefixWord ++ tailWord_907620).sum := by decide
  have hdescent : baseEnd_907620 < baseStart_907620 := by decide
  rcases family_descends (prefixWord ++ tailWord_907620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907631 : List Nat := [1, 1, 2, 1, 3, 1, 2, 3, 6]
def baseStart_907631 : Nat := 118140960795 + 907631 * 2 ^ 59
def prefixEnd_907631 : Nat := 4983230072969 + 3 ^ 40 * 907631 * 2
def baseEnd_907631 : Nat := 414267519929816553989677

theorem tailTrace_907631 : CollatzResearch.WordTrace tailWord_907631 prefixEnd_907631 414267519929816553989677 := by
  unfold tailWord_907631
  simp only [CollatzResearch.WordTrace]
  refine ⟨33104022174815372878850747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22069348116543581919233831 33104022174815372878850747)
  ·
    refine ⟨49656033262223059318276121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33104022174815372878850747 49656033262223059318276121)
    ·
      refine ⟨37242024946667294488707091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49656033262223059318276121 37242024946667294488707091)
      ·
        refine ⟨55863037420000941733060637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37242024946667294488707091 55863037420000941733060637)
        ·
          refine ⟨20948639032500353149897739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55863037420000941733060637 20948639032500353149897739)
          ·
            refine ⟨31422958548750529724846609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20948639032500353149897739 31422958548750529724846609)
            ·
              refine ⟨23567218911562897293634957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31422958548750529724846609 23567218911562897293634957)
              ·
                refine ⟨8837707091836086485113109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23567218911562897293634957 8837707091836086485113109)
                ·
                  refine ⟨414267519929816553989677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8837707091836086485113109 414267519929816553989677)
                  ·
                    rfl

theorem cell20_907631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 3, 6].length) (baseStart_907631 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_907631 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_907631 prefixEnd_907631 := by exact prefixLift 907631
  have htrace : WordTrace (prefixWord ++ tailWord_907631) baseStart_907631 baseEnd_907631 := by
    simpa [prefixWord, tailWord_907631, baseEnd_907631] using wordTrace_append hprefix tailTrace_907631
  have hstable : (prefixWord ++ tailWord_907631).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907631).length < 2 ^ (prefixWord ++ tailWord_907631).sum := by decide
  have hdescent : baseEnd_907631 < baseStart_907631 := by decide
  rcases family_descends (prefixWord ++ tailWord_907631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907634 : List Nat := [3, 2, 1, 2, 1, 3, 4, 4]
def baseStart_907634 : Nat := 118140960795 + 907634 * 2 ^ 59
def prefixEnd_907634 : Nat := 4983230072969 + 3 ^ 40 * 907634 * 2
def baseEnd_907634 : Nat := 138089629737187292296555

theorem tailTrace_907634 : CollatzResearch.WordTrace tailWord_907634 prefixEnd_907634 138089629737187292296555 := by
  unfold tailWord_907634
  simp only [CollatzResearch.WordTrace]
  refine ⟨8276032898451126097802489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22069421062536336260806637 8276032898451126097802489)
  ·
    refine ⟨6207024673838344573351867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8276032898451126097802489 6207024673838344573351867)
    ·
      refine ⟨9310537010757516860027801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6207024673838344573351867 9310537010757516860027801)
      ·
        refine ⟨6982902758068137645020851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9310537010757516860027801 6982902758068137645020851)
        ·
          refine ⟨10474354137102206467531277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6982902758068137645020851 10474354137102206467531277)
          ·
            refine ⟨3927882801413327425324229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10474354137102206467531277 3927882801413327425324229)
            ·
              refine ⟨736478025264998892248293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3927882801413327425324229 736478025264998892248293)
              ·
                refine ⟨138089629737187292296555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 736478025264998892248293 138089629737187292296555)
                ·
                  rfl

theorem cell20_907634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 4, 4].length) (baseStart_907634 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_907634 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_907634 prefixEnd_907634 := by exact prefixLift 907634
  have htrace : WordTrace (prefixWord ++ tailWord_907634) baseStart_907634 baseEnd_907634 := by
    simpa [prefixWord, tailWord_907634, baseEnd_907634] using wordTrace_append hprefix tailTrace_907634
  have hstable : (prefixWord ++ tailWord_907634).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907634).length < 2 ^ (prefixWord ++ tailWord_907634).sum := by decide
  have hdescent : baseEnd_907634 < baseStart_907634 := by decide
  rcases family_descends (prefixWord ++ tailWord_907634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907672 : List Nat := [2, 1, 2, 5, 1, 2, 2, 5]
def baseStart_907672 : Nat := 118140960795 + 907672 * 2 ^ 59
def prefixEnd_907672 : Nat := 4983230072969 + 3 ^ 40 * 907672 * 2
def baseEnd_907672 : Nat := 138095411149000877874281

theorem tailTrace_907672 : CollatzResearch.WordTrace tailWord_907672 prefixEnd_907672 138095411149000877874281 := by
  unfold tailWord_907672
  simp only [CollatzResearch.WordTrace]
  refine ⟨16552758783833418440546635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22070345045111224587395513 16552758783833418440546635)
  ·
    refine ⟨24829138175750127660819953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16552758783833418440546635 24829138175750127660819953)
    ·
      refine ⟨18621853631812595745614965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24829138175750127660819953 18621853631812595745614965)
      ·
        refine ⟨1745798777982430851151403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18621853631812595745614965 1745798777982430851151403)
        ·
          refine ⟨2618698166973646276727105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1745798777982430851151403 2618698166973646276727105)
          ·
            refine ⟨1964023625230234707545329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2618698166973646276727105 1964023625230234707545329)
            ·
              refine ⟨1473017718922676030658997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1964023625230234707545329 1473017718922676030658997)
              ·
                refine ⟨138095411149000877874281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1473017718922676030658997 138095411149000877874281)
                ·
                  rfl

theorem cell20_907672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 2, 5].length) (baseStart_907672 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_907672 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_907672 prefixEnd_907672 := by exact prefixLift 907672
  have htrace : WordTrace (prefixWord ++ tailWord_907672) baseStart_907672 baseEnd_907672 := by
    simpa [prefixWord, tailWord_907672, baseEnd_907672] using wordTrace_append hprefix tailTrace_907672
  have hstable : (prefixWord ++ tailWord_907672).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907672).length < 2 ^ (prefixWord ++ tailWord_907672).sum := by decide
  have hdescent : baseEnd_907672 < baseStart_907672 := by decide
  rcases family_descends (prefixWord ++ tailWord_907672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907679 : List Nat := [1, 1, 2, 5, 1, 1, 3, 3, 3]
def baseStart_907679 : Nat := 118140960795 + 907679 * 2 ^ 59
def prefixEnd_907679 : Nat := 4983230072969 + 3 ^ 40 * 907679 * 2
def baseEnd_907679 : Nat := 414289428437741720389481

theorem tailTrace_907679 : CollatzResearch.WordTrace tailWord_907679 prefixEnd_907679 414289428437741720389481 := by
  unfold tailWord_907679
  simp only [CollatzResearch.WordTrace]
  refine ⟨33105772878641477076598091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22070515252427651384398727 33105772878641477076598091)
  ·
    refine ⟨49658659317962215614897137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33105772878641477076598091 49658659317962215614897137)
    ·
      refine ⟨37243994488471661711172853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49658659317962215614897137 37243994488471661711172853)
      ·
        refine ⟨3491624483294218285422455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37243994488471661711172853 3491624483294218285422455)
        ·
          refine ⟨5237436724941327428133683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3491624483294218285422455 5237436724941327428133683)
          ·
            refine ⟨7856155087411991142200525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5237436724941327428133683 7856155087411991142200525)
            ·
              refine ⟨2946058157779496678325197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7856155087411991142200525 2946058157779496678325197)
              ·
                refine ⟨1104771809167311254371949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2946058157779496678325197 1104771809167311254371949)
                ·
                  refine ⟨414289428437741720389481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1104771809167311254371949 414289428437741720389481)
                  ·
                    rfl

theorem cell20_907679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 3, 3].length) (baseStart_907679 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_907679 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_907679 prefixEnd_907679 := by exact prefixLift 907679
  have htrace : WordTrace (prefixWord ++ tailWord_907679) baseStart_907679 baseEnd_907679 := by
    simpa [prefixWord, tailWord_907679, baseEnd_907679] using wordTrace_append hprefix tailTrace_907679
  have hstable : (prefixWord ++ tailWord_907679).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907679).length < 2 ^ (prefixWord ++ tailWord_907679).sum := by decide
  have hdescent : baseEnd_907679 < baseStart_907679 := by decide
  rcases family_descends (prefixWord ++ tailWord_907679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907716 : List Nat := [2, 3, 3, 2, 2, 2, 2, 2, 2]
def baseStart_907716 : Nat := 118140960795 + 907716 * 2 ^ 59
def prefixEnd_907716 : Nat := 4983230072969 + 3 ^ 40 * 907716 * 2
def baseEnd_907716 : Nat := 414306316245934036155997

theorem tailTrace_907716 : CollatzResearch.WordTrace tailWord_907716 prefixEnd_907716 414306316245934036155997 := by
  unfold tailWord_907716
  simp only [CollatzResearch.WordTrace]
  refine ⟨16553561189753716197847501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22071414919671621597130001 16553561189753716197847501)
  ·
    refine ⟨6207585446157643574192813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16553561189753716197847501 6207585446157643574192813)
    ·
      refine ⟨2327844542309116340322305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6207585446157643574192813 2327844542309116340322305)
      ·
        refine ⟨1745883406731837255241729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2327844542309116340322305 1745883406731837255241729)
        ·
          refine ⟨1309412555048877941431297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1745883406731837255241729 1309412555048877941431297)
          ·
            refine ⟨982059416286658456073473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1309412555048877941431297 982059416286658456073473)
            ·
              refine ⟨736544562214993842055105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 982059416286658456073473 736544562214993842055105)
              ·
                refine ⟨552408421661245381541329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 736544562214993842055105 552408421661245381541329)
                ·
                  refine ⟨414306316245934036155997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 552408421661245381541329 414306316245934036155997)
                  ·
                    rfl

theorem cell20_907716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 2, 2, 2].length) (baseStart_907716 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_907716 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_907716 prefixEnd_907716 := by exact prefixLift 907716
  have htrace : WordTrace (prefixWord ++ tailWord_907716) baseStart_907716 baseEnd_907716 := by
    simpa [prefixWord, tailWord_907716, baseEnd_907716] using wordTrace_append hprefix tailTrace_907716
  have hstable : (prefixWord ++ tailWord_907716).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907716).length < 2 ^ (prefixWord ++ tailWord_907716).sum := by decide
  have hdescent : baseEnd_907716 < baseStart_907716 := by decide
  rcases family_descends (prefixWord ++ tailWord_907716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907720 : List Nat := [2, 1, 3, 1, 3, 2, 4, 2, 2]
def baseStart_907720 : Nat := 118140960795 + 907720 * 2 ^ 59
def prefixEnd_907720 : Nat := 4983230072969 + 3 ^ 40 * 907720 * 2
def baseEnd_907720 : Nat := 414308141954927800022647

theorem tailTrace_907720 : CollatzResearch.WordTrace tailWord_907720 prefixEnd_907720 414308141954927800022647 := by
  unfold tailWord_907720
  simp only [CollatzResearch.WordTrace]
  refine ⟨16553634135746470539420307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22071512180995294052560409 16553634135746470539420307)
  ·
    refine ⟨24830451203619705809130461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16553634135746470539420307 24830451203619705809130461)
    ·
      refine ⟨9311419201357389678423923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24830451203619705809130461 9311419201357389678423923)
      ·
        refine ⟨13967128802036084517635885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9311419201357389678423923 13967128802036084517635885)
        ·
          refine ⟨5237673300763531694113457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13967128802036084517635885 5237673300763531694113457)
          ·
            refine ⟨3928254975572648770585093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5237673300763531694113457 3928254975572648770585093)
            ·
              refine ⟨736547807919871644484705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3928254975572648770585093 736547807919871644484705)
              ·
                refine ⟨552410855939903733363529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 736547807919871644484705 552410855939903733363529)
                ·
                  refine ⟨414308141954927800022647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 552410855939903733363529 414308141954927800022647)
                  ·
                    rfl

theorem cell20_907720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 4, 2, 2].length) (baseStart_907720 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_907720 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_907720 prefixEnd_907720 := by exact prefixLift 907720
  have htrace : WordTrace (prefixWord ++ tailWord_907720) baseStart_907720 baseEnd_907720 := by
    simpa [prefixWord, tailWord_907720, baseEnd_907720] using wordTrace_append hprefix tailTrace_907720
  have hstable : (prefixWord ++ tailWord_907720).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907720).length < 2 ^ (prefixWord ++ tailWord_907720).sum := by decide
  have hdescent : baseEnd_907720 < baseStart_907720 := by decide
  rcases family_descends (prefixWord ++ tailWord_907720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907734 : List Nat := [5, 2, 1, 1, 1, 1, 1, 5, 3]
def baseStart_907734 : Nat := 118140960795 + 907734 * 2 ^ 59
def prefixEnd_907734 : Nat := 4983230072969 + 3 ^ 40 * 907734 * 2
def baseEnd_907734 : Nat := 414314531936405973555923

theorem tailTrace_907734 : CollatzResearch.WordTrace tailWord_907734 prefixEnd_907734 414314531936405973555923 := by
  unfold tailWord_907734
  simp only [CollatzResearch.WordTrace]
  refine ⟨2069236180840138841865641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22071852595628147646566837 2069236180840138841865641)
  ·
    refine ⟨1551927135630104131399231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2069236180840138841865641 1551927135630104131399231)
    ·
      refine ⟨2327890703445156197098847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1551927135630104131399231 2327890703445156197098847)
      ·
        refine ⟨3491836055167734295648271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2327890703445156197098847 3491836055167734295648271)
        ·
          refine ⟨5237754082751601443472407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3491836055167734295648271 5237754082751601443472407)
          ·
            refine ⟨7856631124127402165208611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5237754082751601443472407 7856631124127402165208611)
            ·
              refine ⟨11784946686191103247812917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7856631124127402165208611 11784946686191103247812917)
              ·
                refine ⟨1104838751830415929482461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11784946686191103247812917 1104838751830415929482461)
                ·
                  refine ⟨414314531936405973555923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1104838751830415929482461 414314531936405973555923)
                  ·
                    rfl

theorem cell20_907734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_907734 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_907734 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_907734 prefixEnd_907734 := by exact prefixLift 907734
  have htrace : WordTrace (prefixWord ++ tailWord_907734) baseStart_907734 baseEnd_907734 := by
    simpa [prefixWord, tailWord_907734, baseEnd_907734] using wordTrace_append hprefix tailTrace_907734
  have hstable : (prefixWord ++ tailWord_907734).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907734).length < 2 ^ (prefixWord ++ tailWord_907734).sum := by decide
  have hdescent : baseEnd_907734 < baseStart_907734 := by decide
  rcases family_descends (prefixWord ++ tailWord_907734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907758 : List Nat := [4, 1, 2, 1, 2, 3, 2, 3, 2]
def baseStart_907758 : Nat := 118140960795 + 907758 * 2 ^ 59
def prefixEnd_907758 : Nat := 4983230072969 + 3 ^ 40 * 907758 * 2
def baseEnd_907758 : Nat := 414325486190368556755825

theorem tailTrace_907758 : CollatzResearch.WordTrace tailWord_907758 prefixEnd_907758 414325486190368556755825 := by
  unfold tailWord_907758
  simp only [CollatzResearch.WordTrace]
  refine ⟨4138581780669409196090491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22072436163570182379149285 4138581780669409196090491)
  ·
    refine ⟨6207872671004113794135737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4138581780669409196090491 6207872671004113794135737)
    ·
      refine ⟨4655904503253085345601803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6207872671004113794135737 4655904503253085345601803)
      ·
        refine ⟨6983856754879628018402705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4655904503253085345601803 6983856754879628018402705)
        ·
          refine ⟨5237892566159721013802029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6983856754879628018402705 5237892566159721013802029)
          ·
            refine ⟨1964209712309895380175761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5237892566159721013802029 1964209712309895380175761)
            ·
              refine ⟨1473157284232421535131821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1964209712309895380175761 1473157284232421535131821)
              ·
                refine ⟨552433981587158075674433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1473157284232421535131821 552433981587158075674433)
                ·
                  refine ⟨414325486190368556755825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 552433981587158075674433 414325486190368556755825)
                  ·
                    rfl

theorem cell20_907758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 2, 3, 2].length) (baseStart_907758 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_907758 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_907758 prefixEnd_907758 := by exact prefixLift 907758
  have htrace : WordTrace (prefixWord ++ tailWord_907758) baseStart_907758 baseEnd_907758 := by
    simpa [prefixWord, tailWord_907758, baseEnd_907758] using wordTrace_append hprefix tailTrace_907758
  have hstable : (prefixWord ++ tailWord_907758).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907758).length < 2 ^ (prefixWord ++ tailWord_907758).sum := by decide
  have hdescent : baseEnd_907758 < baseStart_907758 := by decide
  rcases family_descends (prefixWord ++ tailWord_907758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907800 : List Nat := [2, 1, 2, 3, 3, 1, 2, 2, 4]
def baseStart_907800 : Nat := 118140960795 + 907800 * 2 ^ 59
def prefixEnd_907800 : Nat := 4983230072969 + 3 ^ 40 * 907800 * 2
def baseEnd_907800 : Nat := 414344656134803077355653

theorem tailTrace_907800 : CollatzResearch.WordTrace tailWord_907800 prefixEnd_907800 414344656134803077355653 := by
  unfold tailWord_907800
  simp only [CollatzResearch.WordTrace]
  refine ⟨16555093055601557370876427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22073457407468743161168569 16555093055601557370876427)
  ·
    refine ⟨24832639583402336056314641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16555093055601557370876427 24832639583402336056314641)
    ·
      refine ⟨18624479687551752042235981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24832639583402336056314641 18624479687551752042235981)
      ·
        refine ⟨6984179882831907015838493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18624479687551752042235981 6984179882831907015838493)
        ·
          refine ⟨2619067456061965130939435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6984179882831907015838493 2619067456061965130939435)
          ·
            refine ⟨3928601184092947696409153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2619067456061965130939435 3928601184092947696409153)
            ·
              refine ⟨2946450888069710772306865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3928601184092947696409153 2946450888069710772306865)
              ·
                refine ⟨2209838166052283079230149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2946450888069710772306865 2209838166052283079230149)
                ·
                  refine ⟨414344656134803077355653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2209838166052283079230149 414344656134803077355653)
                  ·
                    rfl

theorem cell20_907800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 2, 4].length) (baseStart_907800 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_907800 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_907800 prefixEnd_907800 := by exact prefixLift 907800
  have htrace : WordTrace (prefixWord ++ tailWord_907800) baseStart_907800 baseEnd_907800 := by
    simpa [prefixWord, tailWord_907800, baseEnd_907800] using wordTrace_append hprefix tailTrace_907800
  have hstable : (prefixWord ++ tailWord_907800).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907800).length < 2 ^ (prefixWord ++ tailWord_907800).sum := by decide
  have hdescent : baseEnd_907800 < baseStart_907800 := by decide
  rcases family_descends (prefixWord ++ tailWord_907800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907834 : List Nat := [3, 1, 1, 1, 3, 4, 3, 2, 2]
def baseStart_907834 : Nat := 118140960795 + 907834 * 2 ^ 59
def prefixEnd_907834 : Nat := 4983230072969 + 3 ^ 40 * 907834 * 2
def baseEnd_907834 : Nat := 414360174661250070222181

theorem tailTrace_907834 : CollatzResearch.WordTrace tailWord_907834 prefixEnd_907834 414360174661250070222181 := by
  unfold tailWord_907834
  simp only [CollatzResearch.WordTrace]
  refine ⟨8277856548269984637122639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22074284128719959032327037 8277856548269984637122639)
  ·
    refine ⟨12416784822404976955683959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8277856548269984637122639 12416784822404976955683959)
    ·
      refine ⟨18625177233607465433525939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12416784822404976955683959 18625177233607465433525939)
      ·
        refine ⟨27937765850411198150288909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18625177233607465433525939 27937765850411198150288909)
        ·
          refine ⟨10476662193904199306358341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27937765850411198150288909 10476662193904199306358341)
          ·
            refine ⟨1964374161357037369942189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10476662193904199306358341 1964374161357037369942189)
            ·
              refine ⟨736640310508889013728321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1964374161357037369942189 736640310508889013728321)
              ·
                refine ⟨552480232881666760296241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 736640310508889013728321 552480232881666760296241)
                ·
                  refine ⟨414360174661250070222181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 552480232881666760296241 414360174661250070222181)
                  ·
                    rfl

theorem cell20_907834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 3, 2, 2].length) (baseStart_907834 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_907834 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_907834 prefixEnd_907834 := by exact prefixLift 907834
  have htrace : WordTrace (prefixWord ++ tailWord_907834) baseStart_907834 baseEnd_907834 := by
    simpa [prefixWord, tailWord_907834, baseEnd_907834] using wordTrace_append hprefix tailTrace_907834
  have hstable : (prefixWord ++ tailWord_907834).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907834).length < 2 ^ (prefixWord ++ tailWord_907834).sum := by decide
  have hdescent : baseEnd_907834 < baseStart_907834 := by decide
  rcases family_descends (prefixWord ++ tailWord_907834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907844 : List Nat := [2, 3, 5, 1, 1, 1, 1, 3, 3]
def baseStart_907844 : Nat := 118140960795 + 907844 * 2 ^ 59
def prefixEnd_907844 : Nat := 4983230072969 + 3 ^ 40 * 907844 * 2
def baseEnd_907844 : Nat := 414364738933734479888807

theorem tailTrace_907844 : CollatzResearch.WordTrace tailWord_907844 prefixEnd_907844 414364738933734479888807 := by
  unfold tailWord_907844
  simp only [CollatzResearch.WordTrace]
  refine ⟨16555895461521855128177293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22074527282029140170903057 16555895461521855128177293)
  ·
    refine ⟨6208460798070695673066485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16555895461521855128177293 6208460798070695673066485)
    ·
      refine ⟨582043199819127719349983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6208460798070695673066485 582043199819127719349983)
      ·
        refine ⟨873064799728691579024975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 582043199819127719349983 873064799728691579024975)
        ·
          refine ⟨1309597199593037368537463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 873064799728691579024975 1309597199593037368537463)
          ·
            refine ⟨1964395799389556052806195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1309597199593037368537463 1964395799389556052806195)
            ·
              refine ⟨2946593699084334079209293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1964395799389556052806195 2946593699084334079209293)
              ·
                refine ⟨1104972637156625279703485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2946593699084334079209293 1104972637156625279703485)
                ·
                  refine ⟨414364738933734479888807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1104972637156625279703485 414364738933734479888807)
                  ·
                    rfl

theorem cell20_907844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 3, 3].length) (baseStart_907844 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_907844 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_907844 prefixEnd_907844 := by exact prefixLift 907844
  have htrace : WordTrace (prefixWord ++ tailWord_907844) baseStart_907844 baseEnd_907844 := by
    simpa [prefixWord, tailWord_907844, baseEnd_907844] using wordTrace_append hprefix tailTrace_907844
  have hstable : (prefixWord ++ tailWord_907844).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907844).length < 2 ^ (prefixWord ++ tailWord_907844).sum := by decide
  have hdescent : baseEnd_907844 < baseStart_907844 := by decide
  rcases family_descends (prefixWord ++ tailWord_907844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907845 : List Nat := [1, 3, 1, 1, 1, 6, 2, 5]
def baseStart_907845 : Nat := 118140960795 + 907845 * 2 ^ 59
def prefixEnd_907845 : Nat := 4983230072969 + 3 ^ 40 * 907845 * 2
def baseEnd_907845 : Nat := 138121731786994306951823

theorem tailTrace_907845 : CollatzResearch.WordTrace tailWord_907845 prefixEnd_907845 138121731786994306951823 := by
  unfold tailWord_907845
  simp only [CollatzResearch.WordTrace]
  refine ⟨33111827396040087427140989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22074551597360058284760659 33111827396040087427140989)
  ·
    refine ⟨12416935273515032785177871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33111827396040087427140989 12416935273515032785177871)
    ·
      refine ⟨18625402910272549177766807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12416935273515032785177871 18625402910272549177766807)
      ·
        refine ⟨27938104365408823766650211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18625402910272549177766807 27938104365408823766650211)
        ·
          refine ⟨41907156548113235649975317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27938104365408823766650211 41907156548113235649975317)
          ·
            refine ⟨1964397963192807921092593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 41907156548113235649975317 1964397963192807921092593)
            ·
              refine ⟨1473298472394605940819445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1964397963192807921092593 1473298472394605940819445)
              ·
                refine ⟨138121731786994306951823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1473298472394605940819445 138121731786994306951823)
                ·
                  rfl

theorem cell20_907845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 2, 5].length) (baseStart_907845 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_907845 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_907845 prefixEnd_907845 := by exact prefixLift 907845
  have htrace : WordTrace (prefixWord ++ tailWord_907845) baseStart_907845 baseEnd_907845 := by
    simpa [prefixWord, tailWord_907845, baseEnd_907845] using wordTrace_append hprefix tailTrace_907845
  have hstable : (prefixWord ++ tailWord_907845).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907845).length < 2 ^ (prefixWord ++ tailWord_907845).sum := by decide
  have hdescent : baseEnd_907845 < baseStart_907845 := by decide
  rcases family_descends (prefixWord ++ tailWord_907845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907886 : List Nat := [4, 1, 2, 2, 2, 2, 2, 2, 3]
def baseStart_907886 : Nat := 118140960795 + 907886 * 2 ^ 59
def prefixEnd_907886 : Nat := 4983230072969 + 3 ^ 40 * 907886 * 2
def baseEnd_907886 : Nat := 414383908878169000488635

theorem tailTrace_907886 : CollatzResearch.WordTrace tailWord_907886 prefixEnd_907886 414383908878169000488635 := by
  unfold tailWord_907886
  simp only [CollatzResearch.WordTrace]
  refine ⟨4139165348611443928672939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22075548525927700952922341 4139165348611443928672939)
  ·
    refine ⟨6208748022917165893009409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4139165348611443928672939 6208748022917165893009409)
    ·
      refine ⟨4656561017187874419757057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6208748022917165893009409 4656561017187874419757057)
      ·
        refine ⟨3492420762890905814817793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4656561017187874419757057 3492420762890905814817793)
        ·
          refine ⟨2619315572168179361113345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3492420762890905814817793 2619315572168179361113345)
          ·
            refine ⟨1964486679126134520835009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2619315572168179361113345 1964486679126134520835009)
            ·
              refine ⟨1473365009344600890626257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1964486679126134520835009 1473365009344600890626257)
              ·
                refine ⟨1105023757008450667969693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1473365009344600890626257 1105023757008450667969693)
                ·
                  refine ⟨414383908878169000488635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1105023757008450667969693 414383908878169000488635)
                  ·
                    rfl

theorem cell20_907886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 2, 2, 3].length) (baseStart_907886 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_907886 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_907886 prefixEnd_907886 := by exact prefixLift 907886
  have htrace : WordTrace (prefixWord ++ tailWord_907886) baseStart_907886 baseEnd_907886 := by
    simpa [prefixWord, tailWord_907886, baseEnd_907886] using wordTrace_append hprefix tailTrace_907886
  have hstable : (prefixWord ++ tailWord_907886).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907886).length < 2 ^ (prefixWord ++ tailWord_907886).sum := by decide
  have hdescent : baseEnd_907886 < baseStart_907886 := by decide
  rcases family_descends (prefixWord ++ tailWord_907886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907928 : List Nat := [2, 1, 2, 4, 1, 1, 2, 2, 5]
def baseStart_907928 : Nat := 118140960795 + 907928 * 2 ^ 59
def prefixEnd_907928 : Nat := 4983230072969 + 3 ^ 40 * 907928 * 2
def baseEnd_907928 : Nat := 414403078822603521088463

theorem tailTrace_907928 : CollatzResearch.WordTrace tailWord_907928 prefixEnd_907928 414403078822603521088463 := by
  unfold tailWord_907928
  simp only [CollatzResearch.WordTrace]
  refine ⟨16557427327369696301206219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22076569769826261734941625 16557427327369696301206219)
  ·
    refine ⟨24836140991054544451809329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16557427327369696301206219 24836140991054544451809329)
    ·
      refine ⟨18627105743290908338856997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24836140991054544451809329 18627105743290908338856997)
      ·
        refine ⟨3492582326867045313535687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18627105743290908338856997 3492582326867045313535687)
        ·
          refine ⟨5238873490300567970303531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3492582326867045313535687 5238873490300567970303531)
          ·
            refine ⟨7858310235450851955455297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5238873490300567970303531 7858310235450851955455297)
            ·
              refine ⟨5893732676588138966591473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7858310235450851955455297 5893732676588138966591473)
              ·
                refine ⟨4420299507441104224943605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5893732676588138966591473 4420299507441104224943605)
                ·
                  refine ⟨414403078822603521088463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4420299507441104224943605 414403078822603521088463)
                  ·
                    rfl

theorem cell20_907928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 2, 5].length) (baseStart_907928 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_907928 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_907928 prefixEnd_907928 := by exact prefixLift 907928
  have htrace : WordTrace (prefixWord ++ tailWord_907928) baseStart_907928 baseEnd_907928 := by
    simpa [prefixWord, tailWord_907928, baseEnd_907928] using wordTrace_append hprefix tailTrace_907928
  have hstable : (prefixWord ++ tailWord_907928).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907928).length < 2 ^ (prefixWord ++ tailWord_907928).sum := by decide
  have hdescent : baseEnd_907928 < baseStart_907928 := by decide
  rcases family_descends (prefixWord ++ tailWord_907928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907958 : List Nat := [5, 1, 3, 1, 2, 1, 3, 1, 3]
def baseStart_907958 : Nat := 118140960795 + 907958 * 2 ^ 59
def prefixEnd_907958 : Nat := 4983230072969 + 3 ^ 40 * 907958 * 2
def baseEnd_907958 : Nat := 414416771640056750088341

theorem tailTrace_907958 : CollatzResearch.WordTrace tailWord_907958 prefixEnd_907958 414416771640056750088341 := by
  unfold tailWord_907958
  simp only [CollatzResearch.WordTrace]
  refine ⟨2069746802789419232875283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22077299229753805150669685 2069746802789419232875283)
  ·
    refine ⟨3104620204184128849312925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2069746802789419232875283 3104620204184128849312925)
    ·
      refine ⟨1164232576569048318492347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3104620204184128849312925 1164232576569048318492347)
      ·
        refine ⟨1746348864853572477738521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1164232576569048318492347 1746348864853572477738521)
        ·
          refine ⟨1309761648640179358303891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1746348864853572477738521 1309761648640179358303891)
          ·
            refine ⟨1964642472960269037455837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1309761648640179358303891 1964642472960269037455837)
            ·
              refine ⟨736740927360100889045939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1964642472960269037455837 736740927360100889045939)
              ·
                refine ⟨1105111391040151333568909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 736740927360100889045939 1105111391040151333568909)
                ·
                  refine ⟨414416771640056750088341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1105111391040151333568909 414416771640056750088341)
                  ·
                    rfl

theorem cell20_907958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 3, 1, 3].length) (baseStart_907958 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_907958 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_907958 prefixEnd_907958 := by exact prefixLift 907958
  have htrace : WordTrace (prefixWord ++ tailWord_907958) baseStart_907958 baseEnd_907958 := by
    simpa [prefixWord, tailWord_907958, baseEnd_907958] using wordTrace_append hprefix tailTrace_907958
  have hstable : (prefixWord ++ tailWord_907958).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907958).length < 2 ^ (prefixWord ++ tailWord_907958).sum := by decide
  have hdescent : baseEnd_907958 < baseStart_907958 := by decide
  rcases family_descends (prefixWord ++ tailWord_907958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_907976 : List Nat := [2, 1, 3, 1, 2, 5, 2, 4]
def baseStart_907976 : Nat := 118140960795 + 907976 * 2 ^ 59
def prefixEnd_907976 : Nat := 4983230072969 + 3 ^ 40 * 907976 * 2
def baseEnd_907976 : Nat := 138141662443509562496089

theorem tailTrace_907976 : CollatzResearch.WordTrace tailWord_907976 prefixEnd_907976 138141662443509562496089 := by
  unfold tailWord_907976
  simp only [CollatzResearch.WordTrace]
  refine ⟨16558302679282748400079891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22077736905710331200106521 16558302679282748400079891)
  ·
    refine ⟨24837454018924122600119837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16558302679282748400079891 24837454018924122600119837)
    ·
      refine ⟨9314045257096545975044939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24837454018924122600119837 9314045257096545975044939)
      ·
        refine ⟨13971067885644818962567409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9314045257096545975044939 13971067885644818962567409)
        ·
          refine ⟨10478300914233614221925557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13971067885644818962567409 10478300914233614221925557)
          ·
            refine ⟨982340710709401333305521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10478300914233614221925557 982340710709401333305521)
            ·
              refine ⟨736755533032050999979141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 982340710709401333305521 736755533032050999979141)
              ·
                refine ⟨138141662443509562496089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 736755533032050999979141 138141662443509562496089)
                ·
                  rfl

theorem cell20_907976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 2, 4].length) (baseStart_907976 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_907976 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_907976 prefixEnd_907976 := by exact prefixLift 907976
  have htrace : WordTrace (prefixWord ++ tailWord_907976) baseStart_907976 baseEnd_907976 := by
    simpa [prefixWord, tailWord_907976, baseEnd_907976] using wordTrace_append hprefix tailTrace_907976
  have hstable : (prefixWord ++ tailWord_907976).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_907976).length < 2 ^ (prefixWord ++ tailWord_907976).sum := by decide
  have hdescent : baseEnd_907976 < baseStart_907976 := by decide
  rcases family_descends (prefixWord ++ tailWord_907976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908004 : List Nat := [2, 3, 1, 1, 1, 4, 2, 1, 5]
def baseStart_908004 : Nat := 118140960795 + 908004 * 2 ^ 59
def prefixEnd_908004 : Nat := 4983230072969 + 3 ^ 40 * 908004 * 2
def baseEnd_908004 : Nat := 414437767293485034554819

theorem tailTrace_908004 : CollatzResearch.WordTrace tailWord_908004 prefixEnd_908004 414437767293485034554819 := by
  unfold tailWord_908004
  simp only [CollatzResearch.WordTrace]
  refine ⟨16558813301232028791089533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22078417734976038388119377 16558813301232028791089533)
  ·
    refine ⟨6209554987962010796658575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16558813301232028791089533 6209554987962010796658575)
    ·
      refine ⟨9314332481943016194987863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6209554987962010796658575 9314332481943016194987863)
      ·
        refine ⟨13971498722914524292481795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9314332481943016194987863 13971498722914524292481795)
        ·
          refine ⟨20957248084371786438722693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13971498722914524292481795 20957248084371786438722693)
          ·
            refine ⟨3929484015819709957260505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20957248084371786438722693 3929484015819709957260505)
            ·
              refine ⟨2947113011864782467945379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3929484015819709957260505 2947113011864782467945379)
              ·
                refine ⟨4420669517797173701918069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2947113011864782467945379 4420669517797173701918069)
                ·
                  refine ⟨414437767293485034554819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4420669517797173701918069 414437767293485034554819)
                  ·
                    rfl

theorem cell20_908004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 1, 5].length) (baseStart_908004 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_908004 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_908004 prefixEnd_908004 := by exact prefixLift 908004
  have htrace : WordTrace (prefixWord ++ tailWord_908004) baseStart_908004 baseEnd_908004 := by
    simpa [prefixWord, tailWord_908004, baseEnd_908004] using wordTrace_append hprefix tailTrace_908004
  have hstable : (prefixWord ++ tailWord_908004).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908004).length < 2 ^ (prefixWord ++ tailWord_908004).sum := by decide
  have hdescent : baseEnd_908004 < baseStart_908004 := by decide
  rcases family_descends (prefixWord ++ tailWord_908004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908087 : List Nat := [1, 1, 3, 1, 2, 1, 5, 2, 4]
def baseStart_908087 : Nat := 118140960795 + 908087 * 2 ^ 59
def prefixEnd_908087 : Nat := 4983230072969 + 3 ^ 40 * 908087 * 2
def baseEnd_908087 : Nat := 414475650755105634787813

theorem tailTrace_908087 : CollatzResearch.WordTrace tailWord_908087 prefixEnd_908087 414475650755105634787813 := by
  unfold tailWord_908087
  simp only [CollatzResearch.WordTrace]
  refine ⟨33120653861163362757450515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22080435907442241838300343 33120653861163362757450515)
  ·
    refine ⟨49680980791745044136175773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33120653861163362757450515 49680980791745044136175773)
    ·
      refine ⟨18630367796904391551065915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49680980791745044136175773 18630367796904391551065915)
      ·
        refine ⟨27945551695356587326598873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18630367796904391551065915 27945551695356587326598873)
        ·
          refine ⟨20959163771517440494949155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27945551695356587326598873 20959163771517440494949155)
          ·
            refine ⟨31438745657276160742423733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20959163771517440494949155 31438745657276160742423733)
            ·
              refine ⟨2947382405369640069602225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31438745657276160742423733 2947382405369640069602225)
              ·
                refine ⟨2210536804027230052201669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2947382405369640069602225 2210536804027230052201669)
                ·
                  refine ⟨414475650755105634787813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2210536804027230052201669 414475650755105634787813)
                  ·
                    rfl

theorem cell20_908087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 2, 4].length) (baseStart_908087 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_908087 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_908087 prefixEnd_908087 := by exact prefixLift 908087
  have htrace : WordTrace (prefixWord ++ tailWord_908087) baseStart_908087 baseEnd_908087 := by
    simpa [prefixWord, tailWord_908087, baseEnd_908087] using wordTrace_append hprefix tailTrace_908087
  have hstable : (prefixWord ++ tailWord_908087).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908087).length < 2 ^ (prefixWord ++ tailWord_908087).sum := by decide
  have hdescent : baseEnd_908087 < baseStart_908087 := by decide
  rcases family_descends (prefixWord ++ tailWord_908087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908090 : List Nat := [3, 1, 1, 1, 6, 1, 3, 4]
def baseStart_908090 : Nat := 118140960795 + 908090 * 2 ^ 59
def prefixEnd_908090 : Nat := 4983230072969 + 3 ^ 40 * 908090 * 2
def baseEnd_908090 : Nat := 138159006678950319229267

theorem tailTrace_908090 : CollatzResearch.WordTrace tailWord_908090 prefixEnd_908090 138159006678950319229267 := by
  unfold tailWord_908090
  simp only [CollatzResearch.WordTrace]
  refine ⟨8280190820038123567452431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22080508853434996179873149 8280190820038123567452431)
  ·
    refine ⟨12420286230057185351178647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8280190820038123567452431 12420286230057185351178647)
    ·
      refine ⟨18630429345085778026767971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12420286230057185351178647 18630429345085778026767971)
      ·
        refine ⟨27945644017628667040151957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18630429345085778026767971 27945644017628667040151957)
        ·
          refine ⟨1309952063326343767507123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 27945644017628667040151957 1309952063326343767507123)
          ·
            refine ⟨1964928094989515651260685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1309952063326343767507123 1964928094989515651260685)
            ·
              refine ⟨736848035621068369222757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1964928094989515651260685 736848035621068369222757)
              ·
                refine ⟨138159006678950319229267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 736848035621068369222757 138159006678950319229267)
                ·
                  rfl

theorem cell20_908090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 3, 4].length) (baseStart_908090 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_908090 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_908090 prefixEnd_908090 := by exact prefixLift 908090
  have htrace : WordTrace (prefixWord ++ tailWord_908090) baseStart_908090 baseEnd_908090 := by
    simpa [prefixWord, tailWord_908090, baseEnd_908090] using wordTrace_append hprefix tailTrace_908090
  have hstable : (prefixWord ++ tailWord_908090).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908090).length < 2 ^ (prefixWord ++ tailWord_908090).sum := by decide
  have hdescent : baseEnd_908090 < baseStart_908090 := by decide
  rcases family_descends (prefixWord ++ tailWord_908090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908149 : List Nat := [1, 3, 4, 1, 1, 3, 1, 6]
def baseStart_908149 : Nat := 118140960795 + 908149 * 2 ^ 59
def prefixEnd_908149 : Nat := 4983230072969 + 3 ^ 40 * 908149 * 2
def baseEnd_908149 : Nat := 138167983081502991573631

theorem tailTrace_908149 : CollatzResearch.WordTrace tailWord_908149 prefixEnd_908149 138167983081502991573631 := by
  unfold tailWord_908149
  simp only [CollatzResearch.WordTrace]
  refine ⟨33122915186938747346207501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22081943457959164897471667 33122915186938747346207501)
  ·
    refine ⟨12421093195102030254827813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33122915186938747346207501 12421093195102030254827813)
    ·
      refine ⟨2328954974081630672780215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12421093195102030254827813 2328954974081630672780215)
      ·
        refine ⟨3493432461122446009170323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2328954974081630672780215 3493432461122446009170323)
        ·
          refine ⟨5240148691683669013755485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3493432461122446009170323 5240148691683669013755485)
          ·
            refine ⟨1965055759381375880158307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5240148691683669013755485 1965055759381375880158307)
            ·
              refine ⟨2947583639072063820237461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1965055759381375880158307 2947583639072063820237461)
              ·
                refine ⟨138167983081502991573631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2947583639072063820237461 138167983081502991573631)
                ·
                  rfl

theorem cell20_908149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 6].length) (baseStart_908149 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_908149 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_908149 prefixEnd_908149 := by exact prefixLift 908149
  have htrace : WordTrace (prefixWord ++ tailWord_908149) baseStart_908149 baseEnd_908149 := by
    simpa [prefixWord, tailWord_908149, baseEnd_908149] using wordTrace_append hprefix tailTrace_908149
  have hstable : (prefixWord ++ tailWord_908149).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908149).length < 2 ^ (prefixWord ++ tailWord_908149).sum := by decide
  have hdescent : baseEnd_908149 < baseStart_908149 := by decide
  rcases family_descends (prefixWord ++ tailWord_908149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908162 : List Nat := [3, 4, 2, 2, 2, 1, 6]
def baseStart_908162 : Nat := 118140960795 + 908162 * 2 ^ 59
def prefixEnd_908162 : Nat := 4983230072969 + 3 ^ 40 * 908162 * 2
def baseEnd_908162 : Nat := 46056653644304300809723

theorem tailTrace_908162 : CollatzResearch.WordTrace tailWord_908162 prefixEnd_908162 46056653644304300809723 := by
  unfold tailWord_908162
  simp only [CollatzResearch.WordTrace]
  refine ⟨8280847333972912641607685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22082259557261100377620493 8280847333972912641607685)
  ·
    refine ⟨1552658875119921120301441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8280847333972912641607685 1552658875119921120301441)
    ·
      refine ⟨1164494156339940840226081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1552658875119921120301441 1164494156339940840226081)
      ·
        refine ⟨873370617254955630169561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1164494156339940840226081 873370617254955630169561)
        ·
          refine ⟨655027962941216722627171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 873370617254955630169561 655027962941216722627171)
          ·
            refine ⟨982541944411825083940757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 655027962941216722627171 982541944411825083940757)
            ·
              refine ⟨46056653644304300809723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 982541944411825083940757 46056653644304300809723)
              ·
                rfl

theorem cell20_908162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 6].length) (baseStart_908162 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_908162 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_908162 prefixEnd_908162 := by exact prefixLift 908162
  have htrace : WordTrace (prefixWord ++ tailWord_908162) baseStart_908162 baseEnd_908162 := by
    simpa [prefixWord, tailWord_908162, baseEnd_908162] using wordTrace_append hprefix tailTrace_908162
  have hstable : (prefixWord ++ tailWord_908162).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908162).length < 2 ^ (prefixWord ++ tailWord_908162).sum := by decide
  have hdescent : baseEnd_908162 < baseStart_908162 := by decide
  rcases family_descends (prefixWord ++ tailWord_908162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908215 : List Nat := [1, 1, 3, 1, 3, 1, 2, 1, 7]
def baseStart_908215 : Nat := 118140960795 + 908215 * 2 ^ 59
def prefixEnd_908215 : Nat := 4983230072969 + 3 ^ 40 * 908215 * 2
def baseEnd_908215 : Nat := 414534073442906078520623

theorem tailTrace_908215 : CollatzResearch.WordTrace tailWord_908215 prefixEnd_908215 414534073442906078520623 := by
  unfold tailWord_908215
  simp only [CollatzResearch.WordTrace]
  refine ⟨33125322404699640618110099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22083548269799760412073399 33125322404699640618110099)
  ·
    refine ⟨49687983607049460927165149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33125322404699640618110099 49687983607049460927165149)
    ·
      refine ⟨18632993852643547847686931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49687983607049460927165149 18632993852643547847686931)
      ·
        refine ⟨27949490778965321771530397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18632993852643547847686931 27949490778965321771530397)
        ·
          refine ⟨10481059042111995664323899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27949490778965321771530397 10481059042111995664323899)
          ·
            refine ⟨15721588563167993496485849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10481059042111995664323899 15721588563167993496485849)
            ·
              refine ⟨11791191422375995122364387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15721588563167993496485849 11791191422375995122364387)
              ·
                refine ⟨17686787133563992683546581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11791191422375995122364387 17686787133563992683546581)
                ·
                  refine ⟨414534073442906078520623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17686787133563992683546581 414534073442906078520623)
                  ·
                    rfl

theorem cell20_908215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 1, 7].length) (baseStart_908215 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_908215 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_908215 prefixEnd_908215 := by exact prefixLift 908215
  have htrace : WordTrace (prefixWord ++ tailWord_908215) baseStart_908215 baseEnd_908215 := by
    simpa [prefixWord, tailWord_908215, baseEnd_908215] using wordTrace_append hprefix tailTrace_908215
  have hstable : (prefixWord ++ tailWord_908215).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908215).length < 2 ^ (prefixWord ++ tailWord_908215).sum := by decide
  have hdescent : baseEnd_908215 < baseStart_908215 := by decide
  rcases family_descends (prefixWord ++ tailWord_908215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908218 : List Nat := [3, 1, 1, 1, 2, 1, 4, 5, 2]
def baseStart_908218 : Nat := 118140960795 + 908218 * 2 ^ 59
def prefixEnd_908218 : Nat := 4983230072969 + 3 ^ 40 * 908218 * 2
def baseEnd_908218 : Nat := 414535442724651401420611

theorem tailTrace_908218 : CollatzResearch.WordTrace tailWord_908218 prefixEnd_908218 414535442724651401420611 := by
  unfold tailWord_908218
  simp only [CollatzResearch.WordTrace]
  refine ⟨8281357955922193032617327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22083621215792514753646205 8281357955922193032617327)
  ·
    refine ⟨12422036933883289548925991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8281357955922193032617327 12422036933883289548925991)
    ·
      refine ⟨18633055400824934323388987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12422036933883289548925991 18633055400824934323388987)
      ·
        refine ⟨27949583101237401485083481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18633055400824934323388987 27949583101237401485083481)
        ·
          refine ⟨20962187325928051113812611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27949583101237401485083481 20962187325928051113812611)
          ·
            refine ⟨31443280988892076670718917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20962187325928051113812611 31443280988892076670718917)
            ·
              refine ⟨5895615185417264375759797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31443280988892076670718917 5895615185417264375759797)
              ·
                refine ⟨552713923632868535227481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5895615185417264375759797 552713923632868535227481)
                ·
                  refine ⟨414535442724651401420611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 552713923632868535227481 414535442724651401420611)
                  ·
                    rfl

theorem cell20_908218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 5, 2].length) (baseStart_908218 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_908218 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_908218 prefixEnd_908218 := by exact prefixLift 908218
  have htrace : WordTrace (prefixWord ++ tailWord_908218) baseStart_908218 baseEnd_908218 := by
    simpa [prefixWord, tailWord_908218, baseEnd_908218] using wordTrace_append hprefix tailTrace_908218
  have hstable : (prefixWord ++ tailWord_908218).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908218).length < 2 ^ (prefixWord ++ tailWord_908218).sum := by decide
  have hdescent : baseEnd_908218 < baseStart_908218 := by decide
  rcases family_descends (prefixWord ++ tailWord_908218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908235 : List Nat := [1, 1, 1, 1, 3, 5, 4, 2, 2]
def baseStart_908235 : Nat := 118140960795 + 908235 * 2 ^ 59
def prefixEnd_908235 : Nat := 4983230072969 + 3 ^ 40 * 908235 * 2
def baseEnd_908235 : Nat := 414543201987874897853875

theorem tailTrace_908235 : CollatzResearch.WordTrace tailWord_908235 prefixEnd_908235 414543201987874897853875 := by
  unfold tailWord_908235
  simp only [CollatzResearch.WordTrace]
  refine ⟨33126051864627184033838159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22084034576418122689225439 33126051864627184033838159)
  ·
    refine ⟨49689077796940776050757239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33126051864627184033838159 49689077796940776050757239)
    ·
      refine ⟨74533616695411164076135859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49689077796940776050757239 74533616695411164076135859)
      ·
        refine ⟨111800425043116746114203789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74533616695411164076135859 111800425043116746114203789)
        ·
          refine ⟨41925159391168779792826421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111800425043116746114203789 41925159391168779792826421)
          ·
            refine ⟨3930483692922073105577477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41925159391168779792826421 3930483692922073105577477)
            ·
              refine ⟨736965692422888707295777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3930483692922073105577477 736965692422888707295777)
              ·
                refine ⟨552724269317166530471833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 736965692422888707295777 552724269317166530471833)
                ·
                  refine ⟨414543201987874897853875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 552724269317166530471833 414543201987874897853875)
                  ·
                    rfl

theorem cell20_908235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 4, 2, 2].length) (baseStart_908235 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_908235 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_908235 prefixEnd_908235 := by exact prefixLift 908235
  have htrace : WordTrace (prefixWord ++ tailWord_908235) baseStart_908235 baseEnd_908235 := by
    simpa [prefixWord, tailWord_908235, baseEnd_908235] using wordTrace_append hprefix tailTrace_908235
  have hstable : (prefixWord ++ tailWord_908235).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908235).length < 2 ^ (prefixWord ++ tailWord_908235).sum := by decide
  have hdescent : baseEnd_908235 < baseStart_908235 := by decide
  rcases family_descends (prefixWord ++ tailWord_908235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908242 : List Nat := [3, 2, 2, 3, 1, 3, 1, 5]
def baseStart_908242 : Nat := 118140960795 + 908242 * 2 ^ 59
def prefixEnd_908242 : Nat := 4983230072969 + 3 ^ 40 * 908242 * 2
def baseEnd_908242 : Nat := 138182132326204661540171

theorem tailTrace_908242 : CollatzResearch.WordTrace tailWord_908242 prefixEnd_908242 138182132326204661540171 := by
  unfold tailWord_908242
  simp only [CollatzResearch.WordTrace]
  refine ⟨8281576793900456057335745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22084204783734549486228653 8281576793900456057335745)
  ·
    refine ⟨6211182595425342043001809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8281576793900456057335745 6211182595425342043001809)
    ·
      refine ⟨4658386946569006532251357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6211182595425342043001809 4658386946569006532251357)
      ·
        refine ⟨1746895104963377449594259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4658386946569006532251357 1746895104963377449594259)
        ·
          refine ⟨2620342657445066174391389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1746895104963377449594259 2620342657445066174391389)
          ·
            refine ⟨982628496541899815396771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2620342657445066174391389 982628496541899815396771)
            ·
              refine ⟨1473942744812849723095157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 982628496541899815396771 1473942744812849723095157)
              ·
                refine ⟨138182132326204661540171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1473942744812849723095157 138182132326204661540171)
                ·
                  rfl

theorem cell20_908242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 1, 5].length) (baseStart_908242 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_908242 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_908242 prefixEnd_908242 := by exact prefixLift 908242
  have htrace : WordTrace (prefixWord ++ tailWord_908242) baseStart_908242 baseEnd_908242 := by
    simpa [prefixWord, tailWord_908242, baseEnd_908242] using wordTrace_append hprefix tailTrace_908242
  have hstable : (prefixWord ++ tailWord_908242).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908242).length < 2 ^ (prefixWord ++ tailWord_908242).sum := by decide
  have hdescent : baseEnd_908242 < baseStart_908242 := by decide
  rcases family_descends (prefixWord ++ tailWord_908242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908273 : List Nat := [1, 2, 2, 2, 4, 2, 2, 3, 2]
def baseStart_908273 : Nat := 118140960795 + 908273 * 2 ^ 59
def prefixEnd_908273 : Nat := 4983230072969 + 3 ^ 40 * 908273 * 2
def baseEnd_908273 : Nat := 414560546223315654587053

theorem tailTrace_908273 : CollatzResearch.WordTrace tailWord_908273 prefixEnd_908273 414560546223315654587053 := by
  unfold tailWord_908273
  simp only [CollatzResearch.WordTrace]
  refine ⟨33127437838489516523721473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22084958558993011015814315 33127437838489516523721473)
  ·
    refine ⟨24845578378867137392791105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33127437838489516523721473 24845578378867137392791105)
    ·
      refine ⟨18634183784150353044593329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24845578378867137392791105 18634183784150353044593329)
      ·
        refine ⟨13975637838112764783444997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18634183784150353044593329 13975637838112764783444997)
        ·
          refine ⟨2620432094646143396895937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13975637838112764783444997 2620432094646143396895937)
          ·
            refine ⟨1965324070984607547671953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2620432094646143396895937 1965324070984607547671953)
            ·
              refine ⟨1473993053238455660753965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1965324070984607547671953 1473993053238455660753965)
              ·
                refine ⟨552747394964420872782737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1473993053238455660753965 552747394964420872782737)
                ·
                  refine ⟨414560546223315654587053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 552747394964420872782737 414560546223315654587053)
                  ·
                    rfl

theorem cell20_908273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 2, 3, 2].length) (baseStart_908273 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_908273 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_908273 prefixEnd_908273 := by exact prefixLift 908273
  have htrace : WordTrace (prefixWord ++ tailWord_908273) baseStart_908273 baseEnd_908273 := by
    simpa [prefixWord, tailWord_908273, baseEnd_908273] using wordTrace_append hprefix tailTrace_908273
  have hstable : (prefixWord ++ tailWord_908273).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908273).length < 2 ^ (prefixWord ++ tailWord_908273).sum := by decide
  have hdescent : baseEnd_908273 < baseStart_908273 := by decide
  rcases family_descends (prefixWord ++ tailWord_908273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908276 : List Nat := [2, 6, 2, 1, 1, 1, 7]
def baseStart_908276 : Nat := 118140960795 + 908276 * 2 ^ 59
def prefixEnd_908276 : Nat := 4983230072969 + 3 ^ 40 * 908276 * 2
def baseEnd_908276 : Nat := 46062435056117886387449

theorem tailTrace_908276 : CollatzResearch.WordTrace tailWord_908276 prefixEnd_908276 46062435056117886387449 := by
  unfold tailWord_908276
  simp only [CollatzResearch.WordTrace]
  refine ⟨16563773628739324018040341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22085031504985765357387121 16563773628739324018040341)
  ·
    refine ⟨776426888847155813345641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 16563773628739324018040341 776426888847155813345641)
    ·
      refine ⟨582320166635366860009231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 776426888847155813345641 582320166635366860009231)
      ·
        refine ⟨873480249953050290013847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 582320166635366860009231 873480249953050290013847)
        ·
          refine ⟨1310220374929575435020771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 873480249953050290013847 1310220374929575435020771)
          ·
            refine ⟨1965330562394363152531157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1310220374929575435020771 1965330562394363152531157)
            ·
              refine ⟨46062435056117886387449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1965330562394363152531157 46062435056117886387449)
              ·
                rfl

theorem cell20_908276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 7].length) (baseStart_908276 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_908276 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_908276 prefixEnd_908276 := by exact prefixLift 908276
  have htrace : WordTrace (prefixWord ++ tailWord_908276) baseStart_908276 baseEnd_908276 := by
    simpa [prefixWord, tailWord_908276, baseEnd_908276] using wordTrace_append hprefix tailTrace_908276
  have hstable : (prefixWord ++ tailWord_908276).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908276).length < 2 ^ (prefixWord ++ tailWord_908276).sum := by decide
  have hdescent : baseEnd_908276 < baseStart_908276 := by decide
  rcases family_descends (prefixWord ++ tailWord_908276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908284 : List Nat := [2, 2, 2, 1, 2, 4, 7]
def baseStart_908284 : Nat := 118140960795 + 908284 * 2 ^ 59
def prefixEnd_908284 : Nat := 4983230072969 + 3 ^ 40 * 908284 * 2
def baseEnd_908284 : Nat := 46062840769227611691149

theorem tailTrace_908284 : CollatzResearch.WordTrace tailWord_908284 prefixEnd_908284 46062840769227611691149 := by
  unfold tailWord_908284
  simp only [CollatzResearch.WordTrace]
  refine ⟨16563919520724832701185953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22085226027633110268247937 16563919520724832701185953)
  ·
    refine ⟨12422939640543624525889465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16563919520724832701185953 12422939640543624525889465)
    ·
      refine ⟨9317204730407718394417099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12422939640543624525889465 9317204730407718394417099)
      ·
        refine ⟨13975807095611577591625649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9317204730407718394417099 13975807095611577591625649)
        ·
          refine ⟨10481855321708683193719237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13975807095611577591625649 10481855321708683193719237)
          ·
            refine ⟨1965347872820378098822357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10481855321708683193719237 1965347872820378098822357)
            ·
              refine ⟨46062840769227611691149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1965347872820378098822357 46062840769227611691149)
              ·
                rfl

theorem cell20_908284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 7].length) (baseStart_908284 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_908284 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_908284 prefixEnd_908284 := by exact prefixLift 908284
  have htrace : WordTrace (prefixWord ++ tailWord_908284) baseStart_908284 baseEnd_908284 := by
    simpa [prefixWord, tailWord_908284, baseEnd_908284] using wordTrace_append hprefix tailTrace_908284
  have hstable : (prefixWord ++ tailWord_908284).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908284).length < 2 ^ (prefixWord ++ tailWord_908284).sum := by decide
  have hdescent : baseEnd_908284 < baseStart_908284 := by decide
  rcases family_descends (prefixWord ++ tailWord_908284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908290 : List Nat := [3, 4, 1, 3, 1, 1, 2, 1, 4]
def baseStart_908290 : Nat := 118140960795 + 908290 * 2 ^ 59
def prefixEnd_908290 : Nat := 4983230072969 + 3 ^ 40 * 908290 * 2
def baseEnd_908290 : Nat := 414568305486539151020317

theorem tailTrace_908290 : CollatzResearch.WordTrace tailWord_908290 prefixEnd_908290 414568305486539151020317 := by
  unfold tailWord_908290
  simp only [CollatzResearch.WordTrace]
  refine ⟨8282014469856982106772581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22085371919618618951393549 8282014469856982106772581)
  ·
    refine ⟨1552877713098184145019859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8282014469856982106772581 1552877713098184145019859)
    ·
      refine ⟨2329316569647276217529789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1552877713098184145019859 2329316569647276217529789)
      ·
        refine ⟨873493713617728581573671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2329316569647276217529789 873493713617728581573671)
        ·
          refine ⟨1310240570426592872360507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 873493713617728581573671 1310240570426592872360507)
          ·
            refine ⟨1965360855639889308540761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1310240570426592872360507 1965360855639889308540761)
            ·
              refine ⟨1474020641729916981405571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1965360855639889308540761 1474020641729916981405571)
              ·
                refine ⟨2211030962594875472108357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1474020641729916981405571 2211030962594875472108357)
                ·
                  refine ⟨414568305486539151020317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2211030962594875472108357 414568305486539151020317)
                  ·
                    rfl

theorem cell20_908290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_908290 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_908290 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_908290 prefixEnd_908290 := by exact prefixLift 908290
  have htrace : WordTrace (prefixWord ++ tailWord_908290) baseStart_908290 baseEnd_908290 := by
    simpa [prefixWord, tailWord_908290, baseEnd_908290] using wordTrace_append hprefix tailTrace_908290
  have hstable : (prefixWord ++ tailWord_908290).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908290).length < 2 ^ (prefixWord ++ tailWord_908290).sum := by decide
  have hdescent : baseEnd_908290 < baseStart_908290 := by decide
  rcases family_descends (prefixWord ++ tailWord_908290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908360 : List Nat := [2, 1, 3, 1, 1, 1, 6, 5]
def baseStart_908360 : Nat := 118140960795 + 908360 * 2 ^ 59
def prefixEnd_908360 : Nat := 4983230072969 + 3 ^ 40 * 908360 * 2
def baseEnd_908360 : Nat := 138200085131310006228899

theorem tailTrace_908360 : CollatzResearch.WordTrace tailWord_908360 prefixEnd_908360 138200085131310006228899 := by
  unfold tailWord_908360
  simp only [CollatzResearch.WordTrace]
  refine ⟨16565305494587165191069267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22087073992782886921425689 16565305494587165191069267)
  ·
    refine ⟨24847958241880747786603901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16565305494587165191069267 24847958241880747786603901)
    ·
      refine ⟨9317984340705280419976463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24847958241880747786603901 9317984340705280419976463)
      ·
        refine ⟨13976976511057920629964695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9317984340705280419976463 13976976511057920629964695)
        ·
          refine ⟨20965464766586880944947043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13976976511057920629964695 20965464766586880944947043)
          ·
            refine ⟨31448197149880321417420565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20965464766586880944947043 31448197149880321417420565)
            ·
              refine ⟨1474134241400640066441589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 31448197149880321417420565 1474134241400640066441589)
              ·
                refine ⟨138200085131310006228899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1474134241400640066441589 138200085131310006228899)
                ·
                  rfl

theorem cell20_908360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 6, 5].length) (baseStart_908360 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_908360 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_908360 prefixEnd_908360 := by exact prefixLift 908360
  have htrace : WordTrace (prefixWord ++ tailWord_908360) baseStart_908360 baseEnd_908360 := by
    simpa [prefixWord, tailWord_908360, baseEnd_908360] using wordTrace_append hprefix tailTrace_908360
  have hstable : (prefixWord ++ tailWord_908360).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908360).length < 2 ^ (prefixWord ++ tailWord_908360).sum := by decide
  have hdescent : baseEnd_908360 < baseStart_908360 := by decide
  rcases family_descends (prefixWord ++ tailWord_908360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908398 : List Nat := [4, 1, 2, 2, 1, 10]
def baseStart_908398 : Nat := 118140960795 + 908398 * 2 ^ 59
def prefixEnd_908398 : Nat := 4983230072969 + 3 ^ 40 * 908398 * 2
def baseEnd_908398 : Nat := 15356207393680399089625

theorem tailTrace_908398 : CollatzResearch.WordTrace tailWord_908398 prefixEnd_908398 15356207393680399089625 := by
  unfold tailWord_908398
  simp only [CollatzResearch.WordTrace]
  refine ⟨4141499620379582859002731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22087997975357775248014565 4141499620379582859002731)
  ·
    refine ⟨6212249430569374288504097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4141499620379582859002731 6212249430569374288504097)
    ·
      refine ⟨4659187072927030716378073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6212249430569374288504097 4659187072927030716378073)
      ·
        refine ⟨3494390304695273037283555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4659187072927030716378073 3494390304695273037283555)
        ·
          refine ⟨5241585457042909555925333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3494390304695273037283555 5241585457042909555925333)
          ·
            refine ⟨15356207393680399089625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5241585457042909555925333 15356207393680399089625)
            ·
              rfl

theorem cell20_908398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 10].length) (baseStart_908398 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_908398 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_908398 prefixEnd_908398 := by exact prefixLift 908398
  have htrace : WordTrace (prefixWord ++ tailWord_908398) baseStart_908398 baseEnd_908398 := by
    simpa [prefixWord, tailWord_908398, baseEnd_908398] using wordTrace_append hprefix tailTrace_908398
  have hstable : (prefixWord ++ tailWord_908398).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908398).length < 2 ^ (prefixWord ++ tailWord_908398).sum := by decide
  have hdescent : baseEnd_908398 < baseStart_908398 := by decide
  rcases family_descends (prefixWord ++ tailWord_908398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908501 : List Nat := [1, 3, 2, 4, 1, 1, 3, 3, 2]
def baseStart_908501 : Nat := 118140960795 + 908501 * 2 ^ 59
def prefixEnd_908501 : Nat := 4983230072969 + 3 ^ 40 * 908501 * 2
def baseEnd_908501 : Nat := 414664611635960194986121

theorem tailTrace_908501 : CollatzResearch.WordTrace tailWord_908501 prefixEnd_908501 414664611635960194986121 := by
  unfold tailWord_908501
  simp only [CollatzResearch.WordTrace]
  refine ⟨33135753681663511463021357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22090502454442340975347571 33135753681663511463021357)
  ·
    refine ⟨12425907630623816798633009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33135753681663511463021357 12425907630623816798633009)
    ·
      refine ⟨9319430722967862598974757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12425907630623816798633009 9319430722967862598974757)
      ·
        refine ⟨1747393260556474237307767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9319430722967862598974757 1747393260556474237307767)
        ·
          refine ⟨2621089890834711355961651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1747393260556474237307767 2621089890834711355961651)
          ·
            refine ⟨3931634836252067033942477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2621089890834711355961651 3931634836252067033942477)
            ·
              refine ⟨1474363063594525137728429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3931634836252067033942477 1474363063594525137728429)
              ·
                refine ⟨552886148847946926648161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1474363063594525137728429 552886148847946926648161)
                ·
                  refine ⟨414664611635960194986121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 552886148847946926648161 414664611635960194986121)
                  ·
                    rfl

theorem cell20_908501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 3, 3, 2].length) (baseStart_908501 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_908501 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_908501 prefixEnd_908501 := by exact prefixLift 908501
  have htrace : WordTrace (prefixWord ++ tailWord_908501) baseStart_908501 baseEnd_908501 := by
    simpa [prefixWord, tailWord_908501, baseEnd_908501] using wordTrace_append hprefix tailTrace_908501
  have hstable : (prefixWord ++ tailWord_908501).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908501).length < 2 ^ (prefixWord ++ tailWord_908501).sum := by decide
  have hdescent : baseEnd_908501 < baseStart_908501 := by decide
  rcases family_descends (prefixWord ++ tailWord_908501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908512 : List Nat := [2, 1, 1, 3, 1, 6, 6]
def baseStart_908512 : Nat := 118140960795 + 908512 * 2 ^ 59
def prefixEnd_908512 : Nat := 4983230072969 + 3 ^ 40 * 908512 * 2
def baseEnd_908512 : Nat := 46074403592854782846601

theorem tailTrace_908512 : CollatzResearch.WordTrace tailWord_908512 prefixEnd_908512 46074403592854782846601 := by
  unfold tailWord_908512
  simp only [CollatzResearch.WordTrace]
  refine ⟨16568077442311830170835895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22090769923082440227781193 16568077442311830170835895)
  ·
    refine ⟨24852116163467745256253843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16568077442311830170835895 24852116163467745256253843)
    ·
      refine ⟨37278174245201617884380765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24852116163467745256253843 37278174245201617884380765)
      ·
        refine ⟨13979315341950606706642787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37278174245201617884380765 13979315341950606706642787)
        ·
          refine ⟨20968973012925910059964181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13979315341950606706642787 20968973012925910059964181)
          ·
            refine ⟨982920609980902034060821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 20968973012925910059964181 982920609980902034060821)
            ·
              refine ⟨46074403592854782846601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 982920609980902034060821 46074403592854782846601)
              ·
                rfl

theorem cell20_908512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 6].length) (baseStart_908512 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_908512 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_908512 prefixEnd_908512 := by exact prefixLift 908512
  have htrace : WordTrace (prefixWord ++ tailWord_908512) baseStart_908512 baseEnd_908512 := by
    simpa [prefixWord, tailWord_908512, baseEnd_908512] using wordTrace_append hprefix tailTrace_908512
  have hstable : (prefixWord ++ tailWord_908512).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908512).length < 2 ^ (prefixWord ++ tailWord_908512).sum := by decide
  have hdescent : baseEnd_908512 < baseStart_908512 := by decide
  rcases family_descends (prefixWord ++ tailWord_908512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908522 : List Nat := [3, 1, 3, 1, 1, 5, 1, 1, 4]
def baseStart_908522 : Nat := 118140960795 + 908522 * 2 ^ 59
def prefixEnd_908522 : Nat := 4983230072969 + 3 ^ 40 * 908522 * 2
def baseEnd_908522 : Nat := 414674196608177455286035

theorem tailTrace_908522 : CollatzResearch.WordTrace tailWord_908522 prefixEnd_908522 414674196608177455286035 := by
  unfold tailWord_908522
  simp only [CollatzResearch.WordTrace]
  refine ⟨8284129903646858012383955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22091013076391621366357213 8284129903646858012383955)
  ·
    refine ⟨12426194855470287018575933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8284129903646858012383955 12426194855470287018575933)
    ·
      refine ⟨4659823070801357631965975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12426194855470287018575933 4659823070801357631965975)
      ·
        refine ⟨6989734606202036447948963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4659823070801357631965975 6989734606202036447948963)
        ·
          refine ⟨10484601909303054671923445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6989734606202036447948963 10484601909303054671923445)
          ·
            refine ⟨982931428997161375492823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10484601909303054671923445 982931428997161375492823)
            ·
              refine ⟨1474397143495742063239235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 982931428997161375492823 1474397143495742063239235)
              ·
                refine ⟨2211595715243613094858853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1474397143495742063239235 2211595715243613094858853)
                ·
                  refine ⟨414674196608177455286035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2211595715243613094858853 414674196608177455286035)
                  ·
                    rfl

theorem cell20_908522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 1, 1, 4].length) (baseStart_908522 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_908522 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_908522 prefixEnd_908522 := by exact prefixLift 908522
  have htrace : WordTrace (prefixWord ++ tailWord_908522) baseStart_908522 baseEnd_908522 := by
    simpa [prefixWord, tailWord_908522, baseEnd_908522] using wordTrace_append hprefix tailTrace_908522
  have hstable : (prefixWord ++ tailWord_908522).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908522).length < 2 ^ (prefixWord ++ tailWord_908522).sum := by decide
  have hdescent : baseEnd_908522 < baseStart_908522 := by decide
  rcases family_descends (prefixWord ++ tailWord_908522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908629 : List Nat := [1, 3, 2, 2, 3, 3, 1, 2, 3]
def baseStart_908629 : Nat := 118140960795 + 908629 * 2 ^ 59
def prefixEnd_908629 : Nat := 4983230072969 + 3 ^ 40 * 908629 * 2
def baseEnd_908629 : Nat := 414723034323760638718931

theorem tailTrace_908629 : CollatzResearch.WordTrace tailWord_908629 prefixEnd_908629 414723034323760638718931 := by
  unfold tailWord_908629
  simp only [CollatzResearch.WordTrace]
  refine ⟨33140422225199789323680941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22093614816799859549120627 33140422225199789323680941)
  ·
    refine ⟨12427658334449920996380353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33140422225199789323680941 12427658334449920996380353)
    ·
      refine ⟨9320743750837440747285265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12427658334449920996380353 9320743750837440747285265)
      ·
        refine ⟨6990557813128080560463949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9320743750837440747285265 6990557813128080560463949)
        ·
          refine ⟨2621459179923030210173981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6990557813128080560463949 2621459179923030210173981)
          ·
            refine ⟨983047192471136328815243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2621459179923030210173981 983047192471136328815243)
            ·
              refine ⟨1474570788706704493222865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 983047192471136328815243 1474570788706704493222865)
              ·
                refine ⟨1105928091530028369917149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1474570788706704493222865 1105928091530028369917149)
                ·
                  refine ⟨414723034323760638718931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1105928091530028369917149 414723034323760638718931)
                  ·
                    rfl

theorem cell20_908629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 1, 2, 3].length) (baseStart_908629 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_908629 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_908629 prefixEnd_908629 := by exact prefixLift 908629
  have htrace : WordTrace (prefixWord ++ tailWord_908629) baseStart_908629 baseEnd_908629 := by
    simpa [prefixWord, tailWord_908629, baseEnd_908629] using wordTrace_append hprefix tailTrace_908629
  have hstable : (prefixWord ++ tailWord_908629).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908629).length < 2 ^ (prefixWord ++ tailWord_908629).sum := by decide
  have hdescent : baseEnd_908629 < baseStart_908629 := by decide
  rcases family_descends (prefixWord ++ tailWord_908629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908681 : List Nat := [1, 2, 1, 1, 8, 1, 6]
def baseStart_908681 : Nat := 118140960795 + 908681 * 2 ^ 59
def prefixEnd_908681 : Nat := 4983230072969 + 3 ^ 40 * 908681 * 2
def baseEnd_908681 : Nat := 46082974282297729887265

theorem tailTrace_908681 : CollatzResearch.WordTrace tailWord_908681 prefixEnd_908681 46082974282297729887265 := by
  unfold tailWord_908681
  simp only [CollatzResearch.WordTrace]
  refine ⟨33142318821011402204573897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22094879214007601469715931 33142318821011402204573897)
  ·
    refine ⟨24856739115758551653430423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33142318821011402204573897 24856739115758551653430423)
    ·
      refine ⟨37285108673637827480145635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24856739115758551653430423 37285108673637827480145635)
      ·
        refine ⟨55927663010456741220218453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37285108673637827480145635 55927663010456741220218453)
        ·
          refine ⟨655402300903789936174435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 55927663010456741220218453 655402300903789936174435)
          ·
            refine ⟨983103451355684904261653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 655402300903789936174435 983103451355684904261653)
            ·
              refine ⟨46082974282297729887265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 983103451355684904261653 46082974282297729887265)
              ·
                rfl

theorem cell20_908681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 6].length) (baseStart_908681 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_908681 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_908681 prefixEnd_908681 := by exact prefixLift 908681
  have htrace : WordTrace (prefixWord ++ tailWord_908681) baseStart_908681 baseEnd_908681 := by
    simpa [prefixWord, tailWord_908681, baseEnd_908681] using wordTrace_append hprefix tailTrace_908681
  have hstable : (prefixWord ++ tailWord_908681).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908681).length < 2 ^ (prefixWord ++ tailWord_908681).sum := by decide
  have hdescent : baseEnd_908681 < baseStart_908681 := by decide
  rcases family_descends (prefixWord ++ tailWord_908681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908716 : List Nat := [2, 2, 1, 1, 1, 1, 4, 4, 4]
def baseStart_908716 : Nat := 118140960795 + 908716 * 2 ^ 59
def prefixEnd_908716 : Nat := 4983230072969 + 3 ^ 40 * 908716 * 2
def baseEnd_908716 : Nat := 414762743494375002818575

theorem tailTrace_908716 : CollatzResearch.WordTrace tailWord_908716 prefixEnd_908716 414762743494375002818575 := by
  unfold tailWord_908716
  simp only [CollatzResearch.WordTrace]
  refine ⟨16571797687942301591049001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22095730250589735454732001 16571797687942301591049001)
  ·
    refine ⟨12428848265956726193286751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16571797687942301591049001 12428848265956726193286751)
    ·
      refine ⟨18643272398935089289930127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12428848265956726193286751 18643272398935089289930127)
      ·
        refine ⟨27964908598402633934895191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18643272398935089289930127 27964908598402633934895191)
        ·
          refine ⟨41947362897603950902342787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27964908598402633934895191 41947362897603950902342787)
          ·
            refine ⟨62921044346405926353514181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41947362897603950902342787 62921044346405926353514181)
            ·
              refine ⟨11797695814951111191283909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62921044346405926353514181 11797695814951111191283909)
              ·
                refine ⟨2212067965303333348365733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11797695814951111191283909 2212067965303333348365733)
                ·
                  refine ⟨414762743494375002818575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2212067965303333348365733 414762743494375002818575)
                  ·
                    rfl

theorem cell20_908716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 4].length) (baseStart_908716 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_908716 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_908716 prefixEnd_908716 := by exact prefixLift 908716
  have htrace : WordTrace (prefixWord ++ tailWord_908716) baseStart_908716 baseEnd_908716 := by
    simpa [prefixWord, tailWord_908716, baseEnd_908716] using wordTrace_append hprefix tailTrace_908716
  have hstable : (prefixWord ++ tailWord_908716).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908716).length < 2 ^ (prefixWord ++ tailWord_908716).sum := by decide
  have hdescent : baseEnd_908716 < baseStart_908716 := by decide
  rcases family_descends (prefixWord ++ tailWord_908716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908738 : List Nat := [3, 5, 2, 1, 2, 1, 2, 2, 2]
def baseStart_908738 : Nat := 118140960795 + 908738 * 2 ^ 59
def prefixEnd_908738 : Nat := 4983230072969 + 3 ^ 40 * 908738 * 2
def baseEnd_908738 : Nat := 414772784893840704085153

theorem tailTrace_908738 : CollatzResearch.WordTrace tailWord_908738 prefixEnd_908738 414772784893840704085153 := by
  unfold tailWord_908738
  simp only [CollatzResearch.WordTrace]
  refine ⟨8286099445451225234849717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22096265187869933959599245 8286099445451225234849717)
  ·
    refine ⟨776821823011052365767161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8286099445451225234849717 776821823011052365767161)
    ·
      refine ⟨582616367258289274325371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 776821823011052365767161 582616367258289274325371)
      ·
        refine ⟨873924550887433911488057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 582616367258289274325371 873924550887433911488057)
        ·
          refine ⟨655443413165575433616043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 873924550887433911488057 655443413165575433616043)
          ·
            refine ⟨983165119748363150424065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 655443413165575433616043 983165119748363150424065)
            ·
              refine ⟨737373839811272362818049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 983165119748363150424065 737373839811272362818049)
              ·
                refine ⟨553030379858454272113537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 737373839811272362818049 553030379858454272113537)
                ·
                  refine ⟨414772784893840704085153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 553030379858454272113537 414772784893840704085153)
                  ·
                    rfl

theorem cell20_908738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_908738 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_908738 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_908738 prefixEnd_908738 := by exact prefixLift 908738
  have htrace : WordTrace (prefixWord ++ tailWord_908738) baseStart_908738 baseEnd_908738 := by
    simpa [prefixWord, tailWord_908738, baseEnd_908738] using wordTrace_append hprefix tailTrace_908738
  have hstable : (prefixWord ++ tailWord_908738).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908738).length < 2 ^ (prefixWord ++ tailWord_908738).sum := by decide
  have hdescent : baseEnd_908738 < baseStart_908738 := by decide
  rcases family_descends (prefixWord ++ tailWord_908738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908740 : List Nat := [2, 3, 3, 2, 1, 9]
def baseStart_908740 : Nat := 118140960795 + 908740 * 2 ^ 59
def prefixEnd_908740 : Nat := 4983230072969 + 3 ^ 40 * 908740 * 2
def baseEnd_908740 : Nat := 15361988805493984667351

theorem tailTrace_908740 : CollatzResearch.WordTrace tailWord_908740 prefixEnd_908740 15361988805493984667351 := by
  unfold tailWord_908740
  simp only [CollatzResearch.WordTrace]
  refine ⟨16572235363898827640485837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22096313818531770187314449 16572235363898827640485837)
  ·
    refine ⟨6214588261462060365182189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16572235363898827640485837 6214588261462060365182189)
    ·
      refine ⟨2330470598048272636943321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6214588261462060365182189 2330470598048272636943321)
      ·
        refine ⟨1747852948536204477707491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2330470598048272636943321 1747852948536204477707491)
        ·
          refine ⟨2621779422804306716561237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1747852948536204477707491 2621779422804306716561237)
          ·
            refine ⟨15361988805493984667351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2621779422804306716561237 15361988805493984667351)
            ·
              rfl

theorem cell20_908740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 9].length) (baseStart_908740 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_908740 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_908740 prefixEnd_908740 := by exact prefixLift 908740
  have htrace : WordTrace (prefixWord ++ tailWord_908740) baseStart_908740 baseEnd_908740 := by
    simpa [prefixWord, tailWord_908740, baseEnd_908740] using wordTrace_append hprefix tailTrace_908740
  have hstable : (prefixWord ++ tailWord_908740).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908740).length < 2 ^ (prefixWord ++ tailWord_908740).sum := by decide
  have hdescent : baseEnd_908740 < baseStart_908740 := by decide
  rcases family_descends (prefixWord ++ tailWord_908740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908747 : List Nat := [1, 1, 1, 1, 3, 3, 3, 4, 3]
def baseStart_908747 : Nat := 118140960795 + 908747 * 2 ^ 59
def prefixEnd_908747 : Nat := 4983230072969 + 3 ^ 40 * 908747 * 2
def baseEnd_908747 : Nat := 414776892739076672785115

theorem tailTrace_908747 : CollatzResearch.WordTrace tailWord_908747 prefixEnd_908747 414776892739076672785115 := by
  unfold tailWord_908747
  simp only [CollatzResearch.WordTrace]
  refine ⟨33144726038772295476476495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22096484025848196984317663 33144726038772295476476495)
  ·
    refine ⟨49717089058158443214714743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33144726038772295476476495 49717089058158443214714743)
    ·
      refine ⟨74575633587237664822072115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49717089058158443214714743 74575633587237664822072115)
      ·
        refine ⟨111863450380856497233108173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74575633587237664822072115 111863450380856497233108173)
        ·
          refine ⟨41948793892821186462415565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 111863450380856497233108173 41948793892821186462415565)
          ·
            refine ⟨15730797709807944923405837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41948793892821186462415565 15730797709807944923405837)
            ·
              refine ⟨5899049141177979346277189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15730797709807944923405837 5899049141177979346277189)
              ·
                refine ⟨1106071713970871127426973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5899049141177979346277189 1106071713970871127426973)
                ·
                  refine ⟨414776892739076672785115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1106071713970871127426973 414776892739076672785115)
                  ·
                    rfl

theorem cell20_908747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 4, 3].length) (baseStart_908747 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_908747 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_908747 prefixEnd_908747 := by exact prefixLift 908747
  have htrace : WordTrace (prefixWord ++ tailWord_908747) baseStart_908747 baseEnd_908747 := by
    simpa [prefixWord, tailWord_908747, baseEnd_908747] using wordTrace_append hprefix tailTrace_908747
  have hstable : (prefixWord ++ tailWord_908747).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908747).length < 2 ^ (prefixWord ++ tailWord_908747).sum := by decide
  have hdescent : baseEnd_908747 < baseStart_908747 := by decide
  rcases family_descends (prefixWord ++ tailWord_908747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908771 : List Nat := [1, 1, 1, 6, 2, 2, 1, 2, 4]
def baseStart_908771 : Nat := 118140960795 + 908771 * 2 ^ 59
def prefixEnd_908771 : Nat := 4983230072969 + 3 ^ 40 * 908771 * 2
def baseEnd_908771 : Nat := 414787846993039255985017

theorem tailTrace_908771 : CollatzResearch.WordTrace tailWord_908771 prefixEnd_908771 414787846993039255985017 := by
  unfold tailWord_908771
  simp only [CollatzResearch.WordTrace]
  refine ⟨33145601390685347575350167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22097067593790231716900111 33145601390685347575350167)
  ·
    refine ⟨49718402086028021363025251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33145601390685347575350167 49718402086028021363025251)
    ·
      refine ⟨74577603129042032044537877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49718402086028021363025251 74577603129042032044537877)
      ·
        refine ⟨3495825146673845252087713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 74577603129042032044537877 3495825146673845252087713)
        ·
          refine ⟨2621868860005383939065785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3495825146673845252087713 2621868860005383939065785)
          ·
            refine ⟨1966401645004037954299339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2621868860005383939065785 1966401645004037954299339)
            ·
              refine ⟨2949602467506056931449009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1966401645004037954299339 2949602467506056931449009)
              ·
                refine ⟨2212201850629542698586757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2949602467506056931449009 2212201850629542698586757)
                ·
                  refine ⟨414787846993039255985017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2212201850629542698586757 414787846993039255985017)
                  ·
                    rfl

theorem cell20_908771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 2, 4].length) (baseStart_908771 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_908771 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_908771 prefixEnd_908771 := by exact prefixLift 908771
  have htrace : WordTrace (prefixWord ++ tailWord_908771) baseStart_908771 baseEnd_908771 := by
    simpa [prefixWord, tailWord_908771, baseEnd_908771] using wordTrace_append hprefix tailTrace_908771
  have hstable : (prefixWord ++ tailWord_908771).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908771).length < 2 ^ (prefixWord ++ tailWord_908771).sum := by decide
  have hdescent : baseEnd_908771 < baseStart_908771 := by decide
  rcases family_descends (prefixWord ++ tailWord_908771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908809 : List Nat := [1, 2, 1, 1, 3, 1, 3, 6, 2]
def baseStart_908809 : Nat := 118140960795 + 908809 * 2 ^ 59
def prefixEnd_908809 : Nat := 4983230072969 + 3 ^ 40 * 908809 * 2
def baseEnd_908809 : Nat := 414805191228480012718195

theorem tailTrace_908809 : CollatzResearch.WordTrace tailWord_908809 prefixEnd_908809 414805191228480012718195 := by
  unfold tailWord_908809
  simp only [CollatzResearch.WordTrace]
  refine ⟨33146987364547680065233481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22097991576365120043488987 33146987364547680065233481)
  ·
    refine ⟨24860240523410760048925111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33146987364547680065233481 24860240523410760048925111)
    ·
      refine ⟨37290360785116140073387667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24860240523410760048925111 37290360785116140073387667)
      ·
        refine ⟨55935541177674210110081501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37290360785116140073387667 55935541177674210110081501)
        ·
          refine ⟨20975827941627828791280563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55935541177674210110081501 20975827941627828791280563)
          ·
            refine ⟨31463741912441743186920845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20975827941627828791280563 31463741912441743186920845)
            ·
              refine ⟨11798903217165653695095317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31463741912441743186920845 11798903217165653695095317)
              ·
                refine ⟨553073588304640016957593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11798903217165653695095317 553073588304640016957593)
                ·
                  refine ⟨414805191228480012718195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 553073588304640016957593 414805191228480012718195)
                  ·
                    rfl

theorem cell20_908809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 6, 2].length) (baseStart_908809 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_908809 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_908809 prefixEnd_908809 := by exact prefixLift 908809
  have htrace : WordTrace (prefixWord ++ tailWord_908809) baseStart_908809 baseEnd_908809 := by
    simpa [prefixWord, tailWord_908809, baseEnd_908809] using wordTrace_append hprefix tailTrace_908809
  have hstable : (prefixWord ++ tailWord_908809).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908809).length < 2 ^ (prefixWord ++ tailWord_908809).sum := by decide
  have hdescent : baseEnd_908809 < baseStart_908809 := by decide
  rcases family_descends (prefixWord ++ tailWord_908809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908833 : List Nat := [1, 2, 3, 2, 2, 4, 2, 4]
def baseStart_908833 : Nat := 118140960795 + 908833 * 2 ^ 59
def prefixEnd_908833 : Nat := 4983230072969 + 3 ^ 40 * 908833 * 2
def baseEnd_908833 : Nat := 138272048494147531972699

theorem tailTrace_908833 : CollatzResearch.WordTrace tailWord_908833 prefixEnd_908833 138272048494147531972699 := by
  unfold tailWord_908833
  simp only [CollatzResearch.WordTrace]
  refine ⟨33147862716460732164107153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22098575144307154776071435 33147862716460732164107153)
  ·
    refine ⟨24860897037345549123080365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33147862716460732164107153 24860897037345549123080365)
    ·
      refine ⟨9322836389004580921155137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24860897037345549123080365 9322836389004580921155137)
      ·
        refine ⟨6992127291753435690866353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9322836389004580921155137 6992127291753435690866353)
        ·
          refine ⟨5244095468815076768149765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6992127291753435690866353 5244095468815076768149765)
          ·
            refine ⟨983267900402826894028081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5244095468815076768149765 983267900402826894028081)
            ·
              refine ⟨737450925302120170521061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 983267900402826894028081 737450925302120170521061)
              ·
                refine ⟨138272048494147531972699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 737450925302120170521061 138272048494147531972699)
                ·
                  rfl

theorem cell20_908833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 2, 4].length) (baseStart_908833 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_908833 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_908833 prefixEnd_908833 := by exact prefixLift 908833
  have htrace : WordTrace (prefixWord ++ tailWord_908833) baseStart_908833 baseEnd_908833 := by
    simpa [prefixWord, tailWord_908833, baseEnd_908833] using wordTrace_append hprefix tailTrace_908833
  have hstable : (prefixWord ++ tailWord_908833).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908833).length < 2 ^ (prefixWord ++ tailWord_908833).sum := by decide
  have hdescent : baseEnd_908833 < baseStart_908833 := by decide
  rcases family_descends (prefixWord ++ tailWord_908833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908870 : List Nat := [6, 1, 1, 1, 4, 1, 2, 1, 3]
def baseStart_908870 : Nat := 118140960795 + 908870 * 2 ^ 59
def prefixEnd_908870 : Nat := 4983230072969 + 3 ^ 40 * 908870 * 2
def baseEnd_908870 : Nat := 414833033290634911684613

theorem tailTrace_908870 : CollatzResearch.WordTrace tailWord_908870 prefixEnd_908870 414833033290634911684613 := by
  unfold tailWord_908870
  simp only [CollatzResearch.WordTrace]
  refine ⟨1035912881791458983850127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 22099474811551124988802709 1035912881791458983850127)
  ·
    refine ⟨1553869322687188475775191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1035912881791458983850127 1553869322687188475775191)
    ·
      refine ⟨2330803984030782713662787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1553869322687188475775191 2330803984030782713662787)
      ·
        refine ⟨3496205976046174070494181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2330803984030782713662787 3496205976046174070494181)
        ·
          refine ⟨655538620508657638217659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3496205976046174070494181 655538620508657638217659)
          ·
            refine ⟨983307930762986457326489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 655538620508657638217659 983307930762986457326489)
            ·
              refine ⟨737480948072239842994867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 983307930762986457326489 737480948072239842994867)
              ·
                refine ⟨1106221422108359764492301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 737480948072239842994867 1106221422108359764492301)
                ·
                  refine ⟨414833033290634911684613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1106221422108359764492301 414833033290634911684613)
                  ·
                    rfl

theorem cell20_908870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 2, 1, 3].length) (baseStart_908870 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_908870 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_908870 prefixEnd_908870 := by exact prefixLift 908870
  have htrace : WordTrace (prefixWord ++ tailWord_908870) baseStart_908870 baseEnd_908870 := by
    simpa [prefixWord, tailWord_908870, baseEnd_908870] using wordTrace_append hprefix tailTrace_908870
  have hstable : (prefixWord ++ tailWord_908870).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908870).length < 2 ^ (prefixWord ++ tailWord_908870).sum := by decide
  have hdescent : baseEnd_908870 < baseStart_908870 := by decide
  rcases family_descends (prefixWord ++ tailWord_908870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908892 : List Nat := [2, 2, 4, 1, 2, 1, 2, 6]
def baseStart_908892 : Nat := 118140960795 + 908892 * 2 ^ 59
def prefixEnd_908892 : Nat := 4983230072969 + 3 ^ 40 * 908892 * 2
def baseEnd_908892 : Nat := 138281024896700204317063

theorem tailTrace_908892 : CollatzResearch.WordTrace tailWord_908892 prefixEnd_908892 138281024896700204317063 := by
  unfold tailWord_908892
  simp only [CollatzResearch.WordTrace]
  refine ⟨16575007311623492620252465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22100009748831323493669953 16575007311623492620252465)
  ·
    refine ⟨12431255483717619465189349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16575007311623492620252465 12431255483717619465189349)
    ·
      refine ⟨2330860403197053649723003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12431255483717619465189349 2330860403197053649723003)
      ·
        refine ⟨3496290604795580474584505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2330860403197053649723003 3496290604795580474584505)
        ·
          refine ⟨2622217953596685355938379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3496290604795580474584505 2622217953596685355938379)
          ·
            refine ⟨3933326930395028033907569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2622217953596685355938379 3933326930395028033907569)
            ·
              refine ⟨2949995197796271025430677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3933326930395028033907569 2949995197796271025430677)
              ·
                refine ⟨138281024896700204317063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2949995197796271025430677 138281024896700204317063)
                ·
                  rfl

theorem cell20_908892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 6].length) (baseStart_908892 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_908892 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_908892 prefixEnd_908892 := by exact prefixLift 908892
  have htrace : WordTrace (prefixWord ++ tailWord_908892) baseStart_908892 baseEnd_908892 := by
    simpa [prefixWord, tailWord_908892, baseEnd_908892] using wordTrace_append hprefix tailTrace_908892
  have hstable : (prefixWord ++ tailWord_908892).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908892).length < 2 ^ (prefixWord ++ tailWord_908892).sum := by decide
  have hdescent : baseEnd_908892 < baseStart_908892 := by decide
  rcases family_descends (prefixWord ++ tailWord_908892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908923 : List Nat := [1, 1, 1, 1, 1, 4, 5, 4, 2]
def baseStart_908923 : Nat := 118140960795 + 908923 * 2 ^ 59
def prefixEnd_908923 : Nat := 4983230072969 + 3 ^ 40 * 908923 * 2
def baseEnd_908923 : Nat := 414857223934802282917729

theorem tailTrace_908923 : CollatzResearch.WordTrace tailWord_908923 prefixEnd_908923 414857223934802282917729 := by
  unfold tailWord_908923
  simp only [CollatzResearch.WordTrace]
  refine ⟨33151145286134677534883423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22100763524089785023255615 33151145286134677534883423)
  ·
    refine ⟨49726717929202016302325135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33151145286134677534883423 49726717929202016302325135)
    ·
      refine ⟨74590076893803024453487703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49726717929202016302325135 74590076893803024453487703)
      ·
        refine ⟨111885115340704536680231555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74590076893803024453487703 111885115340704536680231555)
        ·
          refine ⟨167827673011056805020347333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 111885115340704536680231555 167827673011056805020347333)
          ·
            refine ⟨31467688689573150941315125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 167827673011056805020347333 31467688689573150941315125)
            ·
              refine ⟨2950095814647482900748293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31467688689573150941315125 2950095814647482900748293)
              ·
                refine ⟨553142965246403043890305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2950095814647482900748293 553142965246403043890305)
                ·
                  refine ⟨414857223934802282917729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 553142965246403043890305 414857223934802282917729)
                  ·
                    rfl

theorem cell20_908923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 4, 2].length) (baseStart_908923 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_908923 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_908923 prefixEnd_908923 := by exact prefixLift 908923
  have htrace : WordTrace (prefixWord ++ tailWord_908923) baseStart_908923 baseEnd_908923 := by
    simpa [prefixWord, tailWord_908923, baseEnd_908923] using wordTrace_append hprefix tailTrace_908923
  have hstable : (prefixWord ++ tailWord_908923).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908923).length < 2 ^ (prefixWord ++ tailWord_908923).sum := by decide
  have hdescent : baseEnd_908923 < baseStart_908923 := by decide
  rcases family_descends (prefixWord ++ tailWord_908923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908937 : List Nat := [1, 2, 1, 1, 4, 1, 4, 3, 3]
def baseStart_908937 : Nat := 118140960795 + 908937 * 2 ^ 59
def prefixEnd_908937 : Nat := 4983230072969 + 3 ^ 40 * 908937 * 2
def baseEnd_908937 : Nat := 414863613916280456451005

theorem tailTrace_908937 : CollatzResearch.WordTrace tailWord_908937 prefixEnd_908937 414863613916280456451005 := by
  unfold tailWord_908937
  simp only [CollatzResearch.WordTrace]
  refine ⟨33151655908083957925893065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22101103938722638617262043 33151655908083957925893065)
  ·
    refine ⟨24863741931062968444419799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33151655908083957925893065 24863741931062968444419799)
    ·
      refine ⟨37295612896594452666629699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24863741931062968444419799 37295612896594452666629699)
      ·
        refine ⟨55943419344891678999944549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37295612896594452666629699 55943419344891678999944549)
        ·
          refine ⟨10489391127167189812489603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55943419344891678999944549 10489391127167189812489603)
          ·
            refine ⟨15734086690750784718734405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10489391127167189812489603 15734086690750784718734405)
            ·
              refine ⟨2950141254515772134762701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15734086690750784718734405 2950141254515772134762701)
              ·
                refine ⟨1106302970443414550536013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2950141254515772134762701 1106302970443414550536013)
                ·
                  refine ⟨414863613916280456451005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1106302970443414550536013 414863613916280456451005)
                  ·
                    rfl

theorem cell20_908937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 3, 3].length) (baseStart_908937 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_908937 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_908937 prefixEnd_908937 := by exact prefixLift 908937
  have htrace : WordTrace (prefixWord ++ tailWord_908937) baseStart_908937 baseEnd_908937 := by
    simpa [prefixWord, tailWord_908937, baseEnd_908937] using wordTrace_append hprefix tailTrace_908937
  have hstable : (prefixWord ++ tailWord_908937).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908937).length < 2 ^ (prefixWord ++ tailWord_908937).sum := by decide
  have hdescent : baseEnd_908937 < baseStart_908937 := by decide
  rcases family_descends (prefixWord ++ tailWord_908937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908989 : List Nat := [1, 4, 1, 2, 1, 2, 2, 7]
def baseStart_908989 : Nat := 118140960795 + 908989 * 2 ^ 59
def prefixEnd_908989 : Nat := 4983230072969 + 3 ^ 40 * 908989 * 2
def baseEnd_908989 : Nat := 138295782711066462239153

theorem tailTrace_908989 : CollatzResearch.WordTrace tailWord_908989 prefixEnd_908989 138295782711066462239153 := by
  unfold tailWord_908989
  simp only [CollatzResearch.WordTrace]
  refine ⟨33153552503895570806786021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22102368335930380537857347 33153552503895570806786021)
  ·
    refine ⟨6216291094480419526272379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33153552503895570806786021 6216291094480419526272379)
    ·
      refine ⟨9324436641720629289408569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6216291094480419526272379 9324436641720629289408569)
      ·
        refine ⟨6993327481290471967056427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9324436641720629289408569 6993327481290471967056427)
        ·
          refine ⟨10489991221935707950584641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6993327481290471967056427 10489991221935707950584641)
          ·
            refine ⟨7867493416451780962938481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10489991221935707950584641 7867493416451780962938481)
            ·
              refine ⟨5900620062338835722203861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7867493416451780962938481 5900620062338835722203861)
              ·
                refine ⟨138295782711066462239153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5900620062338835722203861 138295782711066462239153)
                ·
                  rfl

theorem cell20_908989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 7].length) (baseStart_908989 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_908989 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_908989 prefixEnd_908989 := by exact prefixLift 908989
  have htrace : WordTrace (prefixWord ++ tailWord_908989) baseStart_908989 baseEnd_908989 := by
    simpa [prefixWord, tailWord_908989, baseEnd_908989] using wordTrace_append hprefix tailTrace_908989
  have hstable : (prefixWord ++ tailWord_908989).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908989).length < 2 ^ (prefixWord ++ tailWord_908989).sum := by decide
  have hdescent : baseEnd_908989 < baseStart_908989 := by decide
  rcases family_descends (prefixWord ++ tailWord_908989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_908992 : List Nat := [2, 1, 1, 2, 4, 1, 5, 1, 3]
def baseStart_908992 : Nat := 118140960795 + 908992 * 2 ^ 59
def prefixEnd_908992 : Nat := 4983230072969 + 3 ^ 40 * 908992 * 2
def baseEnd_908992 : Nat := 414888717414944709617447

theorem tailTrace_908992 : CollatzResearch.WordTrace tailWord_908992 prefixEnd_908992 414888717414944709617447 := by
  unfold tailWord_908992
  simp only [CollatzResearch.WordTrace]
  refine ⟨16576830961442351159572615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22102441281923134879430153 16576830961442351159572615)
  ·
    refine ⟨24865246442163526739358923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16576830961442351159572615 24865246442163526739358923)
    ·
      refine ⟨37297869663245290109038385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24865246442163526739358923 37297869663245290109038385)
      ·
        refine ⟨27973402247433967581778789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37297869663245290109038385 27973402247433967581778789)
        ·
          refine ⟨5245012921393868921583523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27973402247433967581778789 5245012921393868921583523)
          ·
            refine ⟨7867519382090803382375285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5245012921393868921583523 7867519382090803382375285)
            ·
              refine ⟨737579942071012817097683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7867519382090803382375285 737579942071012817097683)
              ·
                refine ⟨1106369913106519225646525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 737579942071012817097683 1106369913106519225646525)
                ·
                  refine ⟨414888717414944709617447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1106369913106519225646525 414888717414944709617447)
                  ·
                    rfl

theorem cell20_908992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 5, 1, 3].length) (baseStart_908992 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_908992 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_908992 prefixEnd_908992 := by exact prefixLift 908992
  have htrace : WordTrace (prefixWord ++ tailWord_908992) baseStart_908992 baseEnd_908992 := by
    simpa [prefixWord, tailWord_908992, baseEnd_908992] using wordTrace_append hprefix tailTrace_908992
  have hstable : (prefixWord ++ tailWord_908992).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_908992).length < 2 ^ (prefixWord ++ tailWord_908992).sum := by decide
  have hdescent : baseEnd_908992 < baseStart_908992 := by decide
  rcases family_descends (prefixWord ++ tailWord_908992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909002 : List Nat := [3, 1, 2, 1, 6, 1, 2, 4]
def baseStart_909002 : Nat := 118140960795 + 909002 * 2 ^ 59
def prefixEnd_909002 : Nat := 4983230072969 + 3 ^ 40 * 909002 * 2
def baseEnd_909002 : Nat := 138297760562476373094691

theorem tailTrace_909002 : CollatzResearch.WordTrace tailWord_909002 prefixEnd_909002 138297760562476373094691 := by
  unfold tailWord_909002
  simp only [CollatzResearch.WordTrace]
  refine ⟨8288506663212118506752315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22102684435232316018006173 8288506663212118506752315)
  ·
    refine ⟨12432759994818177760128473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8288506663212118506752315 12432759994818177760128473)
    ·
      refine ⟨9324569996113633320096355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12432759994818177760128473 9324569996113633320096355)
      ·
        refine ⟨13986854994170449980144533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9324569996113633320096355 13986854994170449980144533)
        ·
          refine ⟨655633827851739842819275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 13986854994170449980144533 655633827851739842819275)
          ·
            refine ⟨983450741777609764228913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 655633827851739842819275 983450741777609764228913)
            ·
              refine ⟨737588056333207323171685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 983450741777609764228913 737588056333207323171685)
              ·
                refine ⟨138297760562476373094691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 737588056333207323171685 138297760562476373094691)
                ·
                  rfl

theorem cell20_909002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 2, 4].length) (baseStart_909002 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_909002 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_909002 prefixEnd_909002 := by exact prefixLift 909002
  have htrace : WordTrace (prefixWord ++ tailWord_909002) baseStart_909002 baseEnd_909002 := by
    simpa [prefixWord, tailWord_909002, baseEnd_909002] using wordTrace_append hprefix tailTrace_909002
  have hstable : (prefixWord ++ tailWord_909002).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909002).length < 2 ^ (prefixWord ++ tailWord_909002).sum := by decide
  have hdescent : baseEnd_909002 < baseStart_909002 := by decide
  rcases family_descends (prefixWord ++ tailWord_909002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909037 : List Nat := [1, 5, 1, 2, 1, 2, 3, 1, 4]
def baseStart_909037 : Nat := 118140960795 + 909037 * 2 ^ 59
def prefixEnd_909037 : Nat := 4983230072969 + 3 ^ 40 * 909037 * 2
def baseEnd_909037 : Nat := 414909256641124553117263

theorem tailTrace_909037 : CollatzResearch.WordTrace tailWord_909037 prefixEnd_909037 414909256641124553117263 := by
  unfold tailWord_909037
  simp only [CollatzResearch.WordTrace]
  refine ⟨33155303207721675004533365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22103535471814450003022243 33155303207721675004533365)
  ·
    refine ⟨3108309675723907031675003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33155303207721675004533365 3108309675723907031675003)
    ·
      refine ⟨4662464513585860547512505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3108309675723907031675003 4662464513585860547512505)
      ·
        refine ⟨3496848385189395410634379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4662464513585860547512505 3496848385189395410634379)
        ·
          refine ⟨5245272577784093115951569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3496848385189395410634379 5245272577784093115951569)
          ·
            refine ⟨3933954433338069836963677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5245272577784093115951569 3933954433338069836963677)
            ·
              refine ⟨1475232912501776188861379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3933954433338069836963677 1475232912501776188861379)
              ·
                refine ⟨2212849368752664283292069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1475232912501776188861379 2212849368752664283292069)
                ·
                  refine ⟨414909256641124553117263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2212849368752664283292069 414909256641124553117263)
                  ·
                    rfl

theorem cell20_909037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_909037 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_909037 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_909037 prefixEnd_909037 := by exact prefixLift 909037
  have htrace : WordTrace (prefixWord ++ tailWord_909037) baseStart_909037 baseEnd_909037 := by
    simpa [prefixWord, tailWord_909037, baseEnd_909037] using wordTrace_append hprefix tailTrace_909037
  have hstable : (prefixWord ++ tailWord_909037).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909037).length < 2 ^ (prefixWord ++ tailWord_909037).sum := by decide
  have hdescent : baseEnd_909037 < baseStart_909037 := by decide
  rcases family_descends (prefixWord ++ tailWord_909037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909089 : List Nat := [1, 2, 3, 2, 1, 3, 1, 4, 3]
def baseStart_909089 : Nat := 118140960795 + 909089 * 2 ^ 59
def prefixEnd_909089 : Nat := 4983230072969 + 3 ^ 40 * 909089 * 2
def baseEnd_909089 : Nat := 414932990858043483383717

theorem tailTrace_909089 : CollatzResearch.WordTrace tailWord_909089 prefixEnd_909089 414932990858043483383717 := by
  unfold tailWord_909089
  simp only [CollatzResearch.WordTrace]
  refine ⟨33157199803533287885426321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22104799869022191923617547 33157199803533287885426321)
  ·
    refine ⟨24867899852649965914069741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33157199803533287885426321 24867899852649965914069741)
    ·
      refine ⟨9325462444743737217776153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24867899852649965914069741 9325462444743737217776153)
      ·
        refine ⟨6994096833557802913332115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9325462444743737217776153 6994096833557802913332115)
        ·
          refine ⟨10491145250336704369998173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6994096833557802913332115 10491145250336704369998173)
          ·
            refine ⟨3934179468876264138749315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10491145250336704369998173 3934179468876264138749315)
            ·
              refine ⟨5901269203314396208123973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3934179468876264138749315 5901269203314396208123973)
              ·
                refine ⟨1106487975621449289023245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5901269203314396208123973 1106487975621449289023245)
                ·
                  refine ⟨414932990858043483383717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1106487975621449289023245 414932990858043483383717)
                  ·
                    rfl

theorem cell20_909089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 4, 3].length) (baseStart_909089 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_909089 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_909089 prefixEnd_909089 := by exact prefixLift 909089
  have htrace : WordTrace (prefixWord ++ tailWord_909089) baseStart_909089 baseEnd_909089 := by
    simpa [prefixWord, tailWord_909089, baseEnd_909089] using wordTrace_append hprefix tailTrace_909089
  have hstable : (prefixWord ++ tailWord_909089).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909089).length < 2 ^ (prefixWord ++ tailWord_909089).sum := by decide
  have hdescent : baseEnd_909089 < baseStart_909089 := by decide
  rcases family_descends (prefixWord ++ tailWord_909089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909092 : List Nat := [2, 3, 1, 3, 2, 2, 1, 4, 2]
def baseStart_909092 : Nat := 118140960795 + 909092 * 2 ^ 59
def prefixEnd_909092 : Nat := 4983230072969 + 3 ^ 40 * 909092 * 2
def baseEnd_909092 : Nat := 414934360139788806283705

theorem tailTrace_909092 : CollatzResearch.WordTrace tailWord_909092 prefixEnd_909092 414934360139788806283705 := by
  unfold tailWord_909092
  simp only [CollatzResearch.WordTrace]
  refine ⟨16578654611261209698892765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22104872815014946265190353 16578654611261209698892765)
  ·
    refine ⟨6216995479222953637084787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16578654611261209698892765 6216995479222953637084787)
    ·
      refine ⟨9325493218834430455627181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6216995479222953637084787 9325493218834430455627181)
      ·
        refine ⟨3497059957062911420860193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9325493218834430455627181 3497059957062911420860193)
        ·
          refine ⟨2622794967797183565645145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3497059957062911420860193 2622794967797183565645145)
          ·
            refine ⟨1967096225847887674233859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2622794967797183565645145 1967096225847887674233859)
            ·
              refine ⟨2950644338771831511350789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1967096225847887674233859 2950644338771831511350789)
              ·
                refine ⟨553245813519718408378273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2950644338771831511350789 553245813519718408378273)
                ·
                  refine ⟨414934360139788806283705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 553245813519718408378273 414934360139788806283705)
                  ·
                    rfl

theorem cell20_909092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 4, 2].length) (baseStart_909092 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_909092 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_909092 prefixEnd_909092 := by exact prefixLift 909092
  have htrace : WordTrace (prefixWord ++ tailWord_909092) baseStart_909092 baseEnd_909092 := by
    simpa [prefixWord, tailWord_909092, baseEnd_909092] using wordTrace_append hprefix tailTrace_909092
  have hstable : (prefixWord ++ tailWord_909092).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909092).length < 2 ^ (prefixWord ++ tailWord_909092).sum := by decide
  have hdescent : baseEnd_909092 < baseStart_909092 := by decide
  rcases family_descends (prefixWord ++ tailWord_909092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909126 : List Nat := [6, 1, 1, 2, 1, 2, 2, 3, 2]
def baseStart_909126 : Nat := 118140960795 + 909126 * 2 ^ 59
def prefixEnd_909126 : Nat := 4983230072969 + 3 ^ 40 * 909126 * 2
def baseEnd_909126 : Nat := 414949878666235799150233

theorem tailTrace_909126 : CollatzResearch.WordTrace tailWord_909126 prefixEnd_909126 414949878666235799150233 := by
  unfold tailWord_909126
  simp only [CollatzResearch.WordTrace]
  refine ⟨1036204665762476350141351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 22105699536266162136348821 1036204665762476350141351)
  ·
    refine ⟨1554306998643714525212027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1036204665762476350141351 1554306998643714525212027)
    ·
      refine ⟨2331460497965571787818041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1554306998643714525212027 2331460497965571787818041)
      ·
        refine ⟨1748595373474178840863531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2331460497965571787818041 1748595373474178840863531)
        ·
          refine ⟨2622893060211268261295297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1748595373474178840863531 2622893060211268261295297)
          ·
            refine ⟨1967169795158451195971473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2622893060211268261295297 1967169795158451195971473)
            ·
              refine ⟨1475377346368838396978605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1967169795158451195971473 1475377346368838396978605)
              ·
                refine ⟨553266504888314398866977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1475377346368838396978605 553266504888314398866977)
                ·
                  refine ⟨414949878666235799150233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 553266504888314398866977 414949878666235799150233)
                  ·
                    rfl

theorem cell20_909126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 2, 3, 2].length) (baseStart_909126 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_909126 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_909126 prefixEnd_909126 := by exact prefixLift 909126
  have htrace : WordTrace (prefixWord ++ tailWord_909126) baseStart_909126 baseEnd_909126 := by
    simpa [prefixWord, tailWord_909126, baseEnd_909126] using wordTrace_append hprefix tailTrace_909126
  have hstable : (prefixWord ++ tailWord_909126).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909126).length < 2 ^ (prefixWord ++ tailWord_909126).sum := by decide
  have hdescent : baseEnd_909126 < baseStart_909126 := by decide
  rcases family_descends (prefixWord ++ tailWord_909126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909141 : List Nat := [1, 3, 2, 2, 2, 3, 7]
def baseStart_909141 : Nat := 118140960795 + 909141 * 2 ^ 59
def prefixEnd_909141 : Nat := 4983230072969 + 3 ^ 40 * 909141 * 2
def baseEnd_909141 : Nat := 46106302786106934850019

theorem tailTrace_909141 : CollatzResearch.WordTrace tailWord_909141 prefixEnd_909141 46106302786106934850019 := by
  unfold tailWord_909141
  simp only [CollatzResearch.WordTrace]
  refine ⟨33159096399344900766319277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22106064266229933844212851 33159096399344900766319277)
  ·
    refine ⟨12434661149754337787369729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33159096399344900766319277 12434661149754337787369729)
    ·
      refine ⟨9325995862315753340527297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12434661149754337787369729 9325995862315753340527297)
      ·
        refine ⟨6994496896736815005395473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9325995862315753340527297 6994496896736815005395473)
        ·
          refine ⟨5245872672552611254046605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6994496896736815005395473 5245872672552611254046605)
          ·
            refine ⟨1967202252207229220267477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5245872672552611254046605 1967202252207229220267477)
            ·
              refine ⟨46106302786106934850019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1967202252207229220267477 46106302786106934850019)
              ·
                rfl

theorem cell20_909141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 7].length) (baseStart_909141 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_909141 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_909141 prefixEnd_909141 := by exact prefixLift 909141
  have htrace : WordTrace (prefixWord ++ tailWord_909141) baseStart_909141 baseEnd_909141 := by
    simpa [prefixWord, tailWord_909141, baseEnd_909141] using wordTrace_append hprefix tailTrace_909141
  have hstable : (prefixWord ++ tailWord_909141).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909141).length < 2 ^ (prefixWord ++ tailWord_909141).sum := by decide
  have hdescent : baseEnd_909141 < baseStart_909141 := by decide
  rcases family_descends (prefixWord ++ tailWord_909141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909151 : List Nat := [1, 1, 2, 3, 1, 4, 2, 4, 2]
def baseStart_909151 : Nat := 118140960795 + 909151 * 2 ^ 59
def prefixEnd_909151 : Nat := 4983230072969 + 3 ^ 40 * 909151 * 2
def baseEnd_909151 : Nat := 414961289347446823316797

theorem tailTrace_909151 : CollatzResearch.WordTrace tailWord_909151 prefixEnd_909151 414961289347446823316797 := by
  unfold tailWord_909151
  simp only [CollatzResearch.WordTrace]
  refine ⟨33159461129308672474183307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22106307419539114982788871 33159461129308672474183307)
  ·
    refine ⟨49739191693963008711274961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33159461129308672474183307 49739191693963008711274961)
    ·
      refine ⟨37304393770472256533456221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49739191693963008711274961 37304393770472256533456221)
      ·
        refine ⟨13989147663927096200046083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37304393770472256533456221 13989147663927096200046083)
        ·
          refine ⟨20983721495890644300069125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13989147663927096200046083 20983721495890644300069125)
          ·
            refine ⟨3934447780479495806262961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20983721495890644300069125 3934447780479495806262961)
            ·
              refine ⟨2950835835359621854697221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3934447780479495806262961 2950835835359621854697221)
              ·
                refine ⟨553281719129929097755729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2950835835359621854697221 553281719129929097755729)
                ·
                  refine ⟨414961289347446823316797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 553281719129929097755729 414961289347446823316797)
                  ·
                    rfl

theorem cell20_909151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 4, 2].length) (baseStart_909151 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_909151 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_909151 prefixEnd_909151 := by exact prefixLift 909151
  have htrace : WordTrace (prefixWord ++ tailWord_909151) baseStart_909151 baseEnd_909151 := by
    simpa [prefixWord, tailWord_909151, baseEnd_909151] using wordTrace_append hprefix tailTrace_909151
  have hstable : (prefixWord ++ tailWord_909151).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909151).length < 2 ^ (prefixWord ++ tailWord_909151).sum := by decide
  have hdescent : baseEnd_909151 < baseStart_909151 := by decide
  rcases family_descends (prefixWord ++ tailWord_909151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909165 : List Nat := [1, 5, 1, 1, 1, 1, 2, 5, 3]
def baseStart_909165 : Nat := 118140960795 + 909165 * 2 ^ 59
def prefixEnd_909165 : Nat := 4983230072969 + 3 ^ 40 * 909165 * 2
def baseEnd_909165 : Nat := 414967679328924996850073

theorem tailTrace_909165 : CollatzResearch.WordTrace tailWord_909165 prefixEnd_909165 414967679328924996850073 := by
  unfold tailWord_909165
  simp only [CollatzResearch.WordTrace]
  refine ⟨33159971751257952865192949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22106647834171968576795299 33159971751257952865192949)
  ·
    refine ⟨3108747351680433081111839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33159971751257952865192949 3108747351680433081111839)
    ·
      refine ⟨4663121027520649621667759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3108747351680433081111839 4663121027520649621667759)
      ·
        refine ⟨6994681541280974432501639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4663121027520649621667759 6994681541280974432501639)
        ·
          refine ⟨10492022311921461648752459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6994681541280974432501639 10492022311921461648752459)
          ·
            refine ⟨15738033467882192473128689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10492022311921461648752459 15738033467882192473128689)
            ·
              refine ⟨11803525100911644354846517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15738033467882192473128689 11803525100911644354846517)
              ·
                refine ⟨1106580478210466658266861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11803525100911644354846517 1106580478210466658266861)
                ·
                  refine ⟨414967679328924996850073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1106580478210466658266861 414967679328924996850073)
                  ·
                    rfl

theorem cell20_909165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 5, 3].length) (baseStart_909165 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_909165 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_909165 prefixEnd_909165 := by exact prefixLift 909165
  have htrace : WordTrace (prefixWord ++ tailWord_909165) baseStart_909165 baseEnd_909165 := by
    simpa [prefixWord, tailWord_909165, baseEnd_909165] using wordTrace_append hprefix tailTrace_909165
  have hstable : (prefixWord ++ tailWord_909165).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909165).length < 2 ^ (prefixWord ++ tailWord_909165).sum := by decide
  have hdescent : baseEnd_909165 < baseStart_909165 := by decide
  rcases family_descends (prefixWord ++ tailWord_909165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909182 : List Nat := [4, 2, 3, 1, 1, 1, 1, 2, 5]
def baseStart_909182 : Nat := 118140960795 + 909182 * 2 ^ 59
def prefixEnd_909182 : Nat := 4983230072969 + 3 ^ 40 * 909182 * 2
def baseEnd_909182 : Nat := 414975438592148493283337

theorem tailTrace_909182 : CollatzResearch.WordTrace tailWord_909182 prefixEnd_909182 414975438592148493283337 := by
  unfold tailWord_909182
  simp only [CollatzResearch.WordTrace]
  refine ⟨4145073974024545596070225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22107061194797576512374533 4145073974024545596070225)
  ·
    refine ⟨3108805480518409197052669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4145073974024545596070225 3108805480518409197052669)
    ·
      refine ⟨1165802055194403448894751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3108805480518409197052669 1165802055194403448894751)
      ·
        refine ⟨1748703082791605173342127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1165802055194403448894751 1748703082791605173342127)
        ·
          refine ⟨2623054624187407760013191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1748703082791605173342127 2623054624187407760013191)
          ·
            refine ⟨3934581936281111640019787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2623054624187407760013191 3934581936281111640019787)
            ·
              refine ⟨5901872904421667460029681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3934581936281111640019787 5901872904421667460029681)
              ·
                refine ⟨4426404678316250595022261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5901872904421667460029681 4426404678316250595022261)
                ·
                  refine ⟨414975438592148493283337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4426404678316250595022261 414975438592148493283337)
                  ·
                    rfl

theorem cell20_909182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 2, 5].length) (baseStart_909182 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_909182 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_909182 prefixEnd_909182 := by exact prefixLift 909182
  have htrace : WordTrace (prefixWord ++ tailWord_909182) baseStart_909182 baseEnd_909182 := by
    simpa [prefixWord, tailWord_909182, baseEnd_909182] using wordTrace_append hprefix tailTrace_909182
  have hstable : (prefixWord ++ tailWord_909182).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909182).length < 2 ^ (prefixWord ++ tailWord_909182).sum := by decide
  have hdescent : baseEnd_909182 < baseStart_909182 := by decide
  rcases family_descends (prefixWord ++ tailWord_909182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909220 : List Nat := [2, 3, 1, 2, 1, 3, 4, 1, 3]
def baseStart_909220 : Nat := 118140960795 + 909220 * 2 ^ 59
def prefixEnd_909220 : Nat := 4983230072969 + 3 ^ 40 * 909220 * 2
def baseEnd_909220 : Nat := 414992782827589250016515

theorem tailTrace_909220 : CollatzResearch.WordTrace tailWord_909220 prefixEnd_909220 414992782827589250016515 := by
  unfold tailWord_909220
  simp only [CollatzResearch.WordTrace]
  refine ⟨16580988883029348629222557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22107985177372464838963409 16580988883029348629222557)
  ·
    refine ⟨6217870831136005735958459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16580988883029348629222557 6217870831136005735958459)
    ·
      refine ⟨9326806246704008603937689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6217870831136005735958459 9326806246704008603937689)
      ·
        refine ⟨6995104685028006452953267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9326806246704008603937689 6995104685028006452953267)
        ·
          refine ⟨10492657027542009679429901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6995104685028006452953267 10492657027542009679429901)
          ·
            refine ⟨3934746385328253629786213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10492657027542009679429901 3934746385328253629786213)
            ·
              refine ⟨737764947249047555584915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3934746385328253629786213 737764947249047555584915)
              ·
                refine ⟨1106647420873571333377373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 737764947249047555584915 1106647420873571333377373)
                ·
                  refine ⟨414992782827589250016515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1106647420873571333377373 414992782827589250016515)
                  ·
                    rfl

theorem cell20_909220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 4, 1, 3].length) (baseStart_909220 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_909220 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_909220 prefixEnd_909220 := by exact prefixLift 909220
  have htrace : WordTrace (prefixWord ++ tailWord_909220) baseStart_909220 baseEnd_909220 := by
    simpa [prefixWord, tailWord_909220, baseEnd_909220] using wordTrace_append hprefix tailTrace_909220
  have hstable : (prefixWord ++ tailWord_909220).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909220).length < 2 ^ (prefixWord ++ tailWord_909220).sum := by decide
  have hdescent : baseEnd_909220 < baseStart_909220 := by decide
  rcases family_descends (prefixWord ++ tailWord_909220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909231 : List Nat := [1, 1, 2, 1, 2, 2, 4, 1, 6]
def baseStart_909231 : Nat := 118140960795 + 909231 * 2 ^ 59
def prefixEnd_909231 : Nat := 4983230072969 + 3 ^ 40 * 909231 * 2
def baseEnd_909231 : Nat := 414997803527322100649803

theorem tailTrace_909231 : CollatzResearch.WordTrace tailWord_909231 prefixEnd_909231 414997803527322100649803 := by
  unfold tailWord_909231
  simp only [CollatzResearch.WordTrace]
  refine ⟨33162378969018846137095547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22108252646012564091397031 33162378969018846137095547)
  ·
    refine ⟨49743568453528269205643321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33162378969018846137095547 49743568453528269205643321)
    ·
      refine ⟨37307676340146201904232491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49743568453528269205643321 37307676340146201904232491)
      ·
        refine ⟨55961514510219302856348737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37307676340146201904232491 55961514510219302856348737)
        ·
          refine ⟨41971135882664477142261553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55961514510219302856348737 41971135882664477142261553)
          ·
            refine ⟨31478351911998357856696165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41971135882664477142261553 31478351911998357856696165)
            ·
              refine ⟨5902190983499692098130531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31478351911998357856696165 5902190983499692098130531)
              ·
                refine ⟨8853286475249538147195797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5902190983499692098130531 8853286475249538147195797)
                ·
                  refine ⟨414997803527322100649803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8853286475249538147195797 414997803527322100649803)
                  ·
                    rfl

theorem cell20_909231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 1, 6].length) (baseStart_909231 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_909231 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_909231 prefixEnd_909231 := by exact prefixLift 909231
  have htrace : WordTrace (prefixWord ++ tailWord_909231) baseStart_909231 baseEnd_909231 := by
    simpa [prefixWord, tailWord_909231, baseEnd_909231] using wordTrace_append hprefix tailTrace_909231
  have hstable : (prefixWord ++ tailWord_909231).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909231).length < 2 ^ (prefixWord ++ tailWord_909231).sum := by decide
  have hdescent : baseEnd_909231 < baseStart_909231 := by decide
  rcases family_descends (prefixWord ++ tailWord_909231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909279 : List Nat := [1, 1, 2, 3, 4, 1, 2, 3, 3]
def baseStart_909279 : Nat := 118140960795 + 909279 * 2 ^ 59
def prefixEnd_909279 : Nat := 4983230072969 + 3 ^ 40 * 909279 * 2
def baseEnd_909279 : Nat := 415019712035247267049607

theorem tailTrace_909279 : CollatzResearch.WordTrace tailWord_909279 prefixEnd_909279 415019712035247267049607 := by
  unfold tailWord_909279
  simp only [CollatzResearch.WordTrace]
  refine ⟨33164129672844950334842891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22109419781896633556561927 33164129672844950334842891)
  ·
    refine ⟨49746194509267425502264337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33164129672844950334842891 49746194509267425502264337)
    ·
      refine ⟨37309645881950569126698253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49746194509267425502264337 37309645881950569126698253)
      ·
        refine ⟨13991117205731463422511845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37309645881950569126698253 13991117205731463422511845)
        ·
          refine ⟨2623334476074649391720971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13991117205731463422511845 2623334476074649391720971)
          ·
            refine ⟨3935001714111974087581457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2623334476074649391720971 3935001714111974087581457)
            ·
              refine ⟨2951251285583980565686093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3935001714111974087581457 2951251285583980565686093)
              ·
                refine ⟨1106719232093992712132285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2951251285583980565686093 1106719232093992712132285)
                ·
                  refine ⟨415019712035247267049607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1106719232093992712132285 415019712035247267049607)
                  ·
                    rfl

theorem cell20_909279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 3, 3].length) (baseStart_909279 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_909279 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_909279 prefixEnd_909279 := by exact prefixLift 909279
  have htrace : WordTrace (prefixWord ++ tailWord_909279) baseStart_909279 baseEnd_909279 := by
    simpa [prefixWord, tailWord_909279, baseEnd_909279] using wordTrace_append hprefix tailTrace_909279
  have hstable : (prefixWord ++ tailWord_909279).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909279).length < 2 ^ (prefixWord ++ tailWord_909279).sum := by decide
  have hdescent : baseEnd_909279 < baseStart_909279 := by decide
  rcases family_descends (prefixWord ++ tailWord_909279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909282 : List Nat := [3, 3, 3, 1, 2, 1, 1, 2, 4]
def baseStart_909282 : Nat := 118140960795 + 909282 * 2 ^ 59
def prefixEnd_909282 : Nat := 4983230072969 + 3 ^ 40 * 909282 * 2
def baseEnd_909282 : Nat := 415021081316992589949595

theorem tailTrace_909282 : CollatzResearch.WordTrace tailWord_909282 prefixEnd_909282 415021081316992589949595 := by
  unfold tailWord_909282
  simp only [CollatzResearch.WordTrace]
  refine ⟨8291059772958520461800525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22109492727889387898134733 8291059772958520461800525)
  ·
    refine ⟨3109147414859445173175197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8291059772958520461800525 3109147414859445173175197)
    ·
      refine ⟨1165930280572291939940699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3109147414859445173175197 1165930280572291939940699)
      ·
        refine ⟨1748895420858437909911049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1165930280572291939940699 1748895420858437909911049)
        ·
          refine ⟨1311671565643828432433287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1748895420858437909911049 1311671565643828432433287)
          ·
            refine ⟨1967507348465742648649931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1311671565643828432433287 1967507348465742648649931)
            ·
              refine ⟨2951261022698613972974897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1967507348465742648649931 2951261022698613972974897)
              ·
                refine ⟨2213445767023960479731173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2951261022698613972974897 2213445767023960479731173)
                ·
                  refine ⟨415021081316992589949595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2213445767023960479731173 415021081316992589949595)
                  ·
                    rfl

theorem cell20_909282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 2, 4].length) (baseStart_909282 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_909282 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_909282 prefixEnd_909282 := by exact prefixLift 909282
  have htrace : WordTrace (prefixWord ++ tailWord_909282) baseStart_909282 baseEnd_909282 := by
    simpa [prefixWord, tailWord_909282, baseEnd_909282] using wordTrace_append hprefix tailTrace_909282
  have hstable : (prefixWord ++ tailWord_909282).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909282).length < 2 ^ (prefixWord ++ tailWord_909282).sum := by decide
  have hdescent : baseEnd_909282 < baseStart_909282 := by decide
  rcases family_descends (prefixWord ++ tailWord_909282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909310 : List Nat := [4, 2, 2, 2, 1, 2, 7]
def baseStart_909310 : Nat := 118140960795 + 909310 * 2 ^ 59
def prefixEnd_909310 : Nat := 4983230072969 + 3 ^ 40 * 909310 * 2
def baseEnd_909310 : Nat := 46114873475549881890683

theorem tailTrace_909310 : CollatzResearch.WordTrace tailWord_909310 prefixEnd_909310 46114873475549881890683 := by
  unfold tailWord_909310
  simp only [CollatzResearch.WordTrace]
  refine ⟨4145657541966580328652673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22110173557155095086147589 4145657541966580328652673)
  ·
    refine ⟨3109243156474935246489505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4145657541966580328652673 3109243156474935246489505)
    ·
      refine ⟨2331932367356201434867129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3109243156474935246489505 2331932367356201434867129)
      ·
        refine ⟨1748949275517151076150347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2331932367356201434867129 1748949275517151076150347)
        ·
          refine ⟨2623423913275726614225521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1748949275517151076150347 2623423913275726614225521)
          ·
            refine ⟨1967567934956794960669141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2623423913275726614225521 1967567934956794960669141)
            ·
              refine ⟨46114873475549881890683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1967567934956794960669141 46114873475549881890683)
              ·
                rfl

theorem cell20_909310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 7].length) (baseStart_909310 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_909310 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_909310 prefixEnd_909310 := by exact prefixLift 909310
  have htrace : WordTrace (prefixWord ++ tailWord_909310) baseStart_909310 baseEnd_909310 := by
    simpa [prefixWord, tailWord_909310, baseEnd_909310] using wordTrace_append hprefix tailTrace_909310
  have hstable : (prefixWord ++ tailWord_909310).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909310).length < 2 ^ (prefixWord ++ tailWord_909310).sum := by decide
  have hdescent : baseEnd_909310 < baseStart_909310 := by decide
  rcases family_descends (prefixWord ++ tailWord_909310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909317 : List Nat := [1, 3, 1, 1, 2, 4, 3, 2, 3]
def baseStart_909317 : Nat := 118140960795 + 909317 * 2 ^ 59
def prefixEnd_909317 : Nat := 4983230072969 + 3 ^ 40 * 909317 * 2
def baseEnd_909317 : Nat := 415037056270688023782785

theorem tailTrace_909317 : CollatzResearch.WordTrace tailWord_909317 prefixEnd_909317 415037056270688023782785 := by
  unfold tailWord_909317
  simp only [CollatzResearch.WordTrace]
  refine ⟨33165515646707282824726205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22110343764471521883150803 33165515646707282824726205)
  ·
    refine ⟨12437068367515231059272327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33165515646707282824726205 12437068367515231059272327)
    ·
      refine ⟨18655602551272846588908491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12437068367515231059272327 18655602551272846588908491)
      ·
        refine ⟨27983403826909269883362737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18655602551272846588908491 27983403826909269883362737)
        ·
          refine ⟨20987552870181952412522053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27983403826909269883362737 20987552870181952412522053)
          ·
            refine ⟨3935166163159116077347885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20987552870181952412522053 3935166163159116077347885)
            ·
              refine ⟨1475687311184668529005457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3935166163159116077347885 1475687311184668529005457)
              ·
                refine ⟨1106765483388501396754093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1475687311184668529005457 1106765483388501396754093)
                ·
                  refine ⟨415037056270688023782785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1106765483388501396754093 415037056270688023782785)
                  ·
                    rfl

theorem cell20_909317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 3, 2, 3].length) (baseStart_909317 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_909317 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_909317 prefixEnd_909317 := by exact prefixLift 909317
  have htrace : WordTrace (prefixWord ++ tailWord_909317) baseStart_909317 baseEnd_909317 := by
    simpa [prefixWord, tailWord_909317, baseEnd_909317] using wordTrace_append hprefix tailTrace_909317
  have hstable : (prefixWord ++ tailWord_909317).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909317).length < 2 ^ (prefixWord ++ tailWord_909317).sum := by decide
  have hdescent : baseEnd_909317 < baseStart_909317 := by decide
  rcases family_descends (prefixWord ++ tailWord_909317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909324 : List Nat := [2, 2, 1, 2, 3, 1, 4, 1, 4]
def baseStart_909324 : Nat := 118140960795 + 909324 * 2 ^ 59
def prefixEnd_909324 : Nat := 4983230072969 + 3 ^ 40 * 909324 * 2
def baseEnd_909324 : Nat := 415040251261427110549423

theorem tailTrace_909324 : CollatzResearch.WordTrace tailWord_909324 prefixEnd_909324 415040251261427110549423 := by
  unfold tailWord_909324
  simp only [CollatzResearch.WordTrace]
  refine ⟨16582885478840961510115513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22110513971787948680154017 16582885478840961510115513)
  ·
    refine ⟨12437164109130721132586635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16582885478840961510115513 12437164109130721132586635)
    ·
      refine ⟨18655746163696081698879953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12437164109130721132586635 18655746163696081698879953)
      ·
        refine ⟨13991809622772061274159965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18655746163696081698879953 13991809622772061274159965)
        ·
          refine ⟨5246928608539522977809987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13991809622772061274159965 5246928608539522977809987)
          ·
            refine ⟨7870392912809284466714981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5246928608539522977809987 7870392912809284466714981)
            ·
              refine ⟨1475698671151740837509059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7870392912809284466714981 1475698671151740837509059)
              ·
                refine ⟨2213548006727611256263589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1475698671151740837509059 2213548006727611256263589)
                ·
                  refine ⟨415040251261427110549423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2213548006727611256263589 415040251261427110549423)
                  ·
                    rfl

theorem cell20_909324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 4, 1, 4].length) (baseStart_909324 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_909324 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_909324 prefixEnd_909324 := by exact prefixLift 909324
  have htrace : WordTrace (prefixWord ++ tailWord_909324) baseStart_909324 baseEnd_909324 := by
    simpa [prefixWord, tailWord_909324, baseEnd_909324] using wordTrace_append hprefix tailTrace_909324
  have hstable : (prefixWord ++ tailWord_909324).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909324).length < 2 ^ (prefixWord ++ tailWord_909324).sum := by decide
  have hdescent : baseEnd_909324 < baseStart_909324 := by decide
  rcases family_descends (prefixWord ++ tailWord_909324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909348 : List Nat := [2, 3, 1, 4, 2, 1, 1, 6]
def baseStart_909348 : Nat := 118140960795 + 909348 * 2 ^ 59
def prefixEnd_909348 : Nat := 4983230072969 + 3 ^ 40 * 909348 * 2
def baseEnd_909348 : Nat := 138350401838463231249775

theorem tailTrace_909348 : CollatzResearch.WordTrace tailWord_909348 prefixEnd_909348 138350401838463231249775 := by
  unfold tailWord_909348
  simp only [CollatzResearch.WordTrace]
  refine ⟨16583323154797487559552349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22111097539729983412736465 16583323154797487559552349)
  ·
    refine ⟨6218746183049057834832131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16583323154797487559552349 6218746183049057834832131)
    ·
      refine ⟨9328119274573586752248197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6218746183049057834832131 9328119274573586752248197)
      ·
        refine ⟨1749022363982547516046537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9328119274573586752248197 1749022363982547516046537)
        ·
          refine ⟨1311766772986910637034903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1749022363982547516046537 1311766772986910637034903)
          ·
            refine ⟨1967650159480365955552355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1311766772986910637034903 1967650159480365955552355)
            ·
              refine ⟨2951475239220548933328533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1967650159480365955552355 2951475239220548933328533)
              ·
                refine ⟨138350401838463231249775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2951475239220548933328533 138350401838463231249775)
                ·
                  rfl

theorem cell20_909348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 6].length) (baseStart_909348 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_909348 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_909348 prefixEnd_909348 := by exact prefixLift 909348
  have htrace : WordTrace (prefixWord ++ tailWord_909348) baseStart_909348 baseEnd_909348 := by
    simpa [prefixWord, tailWord_909348, baseEnd_909348] using wordTrace_append hprefix tailTrace_909348
  have hstable : (prefixWord ++ tailWord_909348).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909348).length < 2 ^ (prefixWord ++ tailWord_909348).sum := by decide
  have hdescent : baseEnd_909348 < baseStart_909348 := by decide
  rcases family_descends (prefixWord ++ tailWord_909348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909358 : List Nat := [4, 1, 3, 1, 1, 2, 3, 3, 2]
def baseStart_909358 : Nat := 118140960795 + 909358 * 2 ^ 59
def prefixEnd_909358 : Nat := 4983230072969 + 3 ^ 40 * 909358 * 2
def baseEnd_909358 : Nat := 415055769787874103415951

theorem tailTrace_909358 : CollatzResearch.WordTrace tailWord_909358 prefixEnd_909358 415055769787874103415951 := by
  unfold tailWord_909358
  simp only [CollatzResearch.WordTrace]
  refine ⟨4145876379944843353371091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22111340693039164551312485 4145876379944843353371091)
  ·
    refine ⟨6218814569917265030056637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4145876379944843353371091 6218814569917265030056637)
    ·
      refine ⟨2332055463718974386271239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6218814569917265030056637 2332055463718974386271239)
      ·
        refine ⟨3498083195578461579406859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2332055463718974386271239 3498083195578461579406859)
        ·
          refine ⟨5247124793367692369110289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3498083195578461579406859 5247124793367692369110289)
          ·
            refine ⟨3935343595025769276832717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5247124793367692369110289 3935343595025769276832717)
            ·
              refine ⟨1475753848134663478812269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3935343595025769276832717 1475753848134663478812269)
              ·
                refine ⟨553407693050498804554601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1475753848134663478812269 553407693050498804554601)
                ·
                  refine ⟨415055769787874103415951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 553407693050498804554601 415055769787874103415951)
                  ·
                    rfl

theorem cell20_909358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 3, 3, 2].length) (baseStart_909358 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_909358 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_909358 prefixEnd_909358 := by exact prefixLift 909358
  have htrace : WordTrace (prefixWord ++ tailWord_909358) baseStart_909358 baseEnd_909358 := by
    simpa [prefixWord, tailWord_909358, baseEnd_909358] using wordTrace_append hprefix tailTrace_909358
  have hstable : (prefixWord ++ tailWord_909358).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909358).length < 2 ^ (prefixWord ++ tailWord_909358).sum := by decide
  have hdescent : baseEnd_909358 < baseStart_909358 := by decide
  rcases family_descends (prefixWord ++ tailWord_909358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909376 : List Nat := [2, 1, 1, 2, 2, 4, 2, 1, 5]
def baseStart_909376 : Nat := 118140960795 + 909376 * 2 ^ 59
def prefixEnd_909376 : Nat := 4983230072969 + 3 ^ 40 * 909376 * 2
def baseEnd_909376 : Nat := 415063985478346040815877

theorem tailTrace_909376 : CollatzResearch.WordTrace tailWord_909376 prefixEnd_909376 415063985478346040815877 := by
  unfold tailWord_909376
  simp only [CollatzResearch.WordTrace]
  refine ⟨16583833776746767950561991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22111778368995690600749321 16583833776746767950561991)
  ·
    refine ⟨24875750665120151925842987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16583833776746767950561991 24875750665120151925842987)
    ·
      refine ⟨37313625997680227888764481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24875750665120151925842987 37313625997680227888764481)
      ·
        refine ⟨27985219498260170916573361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37313625997680227888764481 27985219498260170916573361)
        ·
          refine ⟨20988914623695128187430021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27985219498260170916573361 20988914623695128187430021)
          ·
            refine ⟨3935421491942836535143129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20988914623695128187430021 3935421491942836535143129)
            ·
              refine ⟨2951566118957127401357347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3935421491942836535143129 2951566118957127401357347)
              ·
                refine ⟨4427349178435691102036021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2951566118957127401357347 4427349178435691102036021)
                ·
                  refine ⟨415063985478346040815877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4427349178435691102036021 415063985478346040815877)
                  ·
                    rfl

theorem cell20_909376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 1, 5].length) (baseStart_909376 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_909376 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_909376 prefixEnd_909376 := by exact prefixLift 909376
  have htrace : WordTrace (prefixWord ++ tailWord_909376) baseStart_909376 baseEnd_909376 := by
    simpa [prefixWord, tailWord_909376, baseEnd_909376] using wordTrace_append hprefix tailTrace_909376
  have hstable : (prefixWord ++ tailWord_909376).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909376).length < 2 ^ (prefixWord ++ tailWord_909376).sum := by decide
  have hdescent : baseEnd_909376 < baseStart_909376 := by decide
  rcases family_descends (prefixWord ++ tailWord_909376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909431 : List Nat := [1, 1, 3, 1, 1, 6, 2, 2, 3]
def baseStart_909431 : Nat := 118140960795 + 909431 * 2 ^ 59
def prefixEnd_909431 : Nat := 4983230072969 + 3 ^ 40 * 909431 * 2
def baseEnd_909431 : Nat := 415089088977010293982319

theorem tailTrace_909431 : CollatzResearch.WordTrace tailWord_909431 prefixEnd_909431 415089088977010293982319 := by
  unfold tailWord_909431
  simp only [CollatzResearch.WordTrace]
  refine ⟨33169673568294280294376147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22113115712196186862917431 33169673568294280294376147)
  ·
    refine ⟨49754510352441420441564221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33169673568294280294376147 49754510352441420441564221)
    ·
      refine ⟨18657941382165532665586583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49754510352441420441564221 18657941382165532665586583)
      ·
        refine ⟨27986912073248298998379875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18657941382165532665586583 27986912073248298998379875)
        ·
          refine ⟨41980368109872448497569813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27986912073248298998379875 41980368109872448497569813)
          ·
            refine ⟨1967829755150271023323585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 41980368109872448497569813 1967829755150271023323585)
            ·
              refine ⟨1475872316362703267492689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1967829755150271023323585 1475872316362703267492689)
              ·
                refine ⟨1106904237272027450619517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1475872316362703267492689 1106904237272027450619517)
                ·
                  refine ⟨415089088977010293982319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1106904237272027450619517 415089088977010293982319)
                  ·
                    rfl

theorem cell20_909431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 2, 2, 3].length) (baseStart_909431 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_909431 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_909431 prefixEnd_909431 := by exact prefixLift 909431
  have htrace : WordTrace (prefixWord ++ tailWord_909431) baseStart_909431 baseEnd_909431 := by
    simpa [prefixWord, tailWord_909431, baseEnd_909431] using wordTrace_append hprefix tailTrace_909431
  have hstable : (prefixWord ++ tailWord_909431).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909431).length < 2 ^ (prefixWord ++ tailWord_909431).sum := by decide
  have hdescent : baseEnd_909431 < baseStart_909431 := by decide
  rcases family_descends (prefixWord ++ tailWord_909431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909441 : List Nat := [1, 2, 4, 2, 4, 1, 1, 5]
def baseStart_909441 : Nat := 118140960795 + 909441 * 2 ^ 59
def prefixEnd_909441 : Nat := 4983230072969 + 3 ^ 40 * 909441 * 2
def baseEnd_909441 : Nat := 138364551083164901216315

theorem tailTrace_909441 : CollatzResearch.WordTrace tailWord_909441 prefixEnd_909441 138364551083164901216315 := by
  unfold tailWord_909441
  simp only [CollatzResearch.WordTrace]
  refine ⟨33170038298258052002240177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22113358865505368001493451 33170038298258052002240177)
  ·
    refine ⟨24877528723693539001680133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33170038298258052002240177 24877528723693539001680133)
    ·
      refine ⟨4664536635692538562815025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24877528723693539001680133 4664536635692538562815025)
      ·
        refine ⟨3498402476769403922111269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4664536635692538562815025 3498402476769403922111269)
        ·
          refine ⟨655950464394263235395863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3498402476769403922111269 655950464394263235395863)
          ·
            refine ⟨983925696591394853093795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 655950464394263235395863 983925696591394853093795)
            ·
              refine ⟨1475888544887092279640693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 983925696591394853093795 1475888544887092279640693)
              ·
                refine ⟨138364551083164901216315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1475888544887092279640693 138364551083164901216315)
                ·
                  rfl

theorem cell20_909441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 1, 5].length) (baseStart_909441 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_909441 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_909441 prefixEnd_909441 := by exact prefixLift 909441
  have htrace : WordTrace (prefixWord ++ tailWord_909441) baseStart_909441 baseEnd_909441 := by
    simpa [prefixWord, tailWord_909441, baseEnd_909441] using wordTrace_append hprefix tailTrace_909441
  have hstable : (prefixWord ++ tailWord_909441).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909441).length < 2 ^ (prefixWord ++ tailWord_909441).sum := by decide
  have hdescent : baseEnd_909441 < baseStart_909441 := by decide
  rcases family_descends (prefixWord ++ tailWord_909441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909445 : List Nat := [1, 3, 1, 1, 5, 1, 3, 5]
def baseStart_909445 : Nat := 118140960795 + 909445 * 2 ^ 59
def prefixEnd_909445 : Nat := 4983230072969 + 3 ^ 40 * 909445 * 2
def baseEnd_909445 : Nat := 138365159652829489171865

theorem tailTrace_909445 : CollatzResearch.WordTrace tailWord_909445 prefixEnd_909445 138365159652829489171865 := by
  unfold tailWord_909445
  simp only [CollatzResearch.WordTrace]
  refine ⟨33170184190243560685385789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22113456126829040456923859 33170184190243560685385789)
  ·
    refine ⟨12438819071341335257019671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33170184190243560685385789 12438819071341335257019671)
    ·
      refine ⟨18658228607012002885529507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12438819071341335257019671 18658228607012002885529507)
      ·
        refine ⟨27987342910518004328294261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18658228607012002885529507 27987342910518004328294261)
        ·
          refine ⟨2623813397861062905777587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27987342910518004328294261 2623813397861062905777587)
          ·
            refine ⟨3935720096791594358666381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2623813397861062905777587 3935720096791594358666381)
            ·
              refine ⟨1475895036296847884499893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3935720096791594358666381 1475895036296847884499893)
              ·
                refine ⟨138365159652829489171865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1475895036296847884499893 138365159652829489171865)
                ·
                  rfl

theorem cell20_909445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 3, 5].length) (baseStart_909445 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_909445 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_909445 prefixEnd_909445 := by exact prefixLift 909445
  have htrace : WordTrace (prefixWord ++ tailWord_909445) baseStart_909445 baseEnd_909445 := by
    simpa [prefixWord, tailWord_909445, baseEnd_909445] using wordTrace_append hprefix tailTrace_909445
  have hstable : (prefixWord ++ tailWord_909445).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909445).length < 2 ^ (prefixWord ++ tailWord_909445).sum := by decide
  have hdescent : baseEnd_909445 < baseStart_909445 := by decide
  rcases family_descends (prefixWord ++ tailWord_909445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909482 : List Nat := [3, 1, 5, 1, 3, 1, 1, 2, 3]
def baseStart_909482 : Nat := 118140960795 + 909482 * 2 ^ 59
def prefixEnd_909482 : Nat := 4983230072969 + 3 ^ 40 * 909482 * 2
def baseEnd_909482 : Nat := 415112366766680783282111

theorem tailTrace_909482 : CollatzResearch.WordTrace tailWord_909482 prefixEnd_909482 415112366766680783282111 := by
  unfold tailWord_909482
  simp only [CollatzResearch.WordTrace]
  refine ⟨8292883422777379001120675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22114355794073010669655133 8292883422777379001120675)
  ·
    refine ⟨12439325134166068501681013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8292883422777379001120675 12439325134166068501681013)
    ·
      refine ⟨1166186731328068922032595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12439325134166068501681013 1166186731328068922032595)
      ·
        refine ⟨1749280096992103383048893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1166186731328068922032595 1749280096992103383048893)
        ·
          refine ⟨655980036372038768643335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1749280096992103383048893 655980036372038768643335)
          ·
            refine ⟨983970054558058152965003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 655980036372038768643335 983970054558058152965003)
            ·
              refine ⟨1475955081837087229447505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 983970054558058152965003 1475955081837087229447505)
              ·
                refine ⟨1106966311377815422085629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1475955081837087229447505 1106966311377815422085629)
                ·
                  refine ⟨415112366766680783282111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1106966311377815422085629 415112366766680783282111)
                  ·
                    rfl

theorem cell20_909482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 1, 2, 3].length) (baseStart_909482 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_909482 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_909482 prefixEnd_909482 := by exact prefixLift 909482
  have htrace : WordTrace (prefixWord ++ tailWord_909482) baseStart_909482 baseEnd_909482 := by
    simpa [prefixWord, tailWord_909482, baseEnd_909482] using wordTrace_append hprefix tailTrace_909482
  have hstable : (prefixWord ++ tailWord_909482).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909482).length < 2 ^ (prefixWord ++ tailWord_909482).sum := by decide
  have hdescent : baseEnd_909482 < baseStart_909482 := by decide
  rcases family_descends (prefixWord ++ tailWord_909482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909490 : List Nat := [3, 2, 1, 1, 1, 3, 3, 1, 5]
def baseStart_909490 : Nat := 118140960795 + 909490 * 2 ^ 59
def prefixEnd_909490 : Nat := 4983230072969 + 3 ^ 40 * 909490 * 2
def baseEnd_909490 : Nat := 415116018184668311015411

theorem tailTrace_909490 : CollatzResearch.WordTrace tailWord_909490 prefixEnd_909490 415116018184668311015411 := by
  unfold tailWord_909490
  simp only [CollatzResearch.WordTrace]
  refine ⟨8292956368770133342693481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22114550316720355580515949 8292956368770133342693481)
  ·
    refine ⟨6219717276577600007020111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8292956368770133342693481 6219717276577600007020111)
    ·
      refine ⟨9329575914866400010530167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6219717276577600007020111 9329575914866400010530167)
      ·
        refine ⟨13994363872299600015795251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9329575914866400010530167 13994363872299600015795251)
        ·
          refine ⟨20991545808449400023692877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13994363872299600015795251 20991545808449400023692877)
          ·
            refine ⟨7871829678168525008884829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20991545808449400023692877 7871829678168525008884829)
            ·
              refine ⟨2951936129313196878331811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7871829678168525008884829 2951936129313196878331811)
              ·
                refine ⟨4427904193969795317497717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2951936129313196878331811 4427904193969795317497717)
                ·
                  refine ⟨415116018184668311015411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4427904193969795317497717 415116018184668311015411)
                  ·
                    rfl

theorem cell20_909490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 1, 5].length) (baseStart_909490 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_909490 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_909490 prefixEnd_909490 := by exact prefixLift 909490
  have htrace : WordTrace (prefixWord ++ tailWord_909490) baseStart_909490 baseEnd_909490 := by
    simpa [prefixWord, tailWord_909490, baseEnd_909490] using wordTrace_append hprefix tailTrace_909490
  have hstable : (prefixWord ++ tailWord_909490).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909490).length < 2 ^ (prefixWord ++ tailWord_909490).sum := by decide
  have hdescent : baseEnd_909490 < baseStart_909490 := by decide
  rcases family_descends (prefixWord ++ tailWord_909490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909521 : List Nat := [1, 2, 2, 1, 2, 2, 6, 4]
def baseStart_909521 : Nat := 118140960795 + 909521 * 2 ^ 59
def prefixEnd_909521 : Nat := 4983230072969 + 3 ^ 40 * 909521 * 2
def baseEnd_909521 : Nat := 138376722476456660327317

theorem tailTrace_909521 : CollatzResearch.WordTrace tailWord_909521 prefixEnd_909521 138376722476456660327317 := by
  unfold tailWord_909521
  simp only [CollatzResearch.WordTrace]
  refine ⟨33172956137968225665152417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22115304091978817110101611 33172956137968225665152417)
  ·
    refine ⟨24879717103476169248864313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33172956137968225665152417 24879717103476169248864313)
    ·
      refine ⟨18659787827607126936648235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24879717103476169248864313 18659787827607126936648235)
      ·
        refine ⟨27989681741410690404972353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18659787827607126936648235 27989681741410690404972353)
        ·
          refine ⟨20992261306058017803729265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27989681741410690404972353 20992261306058017803729265)
          ·
            refine ⟨15744195979543513352796949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20992261306058017803729265 15744195979543513352796949)
            ·
              refine ⟨738009186541102188412357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 15744195979543513352796949 738009186541102188412357)
              ·
                refine ⟨138376722476456660327317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 738009186541102188412357 138376722476456660327317)
                ·
                  rfl

theorem cell20_909521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 6, 4].length) (baseStart_909521 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_909521 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_909521 prefixEnd_909521 := by exact prefixLift 909521
  have htrace : WordTrace (prefixWord ++ tailWord_909521) baseStart_909521 baseEnd_909521 := by
    simpa [prefixWord, tailWord_909521, baseEnd_909521] using wordTrace_append hprefix tailTrace_909521
  have hstable : (prefixWord ++ tailWord_909521).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909521).length < 2 ^ (prefixWord ++ tailWord_909521).sum := by decide
  have hdescent : baseEnd_909521 < baseStart_909521 := by decide
  rcases family_descends (prefixWord ++ tailWord_909521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909528 : List Nat := [2, 1, 2, 2, 4, 1, 1, 2, 5]
def baseStart_909528 : Nat := 118140960795 + 909528 * 2 ^ 59
def prefixEnd_909528 : Nat := 4983230072969 + 3 ^ 40 * 909528 * 2
def baseEnd_909528 : Nat := 415133362420109067748589

theorem tailTrace_909528 : CollatzResearch.WordTrace tailWord_909528 prefixEnd_909528 415133362420109067748589 := by
  unfold tailWord_909528
  simp only [CollatzResearch.WordTrace]
  refine ⟨16586605724471432930328619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22115474299295243907104825 16586605724471432930328619)
  ·
    refine ⟨24879908586707149395492929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16586605724471432930328619 24879908586707149395492929)
    ·
      refine ⟨18659931440030362046619697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24879908586707149395492929 18659931440030362046619697)
      ·
        refine ⟨13994948580022771534964773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18659931440030362046619697 13994948580022771534964773)
        ·
          refine ⟨2624052858754269662805895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13994948580022771534964773 2624052858754269662805895)
          ·
            refine ⟨3936079288131404494208843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2624052858754269662805895 3936079288131404494208843)
            ·
              refine ⟨5904118932197106741313265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3936079288131404494208843 5904118932197106741313265)
              ·
                refine ⟨4428089199147830055984949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5904118932197106741313265 4428089199147830055984949)
                ·
                  refine ⟨415133362420109067748589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4428089199147830055984949 415133362420109067748589)
                  ·
                    rfl

theorem cell20_909528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 2, 5].length) (baseStart_909528 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_909528 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_909528 prefixEnd_909528 := by exact prefixLift 909528
  have htrace : WordTrace (prefixWord ++ tailWord_909528) baseStart_909528 baseEnd_909528 := by
    simpa [prefixWord, tailWord_909528, baseEnd_909528] using wordTrace_append hprefix tailTrace_909528
  have hstable : (prefixWord ++ tailWord_909528).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909528).length < 2 ^ (prefixWord ++ tailWord_909528).sum := by decide
  have hdescent : baseEnd_909528 < baseStart_909528 := by decide
  rcases family_descends (prefixWord ++ tailWord_909528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909552 : List Nat := [2, 1, 1, 1, 3, 1, 1, 8, 2]
def baseStart_909552 : Nat := 118140960795 + 909552 * 2 ^ 59
def prefixEnd_909552 : Nat := 4983230072969 + 3 ^ 40 * 909552 * 2
def baseEnd_909552 : Nat := 415144316674071650948491

theorem tailTrace_909552 : CollatzResearch.WordTrace tailWord_909552 prefixEnd_909552 415144316674071650948491 := by
  unfold tailWord_909552
  simp only [CollatzResearch.WordTrace]
  refine ⟨16587043400427958979765455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22116057867237278639687273 16587043400427958979765455)
  ·
    refine ⟨24880565100641938469648183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16587043400427958979765455 24880565100641938469648183)
    ·
      refine ⟨37320847650962907704472275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24880565100641938469648183 37320847650962907704472275)
      ·
        refine ⟨55981271476444361556708413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37320847650962907704472275 55981271476444361556708413)
        ·
          refine ⟨20992976803666635583765655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55981271476444361556708413 20992976803666635583765655)
          ·
            refine ⟨31489465205499953375648483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20992976803666635583765655 31489465205499953375648483)
            ·
              refine ⟨47234197808249930063472725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31489465205499953375648483 47234197808249930063472725)
              ·
                refine ⟨553525755565428867931321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 47234197808249930063472725 553525755565428867931321)
                ·
                  refine ⟨415144316674071650948491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 553525755565428867931321 415144316674071650948491)
                  ·
                    rfl

theorem cell20_909552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 8, 2].length) (baseStart_909552 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_909552 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_909552 prefixEnd_909552 := by exact prefixLift 909552
  have htrace : WordTrace (prefixWord ++ tailWord_909552) baseStart_909552 baseEnd_909552 := by
    simpa [prefixWord, tailWord_909552, baseEnd_909552] using wordTrace_append hprefix tailTrace_909552
  have hstable : (prefixWord ++ tailWord_909552).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909552).length < 2 ^ (prefixWord ++ tailWord_909552).sum := by decide
  have hdescent : baseEnd_909552 < baseStart_909552 := by decide
  rcases family_descends (prefixWord ++ tailWord_909552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909562 : List Nat := [3, 1, 1, 1, 1, 7, 2, 1, 3]
def baseStart_909562 : Nat := 118140960795 + 909562 * 2 ^ 59
def prefixEnd_909562 : Nat := 4983230072969 + 3 ^ 40 * 909562 * 2
def baseEnd_909562 : Nat := 415148880946556060615117

theorem tailTrace_909562 : CollatzResearch.WordTrace tailWord_909562 prefixEnd_909562 415148880946556060615117 := by
  unfold tailWord_909562
  simp only [CollatzResearch.WordTrace]
  refine ⟨8293612882704922416848735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22116301020546459778263293 8293612882704922416848735)
  ·
    refine ⟨12440419324057383625273103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8293612882704922416848735 12440419324057383625273103)
    ·
      refine ⟨18660628986086075437909655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12440419324057383625273103 18660628986086075437909655)
      ·
        refine ⟨27990943479129113156864483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18660628986086075437909655 27990943479129113156864483)
        ·
          refine ⟨41986415218693669735296725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27990943479129113156864483 41986415218693669735296725)
          ·
            refine ⟨984056606688132884421017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 41986415218693669735296725 984056606688132884421017)
            ·
              refine ⟨738042455016099663315763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 984056606688132884421017 738042455016099663315763)
              ·
                refine ⟨1107063682524149494973645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 738042455016099663315763 1107063682524149494973645)
                ·
                  refine ⟨415148880946556060615117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1107063682524149494973645 415148880946556060615117)
                  ·
                    rfl

theorem cell20_909562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 2, 1, 3].length) (baseStart_909562 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_909562 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_909562 prefixEnd_909562 := by exact prefixLift 909562
  have htrace : WordTrace (prefixWord ++ tailWord_909562) baseStart_909562 baseEnd_909562 := by
    simpa [prefixWord, tailWord_909562, baseEnd_909562] using wordTrace_append hprefix tailTrace_909562
  have hstable : (prefixWord ++ tailWord_909562).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909562).length < 2 ^ (prefixWord ++ tailWord_909562).sum := by decide
  have hdescent : baseEnd_909562 < baseStart_909562 := by decide
  rcases family_descends (prefixWord ++ tailWord_909562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909580 : List Nat := [2, 2, 1, 2, 2, 2, 1, 8]
def baseStart_909580 : Nat := 118140960795 + 909580 * 2 ^ 59
def prefixEnd_909580 : Nat := 4983230072969 + 3 ^ 40 * 909580 * 2
def baseEnd_909580 : Nat := 138385698879009332671681

theorem tailTrace_909580 : CollatzResearch.WordTrace tailWord_909580 prefixEnd_909580 138385698879009332671681 := by
  unfold tailWord_909580
  simp only [CollatzResearch.WordTrace]
  refine ⟨16587554022377239370775097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22116738696502985827700129 16587554022377239370775097)
  ·
    refine ⟨12440665516782929528081323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16587554022377239370775097 12440665516782929528081323)
    ·
      refine ⟨18660998275174394292121985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12440665516782929528081323 18660998275174394292121985)
      ·
        refine ⟨13995748706380795719091489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18660998275174394292121985 13995748706380795719091489)
        ·
          refine ⟨10496811529785596789318617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13995748706380795719091489 10496811529785596789318617)
          ·
            refine ⟨7872608647339197591988963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10496811529785596789318617 7872608647339197591988963)
            ·
              refine ⟨11808912971008796387983445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7872608647339197591988963 11808912971008796387983445)
              ·
                refine ⟨138385698879009332671681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11808912971008796387983445 138385698879009332671681)
                ·
                  rfl

theorem cell20_909580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 8].length) (baseStart_909580 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_909580 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_909580 prefixEnd_909580 := by exact prefixLift 909580
  have htrace : WordTrace (prefixWord ++ tailWord_909580) baseStart_909580 baseEnd_909580 := by
    simpa [prefixWord, tailWord_909580, baseEnd_909580] using wordTrace_append hprefix tailTrace_909580
  have hstable : (prefixWord ++ tailWord_909580).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909580).length < 2 ^ (prefixWord ++ tailWord_909580).sum := by decide
  have hdescent : baseEnd_909580 < baseStart_909580 := by decide
  rcases family_descends (prefixWord ++ tailWord_909580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909587 : List Nat := [1, 1, 1, 2, 1, 3, 1, 3, 7]
def baseStart_909587 : Nat := 118140960795 + 909587 * 2 ^ 59
def prefixEnd_909587 : Nat := 4983230072969 + 3 ^ 40 * 909587 * 2
def baseEnd_909587 : Nat := 415160291627767084781681

theorem tailTrace_909587 : CollatzResearch.WordTrace tailWord_909587 prefixEnd_909587 415160291627767084781681 := by
  unfold tailWord_909587
  simp only [CollatzResearch.WordTrace]
  refine ⟨33175363355729118937055015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22116908903819412624703343 33175363355729118937055015)
  ·
    refine ⟨49763045033593678405582523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33175363355729118937055015 49763045033593678405582523)
    ·
      refine ⟨74644567550390517608373785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49763045033593678405582523 74644567550390517608373785)
      ·
        refine ⟨55983425662792888206280339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74644567550390517608373785 55983425662792888206280339)
        ·
          refine ⟨83975138494189332309420509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55983425662792888206280339 83975138494189332309420509)
          ·
            refine ⟨31490676935320999616032691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 83975138494189332309420509 31490676935320999616032691)
            ·
              refine ⟨47236015402981499424049037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31490676935320999616032691 47236015402981499424049037)
              ·
                refine ⟨17713505776118062284018389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47236015402981499424049037 17713505776118062284018389)
                ·
                  refine ⟨415160291627767084781681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17713505776118062284018389 415160291627767084781681)
                  ·
                    rfl

theorem cell20_909587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 3, 7].length) (baseStart_909587 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_909587 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_909587 prefixEnd_909587 := by exact prefixLift 909587
  have htrace : WordTrace (prefixWord ++ tailWord_909587) baseStart_909587 baseEnd_909587 := by
    simpa [prefixWord, tailWord_909587, baseEnd_909587] using wordTrace_append hprefix tailTrace_909587
  have hstable : (prefixWord ++ tailWord_909587).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909587).length < 2 ^ (prefixWord ++ tailWord_909587).sum := by decide
  have hdescent : baseEnd_909587 < baseStart_909587 := by decide
  rcases family_descends (prefixWord ++ tailWord_909587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909597 : List Nat := [1, 4, 2, 3, 2, 8]
def baseStart_909597 : Nat := 118140960795 + 909597 * 2 ^ 59
def prefixEnd_909597 : Nat := 4983230072969 + 3 ^ 40 * 909597 * 2
def baseEnd_909597 : Nat := 15376476144453759053641

theorem tailTrace_909597 : CollatzResearch.WordTrace tailWord_909597 prefixEnd_909597 15376476144453759053641 := by
  unfold tailWord_909597
  simp only [CollatzResearch.WordTrace]
  refine ⟨33175728085692890644919045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22117152057128593763279363 33175728085692890644919045)
  ·
    refine ⟨6220449016067416995922321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33175728085692890644919045 6220449016067416995922321)
    ·
      refine ⟨4665336762050562746941741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6220449016067416995922321 4665336762050562746941741)
      ·
        refine ⟨1749501285768961030103153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4665336762050562746941741 1749501285768961030103153)
        ·
          refine ⟨1312125964326720772577365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1749501285768961030103153 1312125964326720772577365)
          ·
            refine ⟨15376476144453759053641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1312125964326720772577365 15376476144453759053641)
            ·
              rfl

theorem cell20_909597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 8].length) (baseStart_909597 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_909597 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_909597 prefixEnd_909597 := by exact prefixLift 909597
  have htrace : WordTrace (prefixWord ++ tailWord_909597) baseStart_909597 baseEnd_909597 := by
    simpa [prefixWord, tailWord_909597, baseEnd_909597] using wordTrace_append hprefix tailTrace_909597
  have hstable : (prefixWord ++ tailWord_909597).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909597).length < 2 ^ (prefixWord ++ tailWord_909597).sum := by decide
  have hdescent : baseEnd_909597 < baseStart_909597 := by decide
  rcases family_descends (prefixWord ++ tailWord_909597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909666 : List Nat := [3, 3, 2, 1, 1, 2, 1, 3, 4]
def baseStart_909666 : Nat := 118140960795 + 909666 * 2 ^ 59
def prefixEnd_909666 : Nat := 4983230072969 + 3 ^ 40 * 909666 * 2
def baseEnd_909666 : Nat := 415196349380393921148025

theorem tailTrace_909666 : CollatzResearch.WordTrace tailWord_909666 prefixEnd_909666 415196349380393921148025 := by
  unfold tailWord_909666
  simp only [CollatzResearch.WordTrace]
  refine ⟨8294561180610728857295213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22118829814961943619453901 8294561180610728857295213)
  ·
    refine ⟨3110460442729023321485705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8294561180610728857295213 3110460442729023321485705)
    ·
      refine ⟨2332845332046767491114279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3110460442729023321485705 2332845332046767491114279)
      ·
        refine ⟨3499267998070151236671419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2332845332046767491114279 3499267998070151236671419)
        ·
          refine ⟨5248901997105226855007129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3499267998070151236671419 5248901997105226855007129)
          ·
            refine ⟨3936676497828920141255347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5248901997105226855007129 3936676497828920141255347)
            ·
              refine ⟨5905014746743380211883021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3936676497828920141255347 5905014746743380211883021)
              ·
                refine ⟨2214380530028767579456133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5905014746743380211883021 2214380530028767579456133)
                ·
                  refine ⟨415196349380393921148025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2214380530028767579456133 415196349380393921148025)
                  ·
                    rfl

theorem cell20_909666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_909666 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_909666 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_909666 prefixEnd_909666 := by exact prefixLift 909666
  have htrace : WordTrace (prefixWord ++ tailWord_909666) baseStart_909666 baseEnd_909666 := by
    simpa [prefixWord, tailWord_909666, baseEnd_909666] using wordTrace_append hprefix tailTrace_909666
  have hstable : (prefixWord ++ tailWord_909666).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909666).length < 2 ^ (prefixWord ++ tailWord_909666).sum := by decide
  have hdescent : baseEnd_909666 < baseStart_909666 := by decide
  rcases family_descends (prefixWord ++ tailWord_909666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909676 : List Nat := [2, 2, 1, 1, 6, 1, 3, 1, 3]
def baseStart_909676 : Nat := 118140960795 + 909676 * 2 ^ 59
def prefixEnd_909676 : Nat := 4983230072969 + 3 ^ 40 * 909676 * 2
def baseEnd_909676 : Nat := 415200913652878330814651

theorem tailTrace_909676 : CollatzResearch.WordTrace tailWord_909676 prefixEnd_909676 415200913652878330814651 := by
  unfold tailWord_909676
  simp only [CollatzResearch.WordTrace]
  refine ⟨16589304726203343568522441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22119072968271124758029921 16589304726203343568522441)
  ·
    refine ⟨12441978544652507676391831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16589304726203343568522441 12441978544652507676391831)
    ·
      refine ⟨18662967816978761514587747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12441978544652507676391831 18662967816978761514587747)
      ·
        refine ⟨27994451725468142271881621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18662967816978761514587747 27994451725468142271881621)
        ·
          refine ⟨1312239924631319168994451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 27994451725468142271881621 1312239924631319168994451)
          ·
            refine ⟨1968359886946978753491677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1312239924631319168994451 1968359886946978753491677)
            ·
              refine ⟨738134957605117032559379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1968359886946978753491677 738134957605117032559379)
              ·
                refine ⟨1107202436407675548839069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 738134957605117032559379 1107202436407675548839069)
                ·
                  refine ⟨415200913652878330814651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1107202436407675548839069 415200913652878330814651)
                  ·
                    rfl

theorem cell20_909676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 3].length) (baseStart_909676 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_909676 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_909676 prefixEnd_909676 := by exact prefixLift 909676
  have htrace : WordTrace (prefixWord ++ tailWord_909676) baseStart_909676 baseEnd_909676 := by
    simpa [prefixWord, tailWord_909676, baseEnd_909676] using wordTrace_append hprefix tailTrace_909676
  have hstable : (prefixWord ++ tailWord_909676).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909676).length < 2 ^ (prefixWord ++ tailWord_909676).sum := by decide
  have hdescent : baseEnd_909676 < baseStart_909676 := by decide
  rcases family_descends (prefixWord ++ tailWord_909676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909686 : List Nat := [5, 1, 1, 4, 1, 2, 2, 4]
def baseStart_909686 : Nat := 118140960795 + 909686 * 2 ^ 59
def prefixEnd_909686 : Nat := 4983230072969 + 3 ^ 40 * 909686 * 2
def baseEnd_909686 : Nat := 138401825975120913493759

theorem tailTrace_909686 : CollatzResearch.WordTrace tailWord_909686 prefixEnd_909686 138401825975120913493759 := by
  unfold tailWord_909686
  simp only [CollatzResearch.WordTrace]
  refine ⟨2073685886398153677806807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22119316121580305896605941 2073685886398153677806807)
  ·
    refine ⟨3110528829597230516710211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2073685886398153677806807 3110528829597230516710211)
    ·
      refine ⟨4665793244395845775065317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3110528829597230516710211 4665793244395845775065317)
      ·
        refine ⟨874836233324221082824747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4665793244395845775065317 874836233324221082824747)
        ·
          refine ⟨1312254349986331624237121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 874836233324221082824747 1312254349986331624237121)
          ·
            refine ⟨984190762489748718177841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1312254349986331624237121 984190762489748718177841)
            ·
              refine ⟨738143071867311538633381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 984190762489748718177841 738143071867311538633381)
              ·
                refine ⟨138401825975120913493759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 738143071867311538633381 138401825975120913493759)
                ·
                  rfl

theorem cell20_909686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 2, 4].length) (baseStart_909686 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_909686 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_909686 prefixEnd_909686 := by exact prefixLift 909686
  have htrace : WordTrace (prefixWord ++ tailWord_909686) baseStart_909686 baseEnd_909686 := by
    simpa [prefixWord, tailWord_909686, baseEnd_909686] using wordTrace_append hprefix tailTrace_909686
  have hstable : (prefixWord ++ tailWord_909686).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909686).length < 2 ^ (prefixWord ++ tailWord_909686).sum := by decide
  have hdescent : baseEnd_909686 < baseStart_909686 := by decide
  rcases family_descends (prefixWord ++ tailWord_909686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909721 : List Nat := [1, 2, 1, 2, 1, 4, 5, 2, 2]
def baseStart_909721 : Nat := 118140960795 + 909721 * 2 ^ 59
def prefixEnd_909721 : Nat := 4983230072969 + 3 ^ 40 * 909721 * 2
def baseEnd_909721 : Nat := 415221452879058174314467

theorem tailTrace_909721 : CollatzResearch.WordTrace tailWord_909721 prefixEnd_909721 415221452879058174314467 := by
  unfold tailWord_909721
  simp only [CollatzResearch.WordTrace]
  refine ⟨33180250737243659822433017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22120167158162439881622011 33180250737243659822433017)
  ·
    refine ⟨24885188052932744866824763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33180250737243659822433017 24885188052932744866824763)
    ·
      refine ⟨37327782079399117300237145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24885188052932744866824763 37327782079399117300237145)
      ·
        refine ⟨27995836559549337975177859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37327782079399117300237145 27995836559549337975177859)
        ·
          refine ⟨41993754839324006962766789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27995836559549337975177859 41993754839324006962766789)
          ·
            refine ⟨7873829032373251305518773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41993754839324006962766789 7873829032373251305518773)
            ·
              refine ⟨738171471784992309892385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7873829032373251305518773 738171471784992309892385)
              ·
                refine ⟨553628603838744232419289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 738171471784992309892385 553628603838744232419289)
                ·
                  refine ⟨415221452879058174314467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 553628603838744232419289 415221452879058174314467)
                  ·
                    rfl

theorem cell20_909721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 5, 2, 2].length) (baseStart_909721 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_909721 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_909721 prefixEnd_909721 := by exact prefixLift 909721
  have htrace : WordTrace (prefixWord ++ tailWord_909721) baseStart_909721 baseEnd_909721 := by
    simpa [prefixWord, tailWord_909721, baseEnd_909721] using wordTrace_append hprefix tailTrace_909721
  have hstable : (prefixWord ++ tailWord_909721).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909721).length < 2 ^ (prefixWord ++ tailWord_909721).sum := by decide
  have hdescent : baseEnd_909721 < baseStart_909721 := by decide
  rcases family_descends (prefixWord ++ tailWord_909721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909732 : List Nat := [2, 3, 1, 2, 1, 1, 3, 7]
def baseStart_909732 : Nat := 118140960795 + 909732 * 2 ^ 59
def prefixEnd_909732 : Nat := 4983230072969 + 3 ^ 40 * 909732 * 2
def baseEnd_909732 : Nat := 138408824526263674982585

theorem tailTrace_909732 : CollatzResearch.WordTrace tailWord_909732 prefixEnd_909732 138408824526263674982585 := by
  unfold tailWord_909732
  simp only [CollatzResearch.WordTrace]
  refine ⟨16590325970101904350541725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22120434626802539134055633 16590325970101904350541725)
  ·
    refine ⟨6221372238788214131453147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16590325970101904350541725 6221372238788214131453147)
    ·
      refine ⟨9332058358182321197179721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6221372238788214131453147 9332058358182321197179721)
      ·
        refine ⟨6999043768636740897884791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9332058358182321197179721 6999043768636740897884791)
        ·
          refine ⟨10498565652955111346827187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6999043768636740897884791 10498565652955111346827187)
          ·
            refine ⟨15747848479432667020240781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10498565652955111346827187 15747848479432667020240781)
            ·
              refine ⟨5905443179787250132590293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15747848479432667020240781 5905443179787250132590293)
              ·
                refine ⟨138408824526263674982585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5905443179787250132590293 138408824526263674982585)
                ·
                  rfl

theorem cell20_909732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 7].length) (baseStart_909732 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_909732 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_909732 prefixEnd_909732 := by exact prefixLift 909732
  have htrace : WordTrace (prefixWord ++ tailWord_909732) baseStart_909732 baseEnd_909732 := by
    simpa [prefixWord, tailWord_909732, baseEnd_909732] using wordTrace_append hprefix tailTrace_909732
  have hstable : (prefixWord ++ tailWord_909732).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909732).length < 2 ^ (prefixWord ++ tailWord_909732).sum := by decide
  have hdescent : baseEnd_909732 < baseStart_909732 := by decide
  rcases family_descends (prefixWord ++ tailWord_909732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909735 : List Nat := [1, 1, 6, 1, 1, 3, 1, 3, 3]
def baseStart_909735 : Nat := 118140960795 + 909735 * 2 ^ 59
def prefixEnd_909735 : Nat := 4983230072969 + 3 ^ 40 * 909735 * 2
def baseEnd_909735 : Nat := 415227842860536347847743

theorem tailTrace_909735 : CollatzResearch.WordTrace tailWord_909735 prefixEnd_909735 415227842860536347847743 := by
  unfold tailWord_909735
  simp only [CollatzResearch.WordTrace]
  refine ⟨33180761359192940213442659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22120507572795293475628439 33180761359192940213442659)
  ·
    refine ⟨49771142038789410320163989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33180761359192940213442659 49771142038789410320163989)
    ·
      refine ⟨2333022283068253608757687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 49771142038789410320163989 2333022283068253608757687)
      ·
        refine ⟨3499533424602380413136531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2333022283068253608757687 3499533424602380413136531)
        ·
          refine ⟨5249300136903570619704797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3499533424602380413136531 5249300136903570619704797)
          ·
            refine ⟨1968487551338838982389299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5249300136903570619704797 1968487551338838982389299)
            ·
              refine ⟨2952731327008258473583949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1968487551338838982389299 2952731327008258473583949)
              ·
                refine ⟨1107274247628096927593981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2952731327008258473583949 1107274247628096927593981)
                ·
                  refine ⟨415227842860536347847743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1107274247628096927593981 415227842860536347847743)
                  ·
                    rfl

theorem cell20_909735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 3, 3].length) (baseStart_909735 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_909735 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_909735 prefixEnd_909735 := by exact prefixLift 909735
  have htrace : WordTrace (prefixWord ++ tailWord_909735) baseStart_909735 baseEnd_909735 := by
    simpa [prefixWord, tailWord_909735, baseEnd_909735] using wordTrace_append hprefix tailTrace_909735
  have hstable : (prefixWord ++ tailWord_909735).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909735).length < 2 ^ (prefixWord ++ tailWord_909735).sum := by decide
  have hdescent : baseEnd_909735 < baseStart_909735 := by decide
  rcases family_descends (prefixWord ++ tailWord_909735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909777 : List Nat := [1, 2, 2, 1, 2, 1, 1, 5, 5]
def baseStart_909777 : Nat := 118140960795 + 909777 * 2 ^ 59
def prefixEnd_909777 : Nat := 4983230072969 + 3 ^ 40 * 909777 * 2
def baseEnd_909777 : Nat := 415247012804970868447571

theorem tailTrace_909777 : CollatzResearch.WordTrace tailWord_909777 prefixEnd_909777 415247012804970868447571 := by
  unfold tailWord_909777
  simp only [CollatzResearch.WordTrace]
  refine ⟨33182293225040781386471585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22121528816693854257647723 33182293225040781386471585)
  ·
    refine ⟨24886719918780586039853689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33182293225040781386471585 24886719918780586039853689)
    ·
      refine ⟨18665039939085439529890267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24886719918780586039853689 18665039939085439529890267)
      ·
        refine ⟨27997559908628159294835401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18665039939085439529890267 27997559908628159294835401)
        ·
          refine ⟨20998169931471119471126551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27997559908628159294835401 20998169931471119471126551)
          ·
            refine ⟨31497254897206679206689827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20998169931471119471126551 31497254897206679206689827)
            ·
              refine ⟨47245882345810018810034741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31497254897206679206689827 47245882345810018810034741)
              ·
                refine ⟨4429301469919689263440757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47245882345810018810034741 4429301469919689263440757)
                ·
                  refine ⟨415247012804970868447571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4429301469919689263440757 415247012804970868447571)
                  ·
                    rfl

theorem cell20_909777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 5, 5].length) (baseStart_909777 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_909777 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_909777 prefixEnd_909777 := by exact prefixLift 909777
  have htrace : WordTrace (prefixWord ++ tailWord_909777) baseStart_909777 baseEnd_909777 := by
    simpa [prefixWord, tailWord_909777, baseEnd_909777] using wordTrace_append hprefix tailTrace_909777
  have hstable : (prefixWord ++ tailWord_909777).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909777).length < 2 ^ (prefixWord ++ tailWord_909777).sum := by decide
  have hdescent : baseEnd_909777 < baseStart_909777 := by decide
  rcases family_descends (prefixWord ++ tailWord_909777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909828 : List Nat := [2, 3, 2, 3, 1, 3, 1, 2, 3]
def baseStart_909828 : Nat := 118140960795 + 909828 * 2 ^ 59
def prefixEnd_909828 : Nat := 4983230072969 + 3 ^ 40 * 909828 * 2
def baseEnd_909828 : Nat := 415270290594641357747363

theorem tailTrace_909828 : CollatzResearch.WordTrace tailWord_909828 prefixEnd_909828 415270290594641357747363 := by
  unfold tailWord_909828
  simp only [CollatzResearch.WordTrace]
  refine ⟨16592076673928008548289069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22122768898570678064385425 16592076673928008548289069)
  ·
    refine ⟨6222028752723003205608401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16592076673928008548289069 6222028752723003205608401)
    ·
      refine ⟨4666521564542252404206301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6222028752723003205608401 4666521564542252404206301)
      ·
        refine ⟨1749945586703344651577363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4666521564542252404206301 1749945586703344651577363)
        ·
          refine ⟨2624918380055016977366045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1749945586703344651577363 2624918380055016977366045)
          ·
            refine ⟨984344392520631366512267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2624918380055016977366045 984344392520631366512267)
            ·
              refine ⟨1476516588780947049768401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 984344392520631366512267 1476516588780947049768401)
              ·
                refine ⟨1107387441585710287326301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1476516588780947049768401 1107387441585710287326301)
                ·
                  refine ⟨415270290594641357747363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1107387441585710287326301 415270290594641357747363)
                  ·
                    rfl

theorem cell20_909828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 1, 2, 3].length) (baseStart_909828 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_909828 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_909828 prefixEnd_909828 := by exact prefixLift 909828
  have htrace : WordTrace (prefixWord ++ tailWord_909828) baseStart_909828 baseEnd_909828 := by
    simpa [prefixWord, tailWord_909828, baseEnd_909828] using wordTrace_append hprefix tailTrace_909828
  have hstable : (prefixWord ++ tailWord_909828).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909828).length < 2 ^ (prefixWord ++ tailWord_909828).sum := by decide
  have hdescent : baseEnd_909828 < baseStart_909828 := by decide
  rcases family_descends (prefixWord ++ tailWord_909828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909884 : List Nat := [2, 2, 2, 2, 3, 1, 8]
def baseStart_909884 : Nat := 118140960795 + 909884 * 2 ^ 59
def prefixEnd_909884 : Nat := 4983230072969 + 3 ^ 40 * 909884 * 2
def baseEnd_909884 : Nat := 46143983391172672431163

theorem tailTrace_909884 : CollatzResearch.WordTrace tailWord_909884 prefixEnd_909884 46143983391172672431163 := by
  unfold tailWord_909884
  simp only [CollatzResearch.WordTrace]
  refine ⟨16593097917826569330308353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22124130557102092440411137 16593097917826569330308353)
  ·
    refine ⟨12444823438369926997731265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16593097917826569330308353 12444823438369926997731265)
    ·
      refine ⟨9333617578777445248298449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12444823438369926997731265 9333617578777445248298449)
      ·
        refine ⟨7000213184083083936223837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9333617578777445248298449 7000213184083083936223837)
        ·
          refine ⟨2625079944031156476083939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7000213184083083936223837 2625079944031156476083939)
          ·
            refine ⟨3937619916046734714125909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2625079944031156476083939 3937619916046734714125909)
            ·
              refine ⟨46143983391172672431163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3937619916046734714125909 46143983391172672431163)
              ·
                rfl

theorem cell20_909884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 8].length) (baseStart_909884 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_909884 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_909884 prefixEnd_909884 := by exact prefixLift 909884
  have htrace : WordTrace (prefixWord ++ tailWord_909884) baseStart_909884 baseEnd_909884 := by
    simpa [prefixWord, tailWord_909884, baseEnd_909884] using wordTrace_append hprefix tailTrace_909884
  have hstable : (prefixWord ++ tailWord_909884).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909884).length < 2 ^ (prefixWord ++ tailWord_909884).sum := by decide
  have hdescent : baseEnd_909884 < baseStart_909884 := by decide
  rcases family_descends (prefixWord ++ tailWord_909884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909901 : List Nat := [1, 6, 1, 1, 2, 1, 1, 7]
def baseStart_909901 : Nat := 118140960795 + 909901 * 2 ^ 59
def prefixEnd_909901 : Nat := 4983230072969 + 3 ^ 40 * 909901 * 2
def baseEnd_909901 : Nat := 138434536594592516104577

theorem tailTrace_909901 : CollatzResearch.WordTrace tailWord_909901 prefixEnd_909901 138434536594592516104577 := by
  unfold tailWord_909901
  simp only [CollatzResearch.WordTrace]
  refine ⟨33186815876591550563985557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22124543917727700375990371 33186815876591550563985557)
  ·
    refine ⟨1555631994215228932686823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 33186815876591550563985557 1555631994215228932686823)
    ·
      refine ⟨2333447991322843399030235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1555631994215228932686823 2333447991322843399030235)
      ·
        refine ⟨3500171986984265098545353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2333447991322843399030235 3500171986984265098545353)
        ·
          refine ⟨2625128990238198823909015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3500171986984265098545353 2625128990238198823909015)
          ·
            refine ⟨3937693485357298235863523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2625128990238198823909015 3937693485357298235863523)
            ·
              refine ⟨5906540228035947353795285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3937693485357298235863523 5906540228035947353795285)
              ·
                refine ⟨138434536594592516104577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5906540228035947353795285 138434536594592516104577)
                ·
                  rfl

theorem cell20_909901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 7].length) (baseStart_909901 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_909901 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_909901 prefixEnd_909901 := by exact prefixLift 909901
  have htrace : WordTrace (prefixWord ++ tailWord_909901) baseStart_909901 baseEnd_909901 := by
    simpa [prefixWord, tailWord_909901, baseEnd_909901] using wordTrace_append hprefix tailTrace_909901
  have hstable : (prefixWord ++ tailWord_909901).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909901).length < 2 ^ (prefixWord ++ tailWord_909901).sum := by decide
  have hdescent : baseEnd_909901 < baseStart_909901 := by decide
  rcases family_descends (prefixWord ++ tailWord_909901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909942 : List Nat := [5, 1, 1, 2, 3, 1, 2, 2, 3]
def baseStart_909942 : Nat := 118140960795 + 909942 * 2 ^ 59
def prefixEnd_909942 : Nat := 4983230072969 + 3 ^ 40 * 909942 * 2
def baseEnd_909942 : Nat := 415322323300963627946897

theorem tailTrace_909942 : CollatzResearch.WordTrace tailWord_909942 prefixEnd_909942 415322323300963627946897 := by
  unfold tailWord_909942
  simp only [CollatzResearch.WordTrace]
  refine ⟨2074269454340188410389255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22125540846295343044152053 2074269454340188410389255)
  ·
    refine ⟨3111404181510282615583883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2074269454340188410389255 3111404181510282615583883)
    ·
      refine ⟨4667106272265423923375825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3111404181510282615583883 4667106272265423923375825)
      ·
        refine ⟨3500329704199067942531869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4667106272265423923375825 3500329704199067942531869)
        ·
          refine ⟨1312623639074650478449451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3500329704199067942531869 1312623639074650478449451)
          ·
            refine ⟨1968935458611975717674177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1312623639074650478449451 1968935458611975717674177)
            ·
              refine ⟨1476701593958981788255633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1968935458611975717674177 1476701593958981788255633)
              ·
                refine ⟨1107526195469236341191725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1476701593958981788255633 1107526195469236341191725)
                ·
                  refine ⟨415322323300963627946897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1107526195469236341191725 415322323300963627946897)
                  ·
                    rfl

theorem cell20_909942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 2, 2, 3].length) (baseStart_909942 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_909942 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_909942 prefixEnd_909942 := by exact prefixLift 909942
  have htrace : WordTrace (prefixWord ++ tailWord_909942) baseStart_909942 baseEnd_909942 := by
    simpa [prefixWord, tailWord_909942, baseEnd_909942] using wordTrace_append hprefix tailTrace_909942
  have hstable : (prefixWord ++ tailWord_909942).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909942).length < 2 ^ (prefixWord ++ tailWord_909942).sum := by decide
  have hdescent : baseEnd_909942 < baseStart_909942 := by decide
  rcases family_descends (prefixWord ++ tailWord_909942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909949 : List Nat := [1, 4, 1, 1, 5, 1, 1, 4, 2]
def baseStart_909949 : Nat := 118140960795 + 909949 * 2 ^ 59
def prefixEnd_909949 : Nat := 4983230072969 + 3 ^ 40 * 909949 * 2
def baseEnd_909949 : Nat := 415325518291702714713535

theorem tailTrace_909949 : CollatzResearch.WordTrace tailWord_909949 prefixEnd_909949 415325518291702714713535 := by
  unfold tailWord_909949
  simp only [CollatzResearch.WordTrace]
  refine ⟨33188566580417654761732901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22125711053611769841155267 33188566580417654761732901)
  ·
    refine ⟨6222856233828310267824919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33188566580417654761732901 6222856233828310267824919)
    ·
      refine ⟨9334284350742465401737379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6222856233828310267824919 9334284350742465401737379)
      ·
        refine ⟨14001426526113698102606069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9334284350742465401737379 14001426526113698102606069)
        ·
          refine ⟨1312633736823159197119319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14001426526113698102606069 1312633736823159197119319)
          ·
            refine ⟨1968950605234738795678979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1312633736823159197119319 1968950605234738795678979)
            ·
              refine ⟨2953425907852108193518469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1968950605234738795678979 2953425907852108193518469)
              ·
                refine ⟨553767357722270286284713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2953425907852108193518469 553767357722270286284713)
                ·
                  refine ⟨415325518291702714713535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 553767357722270286284713 415325518291702714713535)
                  ·
                    rfl

theorem cell20_909949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 4, 2].length) (baseStart_909949 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_909949 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_909949 prefixEnd_909949 := by exact prefixLift 909949
  have htrace : WordTrace (prefixWord ++ tailWord_909949) baseStart_909949 baseEnd_909949 := by
    simpa [prefixWord, tailWord_909949, baseEnd_909949] using wordTrace_append hprefix tailTrace_909949
  have hstable : (prefixWord ++ tailWord_909949).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909949).length < 2 ^ (prefixWord ++ tailWord_909949).sum := by decide
  have hdescent : baseEnd_909949 < baseStart_909949 := by decide
  rcases family_descends (prefixWord ++ tailWord_909949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909953 : List Nat := [1, 2, 4, 2, 1, 1, 2, 3, 4]
def baseStart_909953 : Nat := 118140960795 + 909953 * 2 ^ 59
def prefixEnd_909953 : Nat := 4983230072969 + 3 ^ 40 * 909953 * 2
def baseEnd_909953 : Nat := 415327344000696478580185

theorem tailTrace_909953 : CollatzResearch.WordTrace tailWord_909953 prefixEnd_909953 415327344000696478580185 := by
  unfold tailWord_909953
  simp only [CollatzResearch.WordTrace]
  refine ⟨33188712472403163444878513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22125808314935442296585675 33188712472403163444878513)
  ·
    refine ⟨24891534354302372583658885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33188712472403163444878513 24891534354302372583658885)
    ·
      refine ⟨4667162691431694859436041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24891534354302372583658885 4667162691431694859436041)
      ·
        refine ⟨3500372018573771144577031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4667162691431694859436041 3500372018573771144577031)
        ·
          refine ⟨5250558027860656716865547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3500372018573771144577031 5250558027860656716865547)
          ·
            refine ⟨7875837041790985075298321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5250558027860656716865547 7875837041790985075298321)
            ·
              refine ⟨5906877781343238806473741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7875837041790985075298321 5906877781343238806473741)
              ·
                refine ⟨2215079168003714552427653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5906877781343238806473741 2215079168003714552427653)
                ·
                  refine ⟨415327344000696478580185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2215079168003714552427653 415327344000696478580185)
                  ·
                    rfl

theorem cell20_909953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 3, 4].length) (baseStart_909953 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_909953 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_909953 prefixEnd_909953 := by exact prefixLift 909953
  have htrace : WordTrace (prefixWord ++ tailWord_909953) baseStart_909953 baseEnd_909953 := by
    simpa [prefixWord, tailWord_909953, baseEnd_909953] using wordTrace_append hprefix tailTrace_909953
  have hstable : (prefixWord ++ tailWord_909953).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909953).length < 2 ^ (prefixWord ++ tailWord_909953).sum := by decide
  have hdescent : baseEnd_909953 < baseStart_909953 := by decide
  rcases family_descends (prefixWord ++ tailWord_909953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909970 : List Nat := [3, 2, 3, 1, 2, 2, 1, 2, 4]
def baseStart_909970 : Nat := 118140960795 + 909970 * 2 ^ 59
def prefixEnd_909970 : Nat := 4983230072969 + 3 ^ 40 * 909970 * 2
def baseEnd_909970 : Nat := 415335103263919975013449

theorem tailTrace_909970 : CollatzResearch.WordTrace tailWord_909970 prefixEnd_909970 415335103263919975013449 := by
  unfold tailWord_909970
  simp only [CollatzResearch.WordTrace]
  refine ⟨8297333128335393837061841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22126221675561050232164909 8297333128335393837061841)
  ·
    refine ⟨6222999846251545377796381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8297333128335393837061841 6222999846251545377796381)
    ·
      refine ⟨2333624942344329516673643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6222999846251545377796381 2333624942344329516673643)
      ·
        refine ⟨3500437413516494275010465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2333624942344329516673643 3500437413516494275010465)
        ·
          refine ⟨2625328060137370706257849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3500437413516494275010465 2625328060137370706257849)
          ·
            refine ⟨1968996045103028029693387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2625328060137370706257849 1968996045103028029693387)
            ·
              refine ⟨2953494067654542044540081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1968996045103028029693387 2953494067654542044540081)
              ·
                refine ⟨2215120550740906533405061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2953494067654542044540081 2215120550740906533405061)
                ·
                  refine ⟨415335103263919975013449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2215120550740906533405061 415335103263919975013449)
                  ·
                    rfl

theorem cell20_909970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 2, 4].length) (baseStart_909970 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_909970 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_909970 prefixEnd_909970 := by exact prefixLift 909970
  have htrace : WordTrace (prefixWord ++ tailWord_909970) baseStart_909970 baseEnd_909970 := by
    simpa [prefixWord, tailWord_909970, baseEnd_909970] using wordTrace_append hprefix tailTrace_909970
  have hstable : (prefixWord ++ tailWord_909970).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909970).length < 2 ^ (prefixWord ++ tailWord_909970).sum := by decide
  have hdescent : baseEnd_909970 < baseStart_909970 := by decide
  rcases family_descends (prefixWord ++ tailWord_909970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_909994 : List Nat := [3, 1, 5, 2, 1, 1, 7]
def baseStart_909994 : Nat := 118140960795 + 909994 * 2 ^ 59
def prefixEnd_909994 : Nat := 4983230072969 + 3 ^ 40 * 909994 * 2
def baseEnd_909994 : Nat := 46149561946431395357039

theorem tailTrace_909994 : CollatzResearch.WordTrace tailWord_909994 prefixEnd_909994 46149561946431395357039 := by
  unfold tailWord_909994
  simp only [CollatzResearch.WordTrace]
  refine ⟨8297551966313656861780259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22126805243503084964747357 8297551966313656861780259)
  ·
    refine ⟨12446327949470485292670389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8297551966313656861780259 12446327949470485292670389)
    ·
      refine ⟨1166843245262857996187849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12446327949470485292670389 1166843245262857996187849)
      ·
        refine ⟨875132433947143497140887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1166843245262857996187849 875132433947143497140887)
        ·
          refine ⟨1312698650920715245711331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 875132433947143497140887 1312698650920715245711331)
          ·
            refine ⟨1969047976381072868566997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1312698650920715245711331 1969047976381072868566997)
            ·
              refine ⟨46149561946431395357039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1969047976381072868566997 46149561946431395357039)
              ·
                rfl

theorem cell20_909994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 7].length) (baseStart_909994 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_909994 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_909994 prefixEnd_909994 := by exact prefixLift 909994
  have htrace : WordTrace (prefixWord ++ tailWord_909994) baseStart_909994 baseEnd_909994 := by
    simpa [prefixWord, tailWord_909994, baseEnd_909994] using wordTrace_append hprefix tailTrace_909994
  have hstable : (prefixWord ++ tailWord_909994).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_909994).length < 2 ^ (prefixWord ++ tailWord_909994).sum := by decide
  have hdescent : baseEnd_909994 < baseStart_909994 := by decide
  rcases family_descends (prefixWord ++ tailWord_909994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910001 : List Nat := [1, 2, 2, 6, 1, 1, 1, 1, 5]
def baseStart_910001 : Nat := 118140960795 + 910001 * 2 ^ 59
def prefixEnd_910001 : Nat := 4983230072969 + 3 ^ 40 * 910001 * 2
def baseEnd_910001 : Nat := 415349252508621644979989

theorem tailTrace_910001 : CollatzResearch.WordTrace tailWord_910001 prefixEnd_910001 415349252508621644979989 := by
  unfold tailWord_910001
  simp only [CollatzResearch.WordTrace]
  refine ⟨33190463176229267642625857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22126975450819511761750571 33190463176229267642625857)
  ·
    refine ⟨24892847382171950731969393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33190463176229267642625857 24892847382171950731969393)
    ·
      refine ⟨18669635536628963048977045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24892847382171950731969393 18669635536628963048977045)
      ·
        refine ⟨875139165779482642920799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 18669635536628963048977045 875139165779482642920799)
        ·
          refine ⟨1312708748669223964381199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 875139165779482642920799 1312708748669223964381199)
          ·
            refine ⟨1969063123003835946571799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1312708748669223964381199 1969063123003835946571799)
            ·
              refine ⟨2953594684505753919857699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1969063123003835946571799 2953594684505753919857699)
              ·
                refine ⟨4430392026758630879786549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2953594684505753919857699 4430392026758630879786549)
                ·
                  refine ⟨415349252508621644979989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4430392026758630879786549 415349252508621644979989)
                  ·
                    rfl

theorem cell20_910001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 1, 5].length) (baseStart_910001 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_910001 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_910001 prefixEnd_910001 := by exact prefixLift 910001
  have htrace : WordTrace (prefixWord ++ tailWord_910001) baseStart_910001 baseEnd_910001 := by
    simpa [prefixWord, tailWord_910001, baseEnd_910001] using wordTrace_append hprefix tailTrace_910001
  have hstable : (prefixWord ++ tailWord_910001).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910001).length < 2 ^ (prefixWord ++ tailWord_910001).sum := by decide
  have hdescent : baseEnd_910001 < baseStart_910001 := by decide
  rcases family_descends (prefixWord ++ tailWord_910001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910057 : List Nat := [1, 2, 1, 1, 1, 2, 12]
def baseStart_910057 : Nat := 118140960795 + 910057 * 2 ^ 59
def prefixEnd_910057 : Nat := 4983230072969 + 3 ^ 40 * 910057 * 2
def baseEnd_910057 : Nat := 46152756937170482123677

theorem tailTrace_910057 : CollatzResearch.WordTrace tailWord_910057 prefixEnd_910057 46152756937170482123677 := by
  unfold tailWord_910057
  simp only [CollatzResearch.WordTrace]
  refine ⟨33192505664026389206664425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22128337109350926137776283 33192505664026389206664425)
  ·
    refine ⟨24894379248019791904998319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33192505664026389206664425 24894379248019791904998319)
    ·
      refine ⟨37341568872029687857497479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24894379248019791904998319 37341568872029687857497479)
      ·
        refine ⟨56012353308044531786246219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37341568872029687857497479 56012353308044531786246219)
        ·
          refine ⟨84018529962066797679369329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56012353308044531786246219 84018529962066797679369329)
          ·
            refine ⟨63013897471550098259526997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84018529962066797679369329 63013897471550098259526997)
            ·
              refine ⟨46152756937170482123677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 63013897471550098259526997 46152756937170482123677)
              ·
                rfl

theorem cell20_910057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 12].length) (baseStart_910057 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_910057 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_910057 prefixEnd_910057 := by exact prefixLift 910057
  have htrace : WordTrace (prefixWord ++ tailWord_910057) baseStart_910057 baseEnd_910057 := by
    simpa [prefixWord, tailWord_910057, baseEnd_910057] using wordTrace_append hprefix tailTrace_910057
  have hstable : (prefixWord ++ tailWord_910057).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910057).length < 2 ^ (prefixWord ++ tailWord_910057).sum := by decide
  have hdescent : baseEnd_910057 < baseStart_910057 := by decide
  rcases family_descends (prefixWord ++ tailWord_910057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910063 : List Nat := [1, 1, 2, 1, 5, 3, 3, 2, 2]
def baseStart_910063 : Nat := 118140960795 + 910063 * 2 ^ 59
def prefixEnd_910063 : Nat := 4983230072969 + 3 ^ 40 * 910063 * 2
def baseEnd_910063 : Nat := 415377550998024984913069

theorem tailTrace_910063 : CollatzResearch.WordTrace tailWord_910063 prefixEnd_910063 415377550998024984913069 := by
  unfold tailWord_910063
  simp only [CollatzResearch.WordTrace]
  refine ⟨33192724502004652231382843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22128483001336434820921895 33192724502004652231382843)
  ·
    refine ⟨49789086753006978347074265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33192724502004652231382843 49789086753006978347074265)
    ·
      refine ⟨37341815064755233760305699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49789086753006978347074265 37341815064755233760305699)
      ·
        refine ⟨56012722597132850640458549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37341815064755233760305699 56012722597132850640458549)
        ·
          refine ⟨5251192743481204747542989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 56012722597132850640458549 5251192743481204747542989)
          ·
            refine ⟨1969197278805451780328621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5251192743481204747542989 1969197278805451780328621)
            ·
              refine ⟨738448979552044417623233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1969197278805451780328621 738448979552044417623233)
              ·
                refine ⟨553836734664033313217425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 738448979552044417623233 553836734664033313217425)
                ·
                  refine ⟨415377550998024984913069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 553836734664033313217425 415377550998024984913069)
                  ·
                    rfl

theorem cell20_910063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 3, 2, 2].length) (baseStart_910063 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_910063 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_910063 prefixEnd_910063 := by exact prefixLift 910063
  have htrace : WordTrace (prefixWord ++ tailWord_910063) baseStart_910063 baseEnd_910063 := by
    simpa [prefixWord, tailWord_910063, baseEnd_910063] using wordTrace_append hprefix tailTrace_910063
  have hstable : (prefixWord ++ tailWord_910063).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910063).length < 2 ^ (prefixWord ++ tailWord_910063).sum := by decide
  have hdescent : baseEnd_910063 < baseStart_910063 := by decide
  rcases family_descends (prefixWord ++ tailWord_910063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910069 : List Nat := [1, 3, 6, 1, 2, 1, 2, 1, 3]
def baseStart_910069 : Nat := 118140960795 + 910069 * 2 ^ 59
def prefixEnd_910069 : Nat := 4983230072969 + 3 ^ 40 * 910069 * 2
def baseEnd_910069 : Nat := 415380289561515630713045

theorem tailTrace_910069 : CollatzResearch.WordTrace tailWord_910069 prefixEnd_910069 415380289561515630713045 := by
  unfold tailWord_910069
  simp only [CollatzResearch.WordTrace]
  refine ⟨33192943339982915256101261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22128628893321943504067507 33192943339982915256101261)
  ·
    refine ⟨12447353752493593221037973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33192943339982915256101261 12447353752493593221037973)
    ·
      refine ⟨583469707148137182236155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 12447353752493593221037973 583469707148137182236155)
      ·
        refine ⟨875204560722205773354233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 583469707148137182236155 875204560722205773354233)
        ·
          refine ⟨656403420541654330015675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 875204560722205773354233 656403420541654330015675)
          ·
            refine ⟨984605130812481495023513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 656403420541654330015675 984605130812481495023513)
            ·
              refine ⟨738453848109361121267635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 984605130812481495023513 738453848109361121267635)
              ·
                refine ⟨1107680772164041681901453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 738453848109361121267635 1107680772164041681901453)
                ·
                  refine ⟨415380289561515630713045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1107680772164041681901453 415380289561515630713045)
                  ·
                    rfl

theorem cell20_910069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 2, 1, 3].length) (baseStart_910069 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_910069 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_910069 prefixEnd_910069 := by exact prefixLift 910069
  have htrace : WordTrace (prefixWord ++ tailWord_910069) baseStart_910069 baseEnd_910069 := by
    simpa [prefixWord, tailWord_910069, baseEnd_910069] using wordTrace_append hprefix tailTrace_910069
  have hstable : (prefixWord ++ tailWord_910069).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910069).length < 2 ^ (prefixWord ++ tailWord_910069).sum := by decide
  have hdescent : baseEnd_910069 < baseStart_910069 := by decide
  rcases family_descends (prefixWord ++ tailWord_910069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910095 : List Nat := [1, 1, 2, 1, 1, 1, 5, 8]
def baseStart_910095 : Nat := 118140960795 + 910095 * 2 ^ 59
def prefixEnd_910095 : Nat := 4983230072969 + 3 ^ 40 * 910095 * 2
def baseEnd_910095 : Nat := 138464052223325031948757

theorem tailTrace_910095 : CollatzResearch.WordTrace tailWord_910095 prefixEnd_910095 138464052223325031948757 := by
  unfold tailWord_910095
  simp only [CollatzResearch.WordTrace]
  refine ⟨33193891637888721696547739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22129261091925814464365159 33193891637888721696547739)
  ·
    refine ⟨49790837456833082544821609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33193891637888721696547739 49790837456833082544821609)
    ·
      refine ⟨37343128092624811908616207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49790837456833082544821609 37343128092624811908616207)
      ·
        refine ⟨56014692138937217862924311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37343128092624811908616207 56014692138937217862924311)
        ·
          refine ⟨84022038208405826794386467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56014692138937217862924311 84022038208405826794386467)
          ·
            refine ⟨126033057312608740191579701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84022038208405826794386467 126033057312608740191579701)
            ·
              refine ⟨11815599123057069392960597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 126033057312608740191579701 11815599123057069392960597)
              ·
                refine ⟨138464052223325031948757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11815599123057069392960597 138464052223325031948757)
                ·
                  rfl

theorem cell20_910095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 8].length) (baseStart_910095 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_910095 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_910095 prefixEnd_910095 := by exact prefixLift 910095
  have htrace : WordTrace (prefixWord ++ tailWord_910095) baseStart_910095 baseEnd_910095 := by
    simpa [prefixWord, tailWord_910095, baseEnd_910095] using wordTrace_append hprefix tailTrace_910095
  have hstable : (prefixWord ++ tailWord_910095).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910095).length < 2 ^ (prefixWord ++ tailWord_910095).sum := by decide
  have hdescent : baseEnd_910095 < baseStart_910095 := by decide
  rcases family_descends (prefixWord ++ tailWord_910095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910125 : List Nat := [1, 5, 3, 2, 1, 2, 1, 5]
def baseStart_910125 : Nat := 118140960795 + 910125 * 2 ^ 59
def prefixEnd_910125 : Nat := 4983230072969 + 3 ^ 40 * 910125 * 2
def baseEnd_910125 : Nat := 138468616495809441615383

theorem tailTrace_910125 : CollatzResearch.WordTrace tailWord_910125 prefixEnd_910125 138468616495809441615383 := by
  unfold tailWord_910125
  simp only [CollatzResearch.WordTrace]
  refine ⟨33194985827780036820139829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22129990551853357880093219 33194985827780036820139829)
  ·
    refine ⟨3112029921354378451888109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33194985827780036820139829 3112029921354378451888109)
    ·
      refine ⟨1167011220507891919458041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3112029921354378451888109 1167011220507891919458041)
      ·
        refine ⟨875258415380918939593531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1167011220507891919458041 875258415380918939593531)
        ·
          refine ⟨1312887623071378409390297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 875258415380918939593531 1312887623071378409390297)
          ·
            refine ⟨984665717303533807042723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1312887623071378409390297 984665717303533807042723)
            ·
              refine ⟨1476998575955300710564085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 984665717303533807042723 1476998575955300710564085)
              ·
                refine ⟨138468616495809441615383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1476998575955300710564085 138468616495809441615383)
                ·
                  rfl

theorem cell20_910125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 1, 5].length) (baseStart_910125 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_910125 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_910125 prefixEnd_910125 := by exact prefixLift 910125
  have htrace : WordTrace (prefixWord ++ tailWord_910125) baseStart_910125 baseEnd_910125 := by
    simpa [prefixWord, tailWord_910125, baseEnd_910125] using wordTrace_append hprefix tailTrace_910125
  have hstable : (prefixWord ++ tailWord_910125).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910125).length < 2 ^ (prefixWord ++ tailWord_910125).sum := by decide
  have hdescent : baseEnd_910125 < baseStart_910125 := by decide
  rcases family_descends (prefixWord ++ tailWord_910125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910143 : List Nat := [1, 1, 2, 2, 5, 2, 1, 2, 4]
def baseStart_910143 : Nat := 118140960795 + 910143 * 2 ^ 59
def prefixEnd_910143 : Nat := 4983230072969 + 3 ^ 40 * 910143 * 2
def baseEnd_910143 : Nat := 415414065177900262246075

theorem tailTrace_910143 : CollatzResearch.WordTrace tailWord_910143 prefixEnd_910143 415414065177900262246075 := by
  unfold tailWord_910143
  simp only [CollatzResearch.WordTrace]
  refine ⟨33195642341714825894295083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22130428227809883929530055 33195642341714825894295083)
  ·
    refine ⟨49793463512572238841442625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33195642341714825894295083 49793463512572238841442625)
    ·
      refine ⟨37345097634429179131081969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49793463512572238841442625 37345097634429179131081969)
      ·
        refine ⟨28008823225821884348311477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37345097634429179131081969 28008823225821884348311477)
        ·
          refine ⟨2625827177420801657654201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28008823225821884348311477 2625827177420801657654201)
          ·
            refine ⟨1969370383065601243240651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2625827177420801657654201 1969370383065601243240651)
            ·
              refine ⟨2954055574598401864860977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1969370383065601243240651 2954055574598401864860977)
              ·
                refine ⟨2215541680948801398645733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2954055574598401864860977 2215541680948801398645733)
                ·
                  refine ⟨415414065177900262246075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2215541680948801398645733 415414065177900262246075)
                  ·
                    rfl

theorem cell20_910143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 2, 4].length) (baseStart_910143 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_910143 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_910143 prefixEnd_910143 := by exact prefixLift 910143
  have htrace : WordTrace (prefixWord ++ tailWord_910143) baseStart_910143 baseEnd_910143 := by
    simpa [prefixWord, tailWord_910143, baseEnd_910143] using wordTrace_append hprefix tailTrace_910143
  have hstable : (prefixWord ++ tailWord_910143).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910143).length < 2 ^ (prefixWord ++ tailWord_910143).sum := by decide
  have hdescent : baseEnd_910143 < baseStart_910143 := by decide
  rcases family_descends (prefixWord ++ tailWord_910143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910195 : List Nat := [1, 1, 1, 2, 2, 1, 4, 5, 3]
def baseStart_910195 : Nat := 118140960795 + 910195 * 2 ^ 59
def prefixEnd_910195 : Nat := 4983230072969 + 3 ^ 40 * 910195 * 2
def baseEnd_910195 : Nat := 415437799394819192512529

theorem tailTrace_910195 : CollatzResearch.WordTrace tailWord_910195 prefixEnd_910195 415437799394819192512529 := by
  unfold tailWord_910195
  simp only [CollatzResearch.WordTrace]
  refine ⟨33197538937526438775188039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22131692625017625850125359 33197538937526438775188039)
  ·
    refine ⟨49796308406289658162782059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33197538937526438775188039 49796308406289658162782059)
    ·
      refine ⟨74694462609434487244173089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49796308406289658162782059 74694462609434487244173089)
      ·
        refine ⟨56020846957075865433129817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74694462609434487244173089 56020846957075865433129817)
        ·
          refine ⟨42015635217806899074847363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56020846957075865433129817 42015635217806899074847363)
          ·
            refine ⟨63023452826710348612271045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42015635217806899074847363 63023452826710348612271045)
            ·
              refine ⟨11816897405008190364800821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63023452826710348612271045 11816897405008190364800821)
              ·
                refine ⟨1107834131719517846700077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11816897405008190364800821 1107834131719517846700077)
                ·
                  refine ⟨415437799394819192512529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1107834131719517846700077 415437799394819192512529)
                  ·
                    rfl

theorem cell20_910195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 5, 3].length) (baseStart_910195 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_910195 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_910195 prefixEnd_910195 := by exact prefixLift 910195
  have htrace : WordTrace (prefixWord ++ tailWord_910195) baseStart_910195 baseEnd_910195 := by
    simpa [prefixWord, tailWord_910195, baseEnd_910195] using wordTrace_append hprefix tailTrace_910195
  have hstable : (prefixWord ++ tailWord_910195).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910195).length < 2 ^ (prefixWord ++ tailWord_910195).sum := by decide
  have hdescent : baseEnd_910195 < baseStart_910195 := by decide
  rcases family_descends (prefixWord ++ tailWord_910195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910198 : List Nat := [5, 1, 1, 3, 1, 1, 2, 2, 4]
def baseStart_910198 : Nat := 118140960795 + 910198 * 2 ^ 59
def prefixEnd_910198 : Nat := 4983230072969 + 3 ^ 40 * 910198 * 2
def baseEnd_910198 : Nat := 415439168676564515412517

theorem tailTrace_910198 : CollatzResearch.WordTrace tailWord_910198 prefixEnd_910198 415439168676564515412517 := by
  unfold tailWord_910198
  simp only [CollatzResearch.WordTrace]
  refine ⟨2074853022282223142971703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22131765571010380191698165 2074853022282223142971703)
  ·
    refine ⟨3112279533423334714457555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2074853022282223142971703 3112279533423334714457555)
    ·
      refine ⟨4668419300135002071686333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3112279533423334714457555 4668419300135002071686333)
      ·
        refine ⟨1750657237550625776882375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4668419300135002071686333 1750657237550625776882375)
        ·
          refine ⟨2625985856325938665323563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1750657237550625776882375 2625985856325938665323563)
          ·
            refine ⟨3938978784488907997985345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2625985856325938665323563 3938978784488907997985345)
            ·
              refine ⟨2954234088366680998489009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3938978784488907997985345 2954234088366680998489009)
              ·
                refine ⟨2215675566275010748866757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2954234088366680998489009 2215675566275010748866757)
                ·
                  refine ⟨415439168676564515412517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2215675566275010748866757 415439168676564515412517)
                  ·
                    rfl

theorem cell20_910198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_910198 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_910198 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_910198 prefixEnd_910198 := by exact prefixLift 910198
  have htrace : WordTrace (prefixWord ++ tailWord_910198) baseStart_910198 baseEnd_910198 := by
    simpa [prefixWord, tailWord_910198, baseEnd_910198] using wordTrace_append hprefix tailTrace_910198
  have hstable : (prefixWord ++ tailWord_910198).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910198).length < 2 ^ (prefixWord ++ tailWord_910198).sum := by decide
  have hdescent : baseEnd_910198 < baseStart_910198 := by decide
  rcases family_descends (prefixWord ++ tailWord_910198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910215 : List Nat := [1, 1, 4, 2, 3, 3, 1, 3, 2]
def baseStart_910215 : Nat := 118140960795 + 910215 * 2 ^ 59
def prefixEnd_910215 : Nat := 4983230072969 + 3 ^ 40 * 910215 * 2
def baseEnd_910215 : Nat := 415446927939788011845781

theorem tailTrace_910215 : CollatzResearch.WordTrace tailWord_910215 prefixEnd_910215 415446927939788011845781 := by
  unfold tailWord_910215
  simp only [CollatzResearch.WordTrace]
  refine ⟨33198268397453982190916099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22132178931635988127277399 33198268397453982190916099)
  ·
    refine ⟨49797402596180973286374149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33198268397453982190916099 49797402596180973286374149)
    ·
      refine ⟨9337012986783932491195153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49797402596180973286374149 9337012986783932491195153)
      ·
        refine ⟨7002759740087949368396365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9337012986783932491195153 7002759740087949368396365)
        ·
          refine ⟨2626034902532981013148637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7002759740087949368396365 2626034902532981013148637)
          ·
            refine ⟨984763088449867879930739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2626034902532981013148637 984763088449867879930739)
            ·
              refine ⟨1477144632674801819896109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 984763088449867879930739 1477144632674801819896109)
              ·
                refine ⟨553929237253050682461041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1477144632674801819896109 553929237253050682461041)
                ·
                  refine ⟨415446927939788011845781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 553929237253050682461041 415446927939788011845781)
                  ·
                    rfl

theorem cell20_910215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 1, 3, 2].length) (baseStart_910215 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_910215 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_910215 prefixEnd_910215 := by exact prefixLift 910215
  have htrace : WordTrace (prefixWord ++ tailWord_910215) baseStart_910215 baseEnd_910215 := by
    simpa [prefixWord, tailWord_910215, baseEnd_910215] using wordTrace_append hprefix tailTrace_910215
  have hstable : (prefixWord ++ tailWord_910215).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910215).length < 2 ^ (prefixWord ++ tailWord_910215).sum := by decide
  have hdescent : baseEnd_910215 < baseStart_910215 := by decide
  rcases family_descends (prefixWord ++ tailWord_910215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910233 : List Nat := [1, 2, 1, 2, 1, 3, 1, 6, 3]
def baseStart_910233 : Nat := 118140960795 + 910233 * 2 ^ 59
def prefixEnd_910233 : Nat := 4983230072969 + 3 ^ 40 * 910233 * 2
def baseEnd_910233 : Nat := 415455143630259949245707

theorem tailTrace_910233 : CollatzResearch.WordTrace tailWord_910233 prefixEnd_910233 415455143630259949245707 := by
  unfold tailWord_910233
  simp only [CollatzResearch.WordTrace]
  refine ⟨33198924911388771265071353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22132616607592514176714235 33198924911388771265071353)
  ·
    refine ⟨24899193683541578448803515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33198924911388771265071353 24899193683541578448803515)
    ·
      refine ⟨37348790525312367673205273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24899193683541578448803515 37348790525312367673205273)
      ·
        refine ⟨28011592893984275754903955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37348790525312367673205273 28011592893984275754903955)
        ·
          refine ⟨42017389340976413632355933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28011592893984275754903955 42017389340976413632355933)
          ·
            refine ⟨15756521002866155112133475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42017389340976413632355933 15756521002866155112133475)
            ·
              refine ⟨23634781504299232668200213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15756521002866155112133475 23634781504299232668200213)
              ·
                refine ⟨1107880383014026531321885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 23634781504299232668200213 1107880383014026531321885)
                ·
                  refine ⟨415455143630259949245707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1107880383014026531321885 415455143630259949245707)
                  ·
                    rfl

theorem cell20_910233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 6, 3].length) (baseStart_910233 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_910233 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_910233 prefixEnd_910233 := by exact prefixLift 910233
  have htrace : WordTrace (prefixWord ++ tailWord_910233) baseStart_910233 baseEnd_910233 := by
    simpa [prefixWord, tailWord_910233, baseEnd_910233] using wordTrace_append hprefix tailTrace_910233
  have hstable : (prefixWord ++ tailWord_910233).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910233).length < 2 ^ (prefixWord ++ tailWord_910233).sum := by decide
  have hdescent : baseEnd_910233 < baseStart_910233 := by decide
  rcases family_descends (prefixWord ++ tailWord_910233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910347 : List Nat := [1, 1, 1, 1, 6, 3, 1, 1, 5]
def baseStart_910347 : Nat := 118140960795 + 910347 * 2 ^ 59
def prefixEnd_910347 : Nat := 4983230072969 + 3 ^ 40 * 910347 * 2
def baseEnd_910347 : Nat := 415507176336582219445241

theorem tailTrace_910347 : CollatzResearch.WordTrace tailWord_910347 prefixEnd_910347 415507176336582219445241 := by
  unfold tailWord_910347
  simp only [CollatzResearch.WordTrace]
  refine ⟨33203082832975768734721295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22135388555317179156480863 33203082832975768734721295)
  ·
    refine ⟨49804624249463653102081943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33203082832975768734721295 49804624249463653102081943)
    ·
      refine ⟨74706936374195479653122915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49804624249463653102081943 74706936374195479653122915)
      ·
        refine ⟨112060404561293219479684373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74706936374195479653122915 112060404561293219479684373)
        ·
          refine ⟨5252831463810619663110205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 112060404561293219479684373 5252831463810619663110205)
          ·
            refine ⟨1969811798928982373666327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5252831463810619663110205 1969811798928982373666327)
            ·
              refine ⟨2954717698393473560499491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1969811798928982373666327 2954717698393473560499491)
              ·
                refine ⟨4432076547590210340749237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2954717698393473560499491 4432076547590210340749237)
                ·
                  refine ⟨415507176336582219445241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4432076547590210340749237 415507176336582219445241)
                  ·
                    rfl

theorem cell20_910347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 1, 5].length) (baseStart_910347 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_910347 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_910347 prefixEnd_910347 := by exact prefixLift 910347
  have htrace : WordTrace (prefixWord ++ tailWord_910347) baseStart_910347 baseEnd_910347 := by
    simpa [prefixWord, tailWord_910347, baseEnd_910347] using wordTrace_append hprefix tailTrace_910347
  have hstable : (prefixWord ++ tailWord_910347).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910347).length < 2 ^ (prefixWord ++ tailWord_910347).sum := by decide
  have hdescent : baseEnd_910347 < baseStart_910347 := by decide
  rcases family_descends (prefixWord ++ tailWord_910347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910350 : List Nat := [4, 1, 1, 2, 2, 2, 2, 4, 2]
def baseStart_910350 : Nat := 118140960795 + 910350 * 2 ^ 59
def prefixEnd_910350 : Nat := 4983230072969 + 3 ^ 40 * 910350 * 2
def baseEnd_910350 : Nat := 415508545618327542345229

theorem tailTrace_910350 : CollatzResearch.WordTrace tailWord_910350 prefixEnd_910350 415508545618327542345229 := by
  unfold tailWord_910350
  simp only [CollatzResearch.WordTrace]
  refine ⟨4150399031495612530885063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22135461501309933498053669 4150399031495612530885063)
  ·
    refine ⟨6225598547243418796327595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4150399031495612530885063 6225598547243418796327595)
    ·
      refine ⟨9338397820865128194491393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6225598547243418796327595 9338397820865128194491393)
      ·
        refine ⟨7003798365648846145868545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9338397820865128194491393 7003798365648846145868545)
        ·
          refine ⟨5252848774236634609401409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7003798365648846145868545 5252848774236634609401409)
          ·
            refine ⟨3939636580677475957051057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5252848774236634609401409 3939636580677475957051057)
            ·
              refine ⟨2954727435508106967788293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3939636580677475957051057 2954727435508106967788293)
              ·
                refine ⟨554011394157770056460305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2954727435508106967788293 554011394157770056460305)
                ·
                  refine ⟨415508545618327542345229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 554011394157770056460305 415508545618327542345229)
                  ·
                    rfl

theorem cell20_910350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 4, 2].length) (baseStart_910350 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_910350 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_910350 prefixEnd_910350 := by exact prefixLift 910350
  have htrace : WordTrace (prefixWord ++ tailWord_910350) baseStart_910350 baseEnd_910350 := by
    simpa [prefixWord, tailWord_910350, baseEnd_910350] using wordTrace_append hprefix tailTrace_910350
  have hstable : (prefixWord ++ tailWord_910350).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910350).length < 2 ^ (prefixWord ++ tailWord_910350).sum := by decide
  have hdescent : baseEnd_910350 < baseStart_910350 := by decide
  rcases family_descends (prefixWord ++ tailWord_910350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910437 : List Nat := [1, 3, 1, 3, 2, 1, 1, 8]
def baseStart_910437 : Nat := 118140960795 + 910437 * 2 ^ 59
def prefixEnd_910437 : Nat := 4983230072969 + 3 ^ 40 * 910437 * 2
def baseEnd_910437 : Nat := 138516084929647302148291

theorem tailTrace_910437 : CollatzResearch.WordTrace tailWord_910437 prefixEnd_910437 138516084929647302148291 := by
  unfold tailWord_910437
  simp only [CollatzResearch.WordTrace]
  refine ⟨33206365402649714105497565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22137576935099809403665043 33206365402649714105497565)
  ·
    refine ⟨12452387025993642789561587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33206365402649714105497565 12452387025993642789561587)
    ·
      refine ⟨18678580538990464184342381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12452387025993642789561587 18678580538990464184342381)
      ·
        refine ⟨7004467702121424069128393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18678580538990464184342381 7004467702121424069128393)
        ·
          refine ⟨5253350776591068051846295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7004467702121424069128393 5253350776591068051846295)
          ·
            refine ⟨7880026164886602077769443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5253350776591068051846295 7880026164886602077769443)
            ·
              refine ⟨11820039247329903116654165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7880026164886602077769443 11820039247329903116654165)
              ·
                refine ⟨138516084929647302148291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11820039247329903116654165 138516084929647302148291)
                ·
                  rfl

theorem cell20_910437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 8].length) (baseStart_910437 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_910437 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_910437 prefixEnd_910437 := by exact prefixLift 910437
  have htrace : WordTrace (prefixWord ++ tailWord_910437) baseStart_910437 baseEnd_910437 := by
    simpa [prefixWord, tailWord_910437, baseEnd_910437] using wordTrace_append hprefix tailTrace_910437
  have hstable : (prefixWord ++ tailWord_910437).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910437).length < 2 ^ (prefixWord ++ tailWord_910437).sum := by decide
  have hdescent : baseEnd_910437 < baseStart_910437 := by decide
  rcases family_descends (prefixWord ++ tailWord_910437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910447 : List Nat := [1, 1, 2, 1, 3, 3, 2, 5, 2]
def baseStart_910447 : Nat := 118140960795 + 910447 * 2 ^ 59
def prefixEnd_910447 : Nat := 4983230072969 + 3 ^ 40 * 910447 * 2
def baseEnd_910447 : Nat := 415552819061426316111499

theorem tailTrace_910447 : CollatzResearch.WordTrace tailWord_910447 prefixEnd_910447 415552819061426316111499 := by
  unfold tailWord_910447
  simp only [CollatzResearch.WordTrace]
  refine ⟨33206730132613485813361595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22137820088408990542241063 33206730132613485813361595)
  ·
    refine ⟨49810095198920228720042393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33206730132613485813361595 49810095198920228720042393)
    ·
      refine ⟨37357571399190171540031795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49810095198920228720042393 37357571399190171540031795)
      ·
        refine ⟨56036357098785257310047693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37357571399190171540031795 56036357098785257310047693)
        ·
          refine ⟨21013633912044471491267885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56036357098785257310047693 21013633912044471491267885)
          ·
            refine ⟨7880112717016676809225457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21013633912044471491267885 7880112717016676809225457)
            ·
              refine ⟨5910084537762507606919093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7880112717016676809225457 5910084537762507606919093)
              ·
                refine ⟨554070425415235088148665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5910084537762507606919093 554070425415235088148665)
                ·
                  refine ⟨415552819061426316111499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 554070425415235088148665 415552819061426316111499)
                  ·
                    rfl

theorem cell20_910447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 5, 2].length) (baseStart_910447 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_910447 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_910447 prefixEnd_910447 := by exact prefixLift 910447
  have htrace : WordTrace (prefixWord ++ tailWord_910447) baseStart_910447 baseEnd_910447 := by
    simpa [prefixWord, tailWord_910447, baseEnd_910447] using wordTrace_append hprefix tailTrace_910447
  have hstable : (prefixWord ++ tailWord_910447).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910447).length < 2 ^ (prefixWord ++ tailWord_910447).sum := by decide
  have hdescent : baseEnd_910447 < baseStart_910447 := by decide
  rcases family_descends (prefixWord ++ tailWord_910447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910464 : List Nat := [2, 1, 1, 2, 1, 3, 6, 2, 2]
def baseStart_910464 : Nat := 118140960795 + 910464 * 2 ^ 59
def prefixEnd_910464 : Nat := 4983230072969 + 3 ^ 40 * 910464 * 2
def baseEnd_910464 : Nat := 415560578324649812544763

theorem tailTrace_910464 : CollatzResearch.WordTrace tailWord_910464 prefixEnd_910464 415560578324649812544763 := by
  unfold tailWord_910464
  simp only [CollatzResearch.WordTrace]
  refine ⟨16603675086775948858365223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22138233449034598477820297 16603675086775948858365223)
  ·
    refine ⟨24905512630163923287547835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16603675086775948858365223 24905512630163923287547835)
    ·
      refine ⟨37358268945245884931321753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24905512630163923287547835 37358268945245884931321753)
      ·
        refine ⟨28018701708934413698491315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37358268945245884931321753 28018701708934413698491315)
        ·
          refine ⟨42028052563401620547736973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28018701708934413698491315 42028052563401620547736973)
          ·
            refine ⟨15760519711275607705401365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42028052563401620547736973 15760519711275607705401365)
            ·
              refine ⟨738774361466044111190689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 15760519711275607705401365 738774361466044111190689)
              ·
                refine ⟨554080771099533083393017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 738774361466044111190689 554080771099533083393017)
                ·
                  refine ⟨415560578324649812544763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 554080771099533083393017 415560578324649812544763)
                  ·
                    rfl

theorem cell20_910464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 6, 2, 2].length) (baseStart_910464 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_910464 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_910464 prefixEnd_910464 := by exact prefixLift 910464
  have htrace : WordTrace (prefixWord ++ tailWord_910464) baseStart_910464 baseEnd_910464 := by
    simpa [prefixWord, tailWord_910464, baseEnd_910464] using wordTrace_append hprefix tailTrace_910464
  have hstable : (prefixWord ++ tailWord_910464).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910464).length < 2 ^ (prefixWord ++ tailWord_910464).sum := by decide
  have hdescent : baseEnd_910464 < baseStart_910464 := by decide
  rcases family_descends (prefixWord ++ tailWord_910464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910478 : List Nat := [4, 1, 1, 3, 2, 1, 2, 3, 3]
def baseStart_910478 : Nat := 118140960795 + 910478 * 2 ^ 59
def prefixEnd_910478 : Nat := 4983230072969 + 3 ^ 40 * 910478 * 2
def baseEnd_910478 : Nat := 415566968306127986078039

theorem tailTrace_910478 : CollatzResearch.WordTrace tailWord_910478 prefixEnd_910478 415566968306127986078039 := by
  unfold tailWord_910478
  simp only [CollatzResearch.WordTrace]
  refine ⟨4150982599437647263467511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22138573863667452071826725 4150982599437647263467511)
  ·
    refine ⟨6226473899156470895201267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4150982599437647263467511 6226473899156470895201267)
    ·
      refine ⟨9339710848734706342801901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6226473899156470895201267 9339710848734706342801901)
      ·
        refine ⟨3502391568275514878550713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9339710848734706342801901 3502391568275514878550713)
        ·
          refine ⟨2626793676206636158913035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3502391568275514878550713 2626793676206636158913035)
          ·
            refine ⟨3940190514309954238369553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2626793676206636158913035 3940190514309954238369553)
            ·
              refine ⟨2955142885732465678777165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3940190514309954238369553 2955142885732465678777165)
              ·
                refine ⟨1108178582149674629541437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2955142885732465678777165 1108178582149674629541437)
                ·
                  refine ⟨415566968306127986078039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1108178582149674629541437 415566968306127986078039)
                  ·
                    rfl

theorem cell20_910478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 3, 3].length) (baseStart_910478 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_910478 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_910478 prefixEnd_910478 := by exact prefixLift 910478
  have htrace : WordTrace (prefixWord ++ tailWord_910478) baseStart_910478 baseEnd_910478 := by
    simpa [prefixWord, tailWord_910478, baseEnd_910478] using wordTrace_append hprefix tailTrace_910478
  have hstable : (prefixWord ++ tailWord_910478).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910478).length < 2 ^ (prefixWord ++ tailWord_910478).sum := by decide
  have hdescent : baseEnd_910478 < baseStart_910478 := by decide
  rcases family_descends (prefixWord ++ tailWord_910478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910578 : List Nat := [3, 2, 1, 3, 3, 2, 1, 1, 4]
def baseStart_910578 : Nat := 118140960795 + 910578 * 2 ^ 59
def prefixEnd_910578 : Nat := 4983230072969 + 3 ^ 40 * 910578 * 2
def baseEnd_910578 : Nat := 415612611030972082744297

theorem tailTrace_910578 : CollatzResearch.WordTrace tailWord_910578 prefixEnd_910578 415612611030972082744297 := by
  unfold tailWord_910578
  simp only [CollatzResearch.WordTrace]
  refine ⟨8302877023784723796595097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22141005396759263457586925 8302877023784723796595097)
  ·
    refine ⟨6227157767838542847446323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8302877023784723796595097 6227157767838542847446323)
    ·
      refine ⟨9340736651757814271169485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6227157767838542847446323 9340736651757814271169485)
      ·
        refine ⟨3502776244409180351688557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9340736651757814271169485 3502776244409180351688557)
        ·
          refine ⟨1313541091653442631883209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3502776244409180351688557 1313541091653442631883209)
          ·
            refine ⟨985155818740081973912407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1313541091653442631883209 985155818740081973912407)
            ·
              refine ⟨1477733728110122960868611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 985155818740081973912407 1477733728110122960868611)
              ·
                refine ⟨2216600592165184441302917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1477733728110122960868611 2216600592165184441302917)
                ·
                  refine ⟨415612611030972082744297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2216600592165184441302917 415612611030972082744297)
                  ·
                    rfl

theorem cell20_910578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 1, 1, 4].length) (baseStart_910578 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_910578 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_910578 prefixEnd_910578 := by exact prefixLift 910578
  have htrace : WordTrace (prefixWord ++ tailWord_910578) baseStart_910578 baseEnd_910578 := by
    simpa [prefixWord, tailWord_910578, baseEnd_910578] using wordTrace_append hprefix tailTrace_910578
  have hstable : (prefixWord ++ tailWord_910578).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910578).length < 2 ^ (prefixWord ++ tailWord_910578).sum := by decide
  have hdescent : baseEnd_910578 < baseStart_910578 := by decide
  rcases family_descends (prefixWord ++ tailWord_910578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910588 : List Nat := [2, 2, 2, 1, 6, 1, 2, 1, 3]
def baseStart_910588 : Nat := 118140960795 + 910588 * 2 ^ 59
def prefixEnd_910588 : Nat := 4983230072969 + 3 ^ 40 * 910588 * 2
def baseEnd_910588 : Nat := 415617175303456492410923

theorem tailTrace_910588 : CollatzResearch.WordTrace tailWord_910588 prefixEnd_910588 415617175303456492410923 := by
  unfold tailWord_910588
  simp only [CollatzResearch.WordTrace]
  refine ⟨16605936412551333447122209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22141248550068444596162945 16605936412551333447122209)
  ·
    refine ⟨12454452309413500085341657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16605936412551333447122209 12454452309413500085341657)
    ·
      refine ⟨9340839232060125064006243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12454452309413500085341657 9340839232060125064006243)
      ·
        refine ⟨14011258848090187596009365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9340839232060125064006243 14011258848090187596009365)
        ·
          refine ⟨656777758504227543562939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 14011258848090187596009365 656777758504227543562939)
          ·
            refine ⟨985166637756341315344409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 656777758504227543562939 985166637756341315344409)
            ·
              refine ⟨738874978317255986508307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 985166637756341315344409 738874978317255986508307)
              ·
                refine ⟨1108312467475883979762461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 738874978317255986508307 1108312467475883979762461)
                ·
                  refine ⟨415617175303456492410923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1108312467475883979762461 415617175303456492410923)
                  ·
                    rfl

theorem cell20_910588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 2, 1, 3].length) (baseStart_910588 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_910588 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_910588 prefixEnd_910588 := by exact prefixLift 910588
  have htrace : WordTrace (prefixWord ++ tailWord_910588) baseStart_910588 baseEnd_910588 := by
    simpa [prefixWord, tailWord_910588, baseEnd_910588] using wordTrace_append hprefix tailTrace_910588
  have hstable : (prefixWord ++ tailWord_910588).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910588).length < 2 ^ (prefixWord ++ tailWord_910588).sum := by decide
  have hdescent : baseEnd_910588 < baseStart_910588 := by decide
  rcases family_descends (prefixWord ++ tailWord_910588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910672 : List Nat := [2, 1, 1, 1, 1, 5, 2, 2, 5]
def baseStart_910672 : Nat := 118140960795 + 910672 * 2 ^ 59
def prefixEnd_910672 : Nat := 4983230072969 + 3 ^ 40 * 910672 * 2
def baseEnd_910672 : Nat := 415655515192325533610579

theorem tailTrace_910672 : CollatzResearch.WordTrace tailWord_910672 prefixEnd_910672 415655515192325533610579 := by
  unfold tailWord_910672
  simp only [CollatzResearch.WordTrace]
  refine ⟨16607468278399174620151135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22143291037865566160201513 16607468278399174620151135)
  ·
    refine ⟨24911202417598761930226703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16607468278399174620151135 24911202417598761930226703)
    ·
      refine ⟨37366803626398142895340055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24911202417598761930226703 37366803626398142895340055)
      ·
        refine ⟨56050205439597214343010083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37366803626398142895340055 56050205439597214343010083)
        ·
          refine ⟨84075308159395821514515125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56050205439597214343010083 84075308159395821514515125)
          ·
            refine ⟨7882060139943358266985793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 84075308159395821514515125 7882060139943358266985793)
            ·
              refine ⟨5911545104957518700239345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7882060139943358266985793 5911545104957518700239345)
              ·
                refine ⟨4433658828718139025179509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5911545104957518700239345 4433658828718139025179509)
                ·
                  refine ⟨415655515192325533610579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4433658828718139025179509 415655515192325533610579)
                  ·
                    rfl

theorem cell20_910672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 2, 5].length) (baseStart_910672 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_910672 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_910672 prefixEnd_910672 := by exact prefixLift 910672
  have htrace : WordTrace (prefixWord ++ tailWord_910672) baseStart_910672 baseEnd_910672 := by
    simpa [prefixWord, tailWord_910672, baseEnd_910672] using wordTrace_append hprefix tailTrace_910672
  have hstable : (prefixWord ++ tailWord_910672).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910672).length < 2 ^ (prefixWord ++ tailWord_910672).sum := by decide
  have hdescent : baseEnd_910672 < baseStart_910672 := by decide
  rcases family_descends (prefixWord ++ tailWord_910672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910675 : List Nat := [1, 1, 1, 2, 1, 1, 8, 3, 2]
def baseStart_910675 : Nat := 118140960795 + 910675 * 2 ^ 59
def prefixEnd_910675 : Nat := 4983230072969 + 3 ^ 40 * 910675 * 2
def baseEnd_910675 : Nat := 415656884474070856510567

theorem tailTrace_910675 : CollatzResearch.WordTrace tailWord_910675 prefixEnd_910675 415656884474070856510567 := by
  unfold tailWord_910675
  simp only [CollatzResearch.WordTrace]
  refine ⟨33215045975787480752661479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22143363983858320501774319 33215045975787480752661479)
  ·
    refine ⟨49822568963681221128992219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33215045975787480752661479 49822568963681221128992219)
    ·
      refine ⟨74733853445521831693488329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49822568963681221128992219 74733853445521831693488329)
      ·
        refine ⟨56050390084141373770116247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74733853445521831693488329 56050390084141373770116247)
        ·
          refine ⟨84075585126212060655174371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56050390084141373770116247 84075585126212060655174371)
          ·
            refine ⟨126113377689318090982761557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84075585126212060655174371 126113377689318090982761557)
            ·
              refine ⟨1477891144796696378704237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 126113377689318090982761557 1477891144796696378704237)
              ·
                refine ⟨554209179298761142014089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1477891144796696378704237 554209179298761142014089)
                ·
                  refine ⟨415656884474070856510567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 554209179298761142014089 415656884474070856510567)
                  ·
                    rfl

theorem cell20_910675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 8, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 8, 3, 2].length) (baseStart_910675 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_910675 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_910675 prefixEnd_910675 := by exact prefixLift 910675
  have htrace : WordTrace (prefixWord ++ tailWord_910675) baseStart_910675 baseEnd_910675 := by
    simpa [prefixWord, tailWord_910675, baseEnd_910675] using wordTrace_append hprefix tailTrace_910675
  have hstable : (prefixWord ++ tailWord_910675).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910675).length < 2 ^ (prefixWord ++ tailWord_910675).sum := by decide
  have hdescent : baseEnd_910675 < baseStart_910675 := by decide
  rcases family_descends (prefixWord ++ tailWord_910675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910702 : List Nat := [4, 1, 2, 4, 1, 1, 3, 1, 3]
def baseStart_910702 : Nat := 118140960795 + 910702 * 2 ^ 59
def prefixEnd_910702 : Nat := 4983230072969 + 3 ^ 40 * 910702 * 2
def baseEnd_910702 : Nat := 415669208009778762610457

theorem tailTrace_910702 : CollatzResearch.WordTrace tailWord_910702 prefixEnd_910702 415669208009778762610457 := by
  unfold tailWord_910702
  simp only [CollatzResearch.WordTrace]
  refine ⟨4152003843336208045486795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22144020497793109575929573 4152003843336208045486795)
  ·
    refine ⟨6228005765004312068230193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4152003843336208045486795 6228005765004312068230193)
    ·
      refine ⟨4671004323753234051172645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6228005765004312068230193 4671004323753234051172645)
      ·
        refine ⟨875813310703731384594871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4671004323753234051172645 875813310703731384594871)
        ·
          refine ⟨1313719966055597076892307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 875813310703731384594871 1313719966055597076892307)
          ·
            refine ⟨1970579949083395615338461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1313719966055597076892307 1970579949083395615338461)
            ·
              refine ⟨738967480906273355751923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1970579949083395615338461 738967480906273355751923)
              ·
                refine ⟨1108451221359410033627885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 738967480906273355751923 1108451221359410033627885)
                ·
                  refine ⟨415669208009778762610457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1108451221359410033627885 415669208009778762610457)
                  ·
                    rfl

theorem cell20_910702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 3, 1, 3].length) (baseStart_910702 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_910702 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_910702 prefixEnd_910702 := by exact prefixLift 910702
  have htrace : WordTrace (prefixWord ++ tailWord_910702) baseStart_910702 baseEnd_910702 := by
    simpa [prefixWord, tailWord_910702, baseEnd_910702] using wordTrace_append hprefix tailTrace_910702
  have hstable : (prefixWord ++ tailWord_910702).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910702).length < 2 ^ (prefixWord ++ tailWord_910702).sum := by decide
  have hdescent : baseEnd_910702 < baseStart_910702 := by decide
  rcases family_descends (prefixWord ++ tailWord_910702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910706 : List Nat := [3, 2, 1, 2, 1, 2, 5, 1, 3]
def baseStart_910706 : Nat := 118140960795 + 910706 * 2 ^ 59
def prefixEnd_910706 : Nat := 4983230072969 + 3 ^ 40 * 910706 * 2
def baseEnd_910706 : Nat := 415671033718772526477107

theorem tailTrace_910706 : CollatzResearch.WordTrace tailWord_910706 prefixEnd_910706 415671033718772526477107 := by
  unfold tailWord_910706
  simp only [CollatzResearch.WordTrace]
  refine ⟨8304044159668793261759993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22144117759116782031359981 8304044159668793261759993)
  ·
    refine ⟨6228033119751594946319995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8304044159668793261759993 6228033119751594946319995)
    ·
      refine ⟨9342049679627392419479993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6228033119751594946319995 9342049679627392419479993)
      ·
        refine ⟨7006537259720544314609995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9342049679627392419479993 7006537259720544314609995)
        ·
          refine ⟨10509805889580816471914993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7006537259720544314609995 10509805889580816471914993)
          ·
            refine ⟨7882354417185612353936245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10509805889580816471914993 7882354417185612353936245)
            ·
              refine ⟨738970726611151158181523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7882354417185612353936245 738970726611151158181523)
              ·
                refine ⟨1108456089916726737272285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 738970726611151158181523 1108456089916726737272285)
                ·
                  refine ⟨415671033718772526477107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1108456089916726737272285 415671033718772526477107)
                  ·
                    rfl

theorem cell20_910706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 5, 1, 3].length) (baseStart_910706 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_910706 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_910706 prefixEnd_910706 := by exact prefixLift 910706
  have htrace : WordTrace (prefixWord ++ tailWord_910706) baseStart_910706 baseEnd_910706 := by
    simpa [prefixWord, tailWord_910706, baseEnd_910706] using wordTrace_append hprefix tailTrace_910706
  have hstable : (prefixWord ++ tailWord_910706).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910706).length < 2 ^ (prefixWord ++ tailWord_910706).sum := by decide
  have hdescent : baseEnd_910706 < baseStart_910706 := by decide
  rcases family_descends (prefixWord ++ tailWord_910706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910751 : List Nat := [1, 1, 2, 5, 1, 4, 1, 1, 4]
def baseStart_910751 : Nat := 118140960795 + 910751 * 2 ^ 59
def prefixEnd_910751 : Nat := 4983230072969 + 3 ^ 40 * 910751 * 2
def baseEnd_910751 : Nat := 415691572944952369976923

theorem tailTrace_910751 : CollatzResearch.WordTrace tailWord_910751 prefixEnd_910751 415691572944952369976923 := by
  unfold tailWord_910751
  simp only [CollatzResearch.WordTrace]
  refine ⟨33217817923512145732428107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22145211949008097154952071 33217817923512145732428107)
  ·
    refine ⟨49826726885268218598642161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33217817923512145732428107 49826726885268218598642161)
    ·
      refine ⟨37370045163951163948981621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49826726885268218598642161 37370045163951163948981621)
      ·
        refine ⟨3503441734120421620217027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37370045163951163948981621 3503441734120421620217027)
        ·
          refine ⟨5255162601180632430325541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3503441734120421620217027 5255162601180632430325541)
          ·
            refine ⟨985342987721368580686039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5255162601180632430325541 985342987721368580686039)
            ·
              refine ⟨1478014481582052871029059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 985342987721368580686039 1478014481582052871029059)
              ·
                refine ⟨2217021722373079306543589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1478014481582052871029059 2217021722373079306543589)
                ·
                  refine ⟨415691572944952369976923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2217021722373079306543589 415691572944952369976923)
                  ·
                    rfl

theorem cell20_910751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 1, 1, 4].length) (baseStart_910751 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_910751 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_910751 prefixEnd_910751 := by exact prefixLift 910751
  have htrace : WordTrace (prefixWord ++ tailWord_910751) baseStart_910751 baseEnd_910751 := by
    simpa [prefixWord, tailWord_910751, baseEnd_910751] using wordTrace_append hprefix tailTrace_910751
  have hstable : (prefixWord ++ tailWord_910751).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910751).length < 2 ^ (prefixWord ++ tailWord_910751).sum := by decide
  have hdescent : baseEnd_910751 < baseStart_910751 := by decide
  rcases family_descends (prefixWord ++ tailWord_910751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910817 : List Nat := [1, 2, 3, 1, 2, 3, 3, 5]
def baseStart_910817 : Nat := 118140960795 + 910817 * 2 ^ 59
def prefixEnd_910817 : Nat := 4983230072969 + 3 ^ 40 * 910817 * 2
def baseEnd_910817 : Nat := 138573899047783157925551

theorem tailTrace_910817 : CollatzResearch.WordTrace tailWord_910817 prefixEnd_910817 138573899047783157925551 := by
  unfold tailWord_910817
  simp only [CollatzResearch.WordTrace]
  refine ⟨33220225141273039004330705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22146816760848692669553803 33220225141273039004330705)
  ·
    refine ⟨24915168855954779253248029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33220225141273039004330705 24915168855954779253248029)
    ·
      refine ⟨9343188320983042219968011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24915168855954779253248029 9343188320983042219968011)
      ·
        refine ⟨14014782481474563329952017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9343188320983042219968011 14014782481474563329952017)
        ·
          refine ⟨10511086861105922497464013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14014782481474563329952017 10511086861105922497464013)
          ·
            refine ⟨3941657572914720936549005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10511086861105922497464013 3941657572914720936549005)
            ·
              refine ⟨1478121589843020351205877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3941657572914720936549005 1478121589843020351205877)
              ·
                refine ⟨138573899047783157925551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1478121589843020351205877 138573899047783157925551)
                ·
                  rfl

theorem cell20_910817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 3, 5].length) (baseStart_910817 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_910817 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_910817 prefixEnd_910817 := by exact prefixLift 910817
  have htrace : WordTrace (prefixWord ++ tailWord_910817) baseStart_910817 baseEnd_910817 := by
    simpa [prefixWord, tailWord_910817, baseEnd_910817] using wordTrace_append hprefix tailTrace_910817
  have hstable : (prefixWord ++ tailWord_910817).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910817).length < 2 ^ (prefixWord ++ tailWord_910817).sum := by decide
  have hdescent : baseEnd_910817 < baseStart_910817 := by decide
  rcases family_descends (prefixWord ++ tailWord_910817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910831 : List Nat := [1, 1, 2, 1, 4, 1, 3, 1, 6]
def baseStart_910831 : Nat := 118140960795 + 910831 * 2 ^ 59
def prefixEnd_910831 : Nat := 4983230072969 + 3 ^ 40 * 910831 * 2
def baseEnd_910831 : Nat := 415728087124827647309929

theorem tailTrace_910831 : CollatzResearch.WordTrace tailWord_910831 prefixEnd_910831 415728087124827647309929 := by
  unfold tailWord_910831
  simp only [CollatzResearch.WordTrace]
  refine ⟨33220735763222319395340347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22147157175481546263560231 33220735763222319395340347)
  ·
    refine ⟨49831103644833479093010521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33220735763222319395340347 49831103644833479093010521)
    ·
      refine ⟨37373327733625109319757891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49831103644833479093010521 37373327733625109319757891)
      ·
        refine ⟨56059991600437663979636837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37373327733625109319757891 56059991600437663979636837)
        ·
          refine ⟨10511248425082061996181907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56059991600437663979636837 10511248425082061996181907)
          ·
            refine ⟨15766872637623092994272861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10511248425082061996181907 15766872637623092994272861)
            ·
              refine ⟨5912577239108659872852323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15766872637623092994272861 5912577239108659872852323)
              ·
                refine ⟨8868865858662989809278485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5912577239108659872852323 8868865858662989809278485)
                ·
                  refine ⟨415728087124827647309929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8868865858662989809278485 415728087124827647309929)
                  ·
                    rfl

theorem cell20_910831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 1, 6].length) (baseStart_910831 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_910831 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_910831 prefixEnd_910831 := by exact prefixLift 910831
  have htrace : WordTrace (prefixWord ++ tailWord_910831) baseStart_910831 baseEnd_910831 := by
    simpa [prefixWord, tailWord_910831, baseEnd_910831] using wordTrace_append hprefix tailTrace_910831
  have hstable : (prefixWord ++ tailWord_910831).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910831).length < 2 ^ (prefixWord ++ tailWord_910831).sum := by decide
  have hdescent : baseEnd_910831 < baseStart_910831 := by decide
  rcases family_descends (prefixWord ++ tailWord_910831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910854 : List Nat := [6, 2, 1, 1, 2, 1, 1, 1, 5]
def baseStart_910854 : Nat := 118140960795 + 910854 * 2 ^ 59
def prefixEnd_910854 : Nat := 4983230072969 + 3 ^ 40 * 910854 * 2
def baseEnd_910854 : Nat := 415738584951541789543169

theorem tailTrace_910854 : CollatzResearch.WordTrace tailWord_910854 prefixEnd_910854 415738584951541789543169 := by
  unfold tailWord_910854
  simp only [CollatzResearch.WordTrace]
  refine ⟨1038174207566843572607113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 22147716428092662882285077 1038174207566843572607113)
  ·
    refine ⟨778630655675132679455335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1038174207566843572607113 778630655675132679455335)
    ·
      refine ⟨1167945983512699019183003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 778630655675132679455335 1167945983512699019183003)
      ·
        refine ⟨1751918975269048528774505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1167945983512699019183003 1751918975269048528774505)
        ·
          refine ⟨1313939231451786396580879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1751918975269048528774505 1313939231451786396580879)
          ·
            refine ⟨1970908847177679594871319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1313939231451786396580879 1970908847177679594871319)
            ·
              refine ⟨2956363270766519392306979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1970908847177679594871319 2956363270766519392306979)
              ·
                refine ⟨4434544906149779088460469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2956363270766519392306979 4434544906149779088460469)
                ·
                  refine ⟨415738584951541789543169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4434544906149779088460469 415738584951541789543169)
                  ·
                    rfl

theorem cell20_910854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_910854 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_910854 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_910854 prefixEnd_910854 := by exact prefixLift 910854
  have htrace : WordTrace (prefixWord ++ tailWord_910854) baseStart_910854 baseEnd_910854 := by
    simpa [prefixWord, tailWord_910854, baseEnd_910854] using wordTrace_append hprefix tailTrace_910854
  have hstable : (prefixWord ++ tailWord_910854).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910854).length < 2 ^ (prefixWord ++ tailWord_910854).sum := by decide
  have hdescent : baseEnd_910854 < baseStart_910854 := by decide
  rcases family_descends (prefixWord ++ tailWord_910854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910855 : List Nat := [1, 1, 4, 3, 2, 2, 7]
def baseStart_910855 : Nat := 118140960795 + 910855 * 2 ^ 59
def prefixEnd_910855 : Nat := 4983230072969 + 3 ^ 40 * 910855 * 2
def baseEnd_910855 : Nat := 46193226819865581167759

theorem tailTrace_910855 : CollatzResearch.WordTrace tailWord_910855 prefixEnd_910855 46193226819865581167759 := by
  unfold tailWord_910855
  simp only [CollatzResearch.WordTrace]
  refine ⟨33221611115135371494214019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22147740743423580996142679 33221611115135371494214019)
  ·
    refine ⟨49832416672703057241321029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33221611115135371494214019 49832416672703057241321029)
    ·
      refine ⟨9343578126131823232747693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49832416672703057241321029 9343578126131823232747693)
      ·
        refine ⟨3503841797299433712280385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9343578126131823232747693 3503841797299433712280385)
        ·
          refine ⟨2627881347974575284210289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3503841797299433712280385 2627881347974575284210289)
          ·
            refine ⟨1970911010980931463157717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2627881347974575284210289 1970911010980931463157717)
            ·
              refine ⟨46193226819865581167759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1970911010980931463157717 46193226819865581167759)
              ·
                rfl

theorem cell20_910855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 7].length) (baseStart_910855 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_910855 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_910855 prefixEnd_910855 := by exact prefixLift 910855
  have htrace : WordTrace (prefixWord ++ tailWord_910855) baseStart_910855 baseEnd_910855 := by
    simpa [prefixWord, tailWord_910855, baseEnd_910855] using wordTrace_append hprefix tailTrace_910855
  have hstable : (prefixWord ++ tailWord_910855).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910855).length < 2 ^ (prefixWord ++ tailWord_910855).sum := by decide
  have hdescent : baseEnd_910855 < baseStart_910855 := by decide
  rcases family_descends (prefixWord ++ tailWord_910855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910858 : List Nat := [3, 1, 2, 2, 2, 4, 1, 2, 3]
def baseStart_910858 : Nat := 118140960795 + 910858 * 2 ^ 59
def prefixEnd_910858 : Nat := 4983230072969 + 3 ^ 40 * 910858 * 2
def baseEnd_910858 : Nat := 415740410660535553409819

theorem tailTrace_910858 : CollatzResearch.WordTrace tailWord_910858 prefixEnd_910858 415740410660535553409819 := by
  unfold tailWord_910858
  simp only [CollatzResearch.WordTrace]
  refine ⟨8305430133531125751643307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22147813689416335337715485 8305430133531125751643307)
  ·
    refine ⟨12458145200296688627464961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8305430133531125751643307 12458145200296688627464961)
    ·
      refine ⟨9343608900222516470598721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12458145200296688627464961 9343608900222516470598721)
      ·
        refine ⟨7007706675166887352949041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9343608900222516470598721 7007706675166887352949041)
        ·
          refine ⟨5255780006375165514711781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7007706675166887352949041 5255780006375165514711781)
          ·
            refine ⟨985458751195343534008459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5255780006375165514711781 985458751195343534008459)
            ·
              refine ⟨1478188126793015301012689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 985458751195343534008459 1478188126793015301012689)
              ·
                refine ⟨1108641095094761475759517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1478188126793015301012689 1108641095094761475759517)
                ·
                  refine ⟨415740410660535553409819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1108641095094761475759517 415740410660535553409819)
                  ·
                    rfl

theorem cell20_910858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 1, 2, 3].length) (baseStart_910858 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_910858 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_910858 prefixEnd_910858 := by exact prefixLift 910858
  have htrace : WordTrace (prefixWord ++ tailWord_910858) baseStart_910858 baseEnd_910858 := by
    simpa [prefixWord, tailWord_910858, baseEnd_910858] using wordTrace_append hprefix tailTrace_910858
  have hstable : (prefixWord ++ tailWord_910858).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910858).length < 2 ^ (prefixWord ++ tailWord_910858).sum := by decide
  have hdescent : baseEnd_910858 < baseStart_910858 := by decide
  rcases family_descends (prefixWord ++ tailWord_910858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910861 : List Nat := [1, 7, 1, 1, 2, 1, 2, 1, 4]
def baseStart_910861 : Nat := 118140960795 + 910861 * 2 ^ 59
def prefixEnd_910861 : Nat := 4983230072969 + 3 ^ 40 * 910861 * 2
def baseEnd_910861 : Nat := 415741779942280876309807

theorem tailTrace_910861 : CollatzResearch.WordTrace tailWord_910861 prefixEnd_910861 415741779942280876309807 := by
  unfold tailWord_910861
  simp only [CollatzResearch.WordTrace]
  refine ⟨33221829953113634518932437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22147886635409089679288291 33221829953113634518932437)
  ·
    refine ⟨778636639526100809037479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 33221829953113634518932437 778636639526100809037479)
    ·
      refine ⟨1167954959289151213556219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 778636639526100809037479 1167954959289151213556219)
      ·
        refine ⟨1751932438933726820334329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1167954959289151213556219 1751932438933726820334329)
        ·
          refine ⟨1313949329200295115250747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1751932438933726820334329 1313949329200295115250747)
          ·
            refine ⟨1970923993800442672876121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1313949329200295115250747 1970923993800442672876121)
            ·
              refine ⟨1478192995350332004657091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1970923993800442672876121 1478192995350332004657091)
              ·
                refine ⟨2217289493025498006985637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1478192995350332004657091 2217289493025498006985637)
                ·
                  refine ⟨415741779942280876309807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2217289493025498006985637 415741779942280876309807)
                  ·
                    rfl

theorem cell20_910861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_910861 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_910861 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_910861 prefixEnd_910861 := by exact prefixLift 910861
  have htrace : WordTrace (prefixWord ++ tailWord_910861) baseStart_910861 baseEnd_910861 := by
    simpa [prefixWord, tailWord_910861, baseEnd_910861] using wordTrace_append hprefix tailTrace_910861
  have hstable : (prefixWord ++ tailWord_910861).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910861).length < 2 ^ (prefixWord ++ tailWord_910861).sum := by decide
  have hdescent : baseEnd_910861 < baseStart_910861 := by decide
  rcases family_descends (prefixWord ++ tailWord_910861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910903 : List Nat := [1, 1, 3, 1, 2, 4, 3, 3, 2]
def baseStart_910903 : Nat := 118140960795 + 910903 * 2 ^ 59
def prefixEnd_910903 : Nat := 4983230072969 + 3 ^ 40 * 910903 * 2
def baseEnd_910903 : Nat := 415760949886715396909635

theorem tailTrace_910903 : CollatzResearch.WordTrace tailWord_910903 prefixEnd_910903 415760949886715396909635 := by
  unfold tailWord_910903
  simp only [CollatzResearch.WordTrace]
  refine ⟨33223361818961475691961363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22148907879307650461307575 33223361818961475691961363)
  ·
    refine ⟨49835042728442213537942045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33223361818961475691961363 49835042728442213537942045)
    ·
      refine ⟨18688141023165830076728267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49835042728442213537942045 18688141023165830076728267)
      ·
        refine ⟨28032211534748745115092401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18688141023165830076728267 28032211534748745115092401)
        ·
          refine ⟨21024158651061558836319301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28032211534748745115092401 21024158651061558836319301)
          ·
            refine ⟨3942029747074042281809869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21024158651061558836319301 3942029747074042281809869)
            ·
              refine ⟨1478261155152765855678701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3942029747074042281809869 1478261155152765855678701)
              ·
                refine ⟨554347933182287195879513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1478261155152765855678701 554347933182287195879513)
                ·
                  refine ⟨415760949886715396909635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 554347933182287195879513 415760949886715396909635)
                  ·
                    rfl

theorem cell20_910903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 3, 3, 2].length) (baseStart_910903 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_910903 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_910903 prefixEnd_910903 := by exact prefixLift 910903
  have htrace : WordTrace (prefixWord ++ tailWord_910903) baseStart_910903 baseEnd_910903 := by
    simpa [prefixWord, tailWord_910903, baseEnd_910903] using wordTrace_append hprefix tailTrace_910903
  have hstable : (prefixWord ++ tailWord_910903).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910903).length < 2 ^ (prefixWord ++ tailWord_910903).sum := by decide
  have hdescent : baseEnd_910903 < baseStart_910903 := by decide
  rcases family_descends (prefixWord ++ tailWord_910903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910924 : List Nat := [2, 2, 1, 3, 1, 3, 3, 1, 4]
def baseStart_910924 : Nat := 118140960795 + 910924 * 2 ^ 59
def prefixEnd_910924 : Nat := 4983230072969 + 3 ^ 40 * 910924 * 2
def baseEnd_910924 : Nat := 415770534858932657209549

theorem tailTrace_910924 : CollatzResearch.WordTrace tailWord_910924 prefixEnd_910924 415770534858932657209549 := by
  unfold tailWord_910924
  simp only [CollatzResearch.WordTrace]
  refine ⟨16612063875942698139237913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22149418501256930852317217 16612063875942698139237913)
  ·
    refine ⟨12459047906957023604428435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16612063875942698139237913 12459047906957023604428435)
    ·
      refine ⟨18688571860435535406642653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12459047906957023604428435 18688571860435535406642653)
      ·
        refine ⟨7008214447663325777490995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18688571860435535406642653 7008214447663325777490995)
        ·
          refine ⟨10512321671494988666236493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7008214447663325777490995 10512321671494988666236493)
          ·
            refine ⟨3942120626810620749838685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10512321671494988666236493 3942120626810620749838685)
            ·
              refine ⟨1478295235053982781189507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3942120626810620749838685 1478295235053982781189507)
              ·
                refine ⟨2217442852580974171784261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1478295235053982781189507 2217442852580974171784261)
                ·
                  refine ⟨415770534858932657209549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2217442852580974171784261 415770534858932657209549)
                  ·
                    rfl

theorem cell20_910924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 3, 1, 4].length) (baseStart_910924 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_910924 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_910924 prefixEnd_910924 := by exact prefixLift 910924
  have htrace : WordTrace (prefixWord ++ tailWord_910924) baseStart_910924 baseEnd_910924 := by
    simpa [prefixWord, tailWord_910924, baseEnd_910924] using wordTrace_append hprefix tailTrace_910924
  have hstable : (prefixWord ++ tailWord_910924).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910924).length < 2 ^ (prefixWord ++ tailWord_910924).sum := by decide
  have hdescent : baseEnd_910924 < baseStart_910924 := by decide
  rcases family_descends (prefixWord ++ tailWord_910924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910945 : List Nat := [1, 2, 3, 1, 1, 3, 2, 1, 6]
def baseStart_910945 : Nat := 118140960795 + 910945 * 2 ^ 59
def prefixEnd_910945 : Nat := 4983230072969 + 3 ^ 40 * 910945 * 2
def baseEnd_910945 : Nat := 415780119831149917509463

theorem tailTrace_910945 : CollatzResearch.WordTrace tailWord_910945 prefixEnd_910945 415780119831149917509463 := by
  unfold tailWord_910945
  simp only [CollatzResearch.WordTrace]
  refine ⟨33224893684809316864990289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22149929123206211243326859 33224893684809316864990289)
  ·
    refine ⟨24918670263606987648742717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33224893684809316864990289 24918670263606987648742717)
    ·
      refine ⟨9344501348852620368278519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24918670263606987648742717 9344501348852620368278519)
      ·
        refine ⟨14016752023278930552417779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9344501348852620368278519 14016752023278930552417779)
        ·
          refine ⟨21025128034918395828626669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14016752023278930552417779 21025128034918395828626669)
          ·
            refine ⟨7884423013094398435735001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21025128034918395828626669 7884423013094398435735001)
            ·
              refine ⟨5913317259820798826801251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7884423013094398435735001 5913317259820798826801251)
              ·
                refine ⟨8869975889731198240201877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5913317259820798826801251 8869975889731198240201877)
                ·
                  refine ⟨415780119831149917509463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8869975889731198240201877 415780119831149917509463)
                  ·
                    rfl

theorem cell20_910945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 1, 6].length) (baseStart_910945 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_910945 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_910945 prefixEnd_910945 := by exact prefixLift 910945
  have htrace : WordTrace (prefixWord ++ tailWord_910945) baseStart_910945 baseEnd_910945 := by
    simpa [prefixWord, tailWord_910945, baseEnd_910945] using wordTrace_append hprefix tailTrace_910945
  have hstable : (prefixWord ++ tailWord_910945).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910945).length < 2 ^ (prefixWord ++ tailWord_910945).sum := by decide
  have hdescent : baseEnd_910945 < baseStart_910945 := by decide
  rcases family_descends (prefixWord ++ tailWord_910945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_910986 : List Nat := [3, 1, 2, 3, 2, 3, 1, 5]
def baseStart_910986 : Nat := 118140960795 + 910986 * 2 ^ 59
def prefixEnd_910986 : Nat := 4983230072969 + 3 ^ 40 * 910986 * 2
def baseEnd_910986 : Nat := 138599611116111999047543

theorem tailTrace_910986 : CollatzResearch.WordTrace tailWord_910986 prefixEnd_910986 138599611116111999047543 := by
  unfold tailWord_910986
  simp only [CollatzResearch.WordTrace]
  refine ⟨8306597269415195216808203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22150926051773853911488541 8306597269415195216808203)
  ·
    refine ⟨12459895904122792825212305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8306597269415195216808203 12459895904122792825212305)
    ·
      refine ⟨9344921928092094618909229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12459895904122792825212305 9344921928092094618909229)
      ·
        refine ⟨3504345723034535482090961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9344921928092094618909229 3504345723034535482090961)
        ·
          refine ⟨2628259292275901611568221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3504345723034535482090961 2628259292275901611568221)
          ·
            refine ⟨985597234603463104338083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2628259292275901611568221 985597234603463104338083)
            ·
              refine ⟨1478395851905194656507125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 985597234603463104338083 1478395851905194656507125)
              ·
                refine ⟨138599611116111999047543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1478395851905194656507125 138599611116111999047543)
                ·
                  rfl

theorem cell20_910986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 1, 5].length) (baseStart_910986 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_910986 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_910986 prefixEnd_910986 := by exact prefixLift 910986
  have htrace : WordTrace (prefixWord ++ tailWord_910986) baseStart_910986 baseEnd_910986 := by
    simpa [prefixWord, tailWord_910986, baseEnd_910986] using wordTrace_append hprefix tailTrace_910986
  have hstable : (prefixWord ++ tailWord_910986).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_910986).length < 2 ^ (prefixWord ++ tailWord_910986).sum := by decide
  have hdescent : baseEnd_910986 < baseStart_910986 := by decide
  rcases family_descends (prefixWord ++ tailWord_910986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911000 : List Nat := [2, 1, 2, 4, 1, 3, 1, 2, 4]
def baseStart_911000 : Nat := 118140960795 + 911000 * 2 ^ 59
def prefixEnd_911000 : Nat := 4983230072969 + 3 ^ 40 * 911000 * 2
def baseEnd_911000 : Nat := 415805223329814170675905

theorem tailTrace_911000 : CollatzResearch.WordTrace tailWord_911000 prefixEnd_911000 415805223329814170675905 := by
  unfold tailWord_911000
  simp only [CollatzResearch.WordTrace]
  refine ⟨16613449849805030629121227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22151266466406707505494969 16613449849805030629121227)
  ·
    refine ⟨24920174774707545943681841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16613449849805030629121227 24920174774707545943681841)
    ·
      refine ⟨18690131081030659457761381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24920174774707545943681841 18690131081030659457761381)
      ·
        refine ⟨3504399577693248648330259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18690131081030659457761381 3504399577693248648330259)
        ·
          refine ⟨5256599366539872972495389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3504399577693248648330259 5256599366539872972495389)
          ·
            refine ⟨1971224762452452364685771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5256599366539872972495389 1971224762452452364685771)
            ·
              refine ⟨2956837143678678547028657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1971224762452452364685771 2956837143678678547028657)
              ·
                refine ⟨2217627857759008910271493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2956837143678678547028657 2217627857759008910271493)
                ·
                  refine ⟨415805223329814170675905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2217627857759008910271493 415805223329814170675905)
                  ·
                    rfl

theorem cell20_911000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 2, 4].length) (baseStart_911000 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_911000 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_911000 prefixEnd_911000 := by exact prefixLift 911000
  have htrace : WordTrace (prefixWord ++ tailWord_911000) baseStart_911000 baseEnd_911000 := by
    simpa [prefixWord, tailWord_911000, baseEnd_911000] using wordTrace_append hprefix tailTrace_911000
  have hstable : (prefixWord ++ tailWord_911000).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911000).length < 2 ^ (prefixWord ++ tailWord_911000).sum := by decide
  have hdescent : baseEnd_911000 < baseStart_911000 := by decide
  rcases family_descends (prefixWord ++ tailWord_911000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911031 : List Nat := [1, 1, 3, 1, 5, 1, 3, 2, 3]
def baseStart_911031 : Nat := 118140960795 + 911031 * 2 ^ 59
def prefixEnd_911031 : Nat := 4983230072969 + 3 ^ 40 * 911031 * 2
def baseEnd_911031 : Nat := 415819372574515840642445

theorem tailTrace_911031 : CollatzResearch.WordTrace tailWord_911031 prefixEnd_911031 415819372574515840642445 := by
  unfold tailWord_911031
  simp only [CollatzResearch.WordTrace]
  refine ⟨33228030362497753552620947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22152020241665169035080631 33228030362497753552620947)
  ·
    refine ⟨49842045543746630328931421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33228030362497753552620947 49842045543746630328931421)
    ·
      refine ⟨18690767078904986373349283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49842045543746630328931421 18690767078904986373349283)
      ·
        refine ⟨28036150618357479560023925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18690767078904986373349283 28036150618357479560023925)
        ·
          refine ⟨2628389120471013708752243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28036150618357479560023925 2628389120471013708752243)
          ·
            refine ⟨3942583680706520563128365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2628389120471013708752243 3942583680706520563128365)
            ·
              refine ⟨1478468880264945211173137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3942583680706520563128365 1478468880264945211173137)
              ·
                refine ⟨1108851660198708908379853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1478468880264945211173137 1108851660198708908379853)
                ·
                  refine ⟨415819372574515840642445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1108851660198708908379853 415819372574515840642445)
                  ·
                    rfl

theorem cell20_911031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 3, 2, 3].length) (baseStart_911031 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_911031 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_911031 prefixEnd_911031 := by exact prefixLift 911031
  have htrace : WordTrace (prefixWord ++ tailWord_911031) baseStart_911031 baseEnd_911031 := by
    simpa [prefixWord, tailWord_911031, baseEnd_911031] using wordTrace_append hprefix tailTrace_911031
  have hstable : (prefixWord ++ tailWord_911031).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911031).length < 2 ^ (prefixWord ++ tailWord_911031).sum := by decide
  have hdescent : baseEnd_911031 < baseStart_911031 := by decide
  rcases family_descends (prefixWord ++ tailWord_911031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911038 : List Nat := [4, 2, 1, 1, 2, 2, 1, 3, 4]
def baseStart_911038 : Nat := 118140960795 + 911038 * 2 ^ 59
def prefixEnd_911038 : Nat := 4983230072969 + 3 ^ 40 * 911038 * 2
def baseEnd_911038 : Nat := 415822567565254927409083

theorem tailTrace_911038 : CollatzResearch.WordTrace tailWord_911038 prefixEnd_911038 415822567565254927409083 := by
  unfold tailWord_911038
  simp only [CollatzResearch.WordTrace]
  refine ⟨4153535709184049218515721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22152190448981595832083845 4153535709184049218515721)
  ·
    refine ⟨3115151781888036913886791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4153535709184049218515721 3115151781888036913886791)
    ·
      refine ⟨4672727672832055370830187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3115151781888036913886791 4672727672832055370830187)
      ·
        refine ⟨7009091509248083056245281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4672727672832055370830187 7009091509248083056245281)
        ·
          refine ⟨5256818631936062292183961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7009091509248083056245281 5256818631936062292183961)
          ·
            refine ⟨3942613973952046719137971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5256818631936062292183961 3942613973952046719137971)
            ·
              refine ⟨5913920960928070078706957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3942613973952046719137971 5913920960928070078706957)
              ·
                refine ⟨2217720360348026279515109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5913920960928070078706957 2217720360348026279515109)
                ·
                  refine ⟨415822567565254927409083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2217720360348026279515109 415822567565254927409083)
                  ·
                    rfl

theorem cell20_911038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_911038 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_911038 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_911038 prefixEnd_911038 := by exact prefixLift 911038
  have htrace : WordTrace (prefixWord ++ tailWord_911038) baseStart_911038 baseEnd_911038 := by
    simpa [prefixWord, tailWord_911038, baseEnd_911038] using wordTrace_append hprefix tailTrace_911038
  have hstable : (prefixWord ++ tailWord_911038).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911038).length < 2 ^ (prefixWord ++ tailWord_911038).sum := by decide
  have hdescent : baseEnd_911038 < baseStart_911038 := by decide
  rcases family_descends (prefixWord ++ tailWord_911038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911068 : List Nat := [2, 2, 5, 1, 3, 1, 1, 3, 2]
def baseStart_911068 : Nat := 118140960795 + 911068 * 2 ^ 59
def prefixEnd_911068 : Nat := 4983230072969 + 3 ^ 40 * 911068 * 2
def baseEnd_911068 : Nat := 415836260382708156408961

theorem tailTrace_911068 : CollatzResearch.WordTrace tailWord_911068 prefixEnd_911068 415836260382708156408961 := by
  unfold tailWord_911068
  simp only [CollatzResearch.WordTrace]
  refine ⟨16614689931681854435858929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22152919908909139247811905 16614689931681854435858929)
  ·
    refine ⟨12461017448761390826894197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16614689931681854435858929 12461017448761390826894197)
    ·
      refine ⟨1168220385821380390021331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12461017448761390826894197 1168220385821380390021331)
      ·
        refine ⟨1752330578732070585031997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1168220385821380390021331 1752330578732070585031997)
        ·
          refine ⟨657123967024526469386999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1752330578732070585031997 657123967024526469386999)
          ·
            refine ⟨985685950536789704080499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 657123967024526469386999 985685950536789704080499)
            ·
              refine ⟨1478528925805184556120749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 985685950536789704080499 1478528925805184556120749)
              ·
                refine ⟨554448347176944208545281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1478528925805184556120749 554448347176944208545281)
                ·
                  refine ⟨415836260382708156408961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 554448347176944208545281 415836260382708156408961)
                  ·
                    rfl

theorem cell20_911068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 1, 3, 2].length) (baseStart_911068 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_911068 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_911068 prefixEnd_911068 := by exact prefixLift 911068
  have htrace : WordTrace (prefixWord ++ tailWord_911068) baseStart_911068 baseEnd_911068 := by
    simpa [prefixWord, tailWord_911068, baseEnd_911068] using wordTrace_append hprefix tailTrace_911068
  have hstable : (prefixWord ++ tailWord_911068).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911068).length < 2 ^ (prefixWord ++ tailWord_911068).sum := by decide
  have hdescent : baseEnd_911068 < baseStart_911068 := by decide
  rcases family_descends (prefixWord ++ tailWord_911068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911079 : List Nat := [1, 1, 5, 4, 2, 1, 6]
def baseStart_911079 : Nat := 118140960795 + 911079 * 2 ^ 59
def prefixEnd_911079 : Nat := 4983230072969 + 3 ^ 40 * 911079 * 2
def baseEnd_911079 : Nat := 46204586786937889671361

theorem tailTrace_911079 : CollatzResearch.WordTrace tailWord_911079 prefixEnd_911079 46204586786937889671361 := by
  unfold tailWord_911079
  simp only [CollatzResearch.WordTrace]
  refine ⟨33229781066323857750368291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22153187377549238500245527 33229781066323857750368291)
  ·
    refine ⟨49844671599485786625552437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33229781066323857750368291 49844671599485786625552437)
    ·
      refine ⟨4672937962451792496145541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 49844671599485786625552437 4672937962451792496145541)
      ·
        refine ⟨876175867959711093027289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4672937962451792496145541 876175867959711093027289)
        ·
          refine ⟨657131900969783319770467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 876175867959711093027289 657131900969783319770467)
          ·
            refine ⟨985697851454674979655701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 657131900969783319770467 985697851454674979655701)
            ·
              refine ⟨46204586786937889671361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 985697851454674979655701 46204586786937889671361)
              ·
                rfl

theorem cell20_911079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 6].length) (baseStart_911079 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_911079 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_911079 prefixEnd_911079 := by exact prefixLift 911079
  have htrace : WordTrace (prefixWord ++ tailWord_911079) baseStart_911079 baseEnd_911079 := by
    simpa [prefixWord, tailWord_911079, baseEnd_911079] using wordTrace_append hprefix tailTrace_911079
  have hstable : (prefixWord ++ tailWord_911079).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911079).length < 2 ^ (prefixWord ++ tailWord_911079).sum := by decide
  have hdescent : baseEnd_911079 < baseStart_911079 := by decide
  rcases family_descends (prefixWord ++ tailWord_911079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911090 : List Nat := [3, 2, 1, 3, 1, 1, 1, 3, 5]
def baseStart_911090 : Nat := 118140960795 + 911090 * 2 ^ 59
def prefixEnd_911090 : Nat := 4983230072969 + 3 ^ 40 * 911090 * 2
def baseEnd_911090 : Nat := 415846301782173857675537

theorem tailTrace_911090 : CollatzResearch.WordTrace tailWord_911090 prefixEnd_911090 415846301782173857675537 := by
  unfold tailWord_911090
  simp only [CollatzResearch.WordTrace]
  refine ⟨8307545567321001657254681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22153454846189337752679149 8307545567321001657254681)
  ·
    refine ⟨6230659175490751242941011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8307545567321001657254681 6230659175490751242941011)
    ·
      refine ⟨9345988763236126864411517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6230659175490751242941011 9345988763236126864411517)
      ·
        refine ⟨3504745786213547574154319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9345988763236126864411517 3504745786213547574154319)
        ·
          refine ⟨5257118679320321361231479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3504745786213547574154319 5257118679320321361231479)
          ·
            refine ⟨7885678018980482041847219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5257118679320321361231479 7885678018980482041847219)
            ·
              refine ⟨11828517028470723062770829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7885678018980482041847219 11828517028470723062770829)
              ·
                refine ⟨4435693885676521148539061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11828517028470723062770829 4435693885676521148539061)
                ·
                  refine ⟨415846301782173857675537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4435693885676521148539061 415846301782173857675537)
                  ·
                    rfl

theorem cell20_911090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 3, 5].length) (baseStart_911090 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_911090 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_911090 prefixEnd_911090 := by exact prefixLift 911090
  have htrace : WordTrace (prefixWord ++ tailWord_911090) baseStart_911090 baseEnd_911090 := by
    simpa [prefixWord, tailWord_911090, baseEnd_911090] using wordTrace_append hprefix tailTrace_911090
  have hstable : (prefixWord ++ tailWord_911090).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911090).length < 2 ^ (prefixWord ++ tailWord_911090).sum := by decide
  have hdescent : baseEnd_911090 < baseStart_911090 := by decide
  rcases family_descends (prefixWord ++ tailWord_911090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911107 : List Nat := [1, 1, 1, 3, 2, 2, 6, 1, 3]
def baseStart_911107 : Nat := 118140960795 + 911107 * 2 ^ 59
def prefixEnd_911107 : Nat := 4983230072969 + 3 ^ 40 * 911107 * 2
def baseEnd_911107 : Nat := 415854061045397354108801

theorem tailTrace_911107 : CollatzResearch.WordTrace tailWord_911107 prefixEnd_911107 415854061045397354108801 := by
  unfold tailWord_911107
  simp only [CollatzResearch.WordTrace]
  refine ⟨33230802310222418532387575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22153868206814945688258383 33230802310222418532387575)
  ·
    refine ⟨49846203465333627798581363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33230802310222418532387575 49846203465333627798581363)
    ·
      refine ⟨74769305198000441697872045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49846203465333627798581363 74769305198000441697872045)
      ·
        refine ⟨28038489449250165636702017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74769305198000441697872045 28038489449250165636702017)
        ·
          refine ⟨21028867086937624227526513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28038489449250165636702017 21028867086937624227526513)
          ·
            refine ⟨15771650315203218170644885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21028867086937624227526513 15771650315203218170644885)
            ·
              refine ⟨739296108525150851748979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 15771650315203218170644885 739296108525150851748979)
              ·
                refine ⟨1108944162787726277623469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 739296108525150851748979 1108944162787726277623469)
                ·
                  refine ⟨415854061045397354108801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1108944162787726277623469 415854061045397354108801)
                  ·
                    rfl

theorem cell20_911107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 6, 1, 3].length) (baseStart_911107 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_911107 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_911107 prefixEnd_911107 := by exact prefixLift 911107
  have htrace : WordTrace (prefixWord ++ tailWord_911107) baseStart_911107 baseEnd_911107 := by
    simpa [prefixWord, tailWord_911107, baseEnd_911107] using wordTrace_append hprefix tailTrace_911107
  have hstable : (prefixWord ++ tailWord_911107).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911107).length < 2 ^ (prefixWord ++ tailWord_911107).sum := by decide
  have hdescent : baseEnd_911107 < baseStart_911107 := by decide
  rcases family_descends (prefixWord ++ tailWord_911107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911148 : List Nat := [2, 2, 1, 1, 1, 7, 2, 2, 2]
def baseStart_911148 : Nat := 118140960795 + 911148 * 2 ^ 59
def prefixEnd_911148 : Nat := 4983230072969 + 3 ^ 40 * 911148 * 2
def baseEnd_911148 : Nat := 415872774562583433741967

theorem tailTrace_911148 : CollatzResearch.WordTrace tailWord_911148 prefixEnd_911148 415872774562583433741967 := by
  unfold tailWord_911148
  simp only [CollatzResearch.WordTrace]
  refine ⟨16616148851536941267315049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22154865135382588356420065 16616148851536941267315049)
  ·
    refine ⟨12462111638652705950486287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16616148851536941267315049 12462111638652705950486287)
    ·
      refine ⟨18693167457979058925729431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12462111638652705950486287 18693167457979058925729431)
      ·
        refine ⟨28039751186968588388594147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18693167457979058925729431 28039751186968588388594147)
        ·
          refine ⟨42059626780452882582891221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28039751186968588388594147 42059626780452882582891221)
          ·
            refine ⟨985772502666864435536513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 42059626780452882582891221 985772502666864435536513)
            ·
              refine ⟨739329377000148326652385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 985772502666864435536513 739329377000148326652385)
              ·
                refine ⟨554497032750111244989289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 739329377000148326652385 554497032750111244989289)
                ·
                  refine ⟨415872774562583433741967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 554497032750111244989289 415872774562583433741967)
                  ·
                    rfl

theorem cell20_911148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 2, 2, 2].length) (baseStart_911148 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_911148 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_911148 prefixEnd_911148 := by exact prefixLift 911148
  have htrace : WordTrace (prefixWord ++ tailWord_911148) baseStart_911148 baseEnd_911148 := by
    simpa [prefixWord, tailWord_911148, baseEnd_911148] using wordTrace_append hprefix tailTrace_911148
  have hstable : (prefixWord ++ tailWord_911148).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911148).length < 2 ^ (prefixWord ++ tailWord_911148).sum := by decide
  have hdescent : baseEnd_911148 < baseStart_911148 := by decide
  rcases family_descends (prefixWord ++ tailWord_911148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911173 : List Nat := [1, 3, 1, 1, 1, 2, 5, 2, 4]
def baseStart_911173 : Nat := 118140960795 + 911173 * 2 ^ 59
def prefixEnd_911173 : Nat := 4983230072969 + 3 ^ 40 * 911173 * 2
def baseEnd_911173 : Nat := 415884185243794457908531

theorem tailTrace_911173 : CollatzResearch.WordTrace tailWord_911173 prefixEnd_911173 415884185243794457908531 := by
  unfold tailWord_911173
  simp only [CollatzResearch.WordTrace]
  refine ⟨33233209527983311804290173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22155473018655541202860115 33233209527983311804290173)
  ·
    refine ⟨12462453572993741926608815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33233209527983311804290173 12462453572993741926608815)
    ·
      refine ⟨18693680359490612889913223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12462453572993741926608815 18693680359490612889913223)
      ·
        refine ⟨28040520539235919334869835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18693680359490612889913223 28040520539235919334869835)
        ·
          refine ⟨42060780808853879002304753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28040520539235919334869835 42060780808853879002304753)
          ·
            refine ⟨31545585606640409251728565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42060780808853879002304753 31545585606640409251728565)
            ·
              refine ⟨2957398650622538367349553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31545585606640409251728565 2957398650622538367349553)
              ·
                refine ⟨2218048987966903775512165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2957398650622538367349553 2218048987966903775512165)
                ·
                  refine ⟨415884185243794457908531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2218048987966903775512165 415884185243794457908531)
                  ·
                    rfl

theorem cell20_911173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 2, 4].length) (baseStart_911173 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_911173 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_911173 prefixEnd_911173 := by exact prefixLift 911173
  have htrace : WordTrace (prefixWord ++ tailWord_911173) baseStart_911173 baseEnd_911173 := by
    simpa [prefixWord, tailWord_911173, baseEnd_911173] using wordTrace_append hprefix tailTrace_911173
  have hstable : (prefixWord ++ tailWord_911173).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911173).length < 2 ^ (prefixWord ++ tailWord_911173).sum := by decide
  have hdescent : baseEnd_911173 < baseStart_911173 := by decide
  rcases family_descends (prefixWord ++ tailWord_911173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911218 : List Nat := [3, 2, 1, 2, 1, 1, 1, 9]
def baseStart_911218 : Nat := 118140960795 + 911218 * 2 ^ 59
def prefixEnd_911218 : Nat := 4983230072969 + 3 ^ 40 * 911218 * 2
def baseEnd_911218 : Nat := 138634908156658100469449

theorem tailTrace_911218 : CollatzResearch.WordTrace tailWord_911218 prefixEnd_911218 138634908156658100469449 := by
  unfold tailWord_911218
  simp only [CollatzResearch.WordTrace]
  refine ⟨8308712703205071122419577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22156567208546856326452205 8308712703205071122419577)
  ·
    refine ⟨6231534527403803341814683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8308712703205071122419577 6231534527403803341814683)
    ·
      refine ⟨9347301791105705012722025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6231534527403803341814683 9347301791105705012722025)
      ·
        refine ⟨7010476343329278759541519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9347301791105705012722025 7010476343329278759541519)
        ·
          refine ⟨10515714514993918139312279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7010476343329278759541519 10515714514993918139312279)
          ·
            refine ⟨15773571772490877208968419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10515714514993918139312279 15773571772490877208968419)
            ·
              refine ⟨23660357658736315813452629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15773571772490877208968419 23660357658736315813452629)
              ·
                refine ⟨138634908156658100469449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23660357658736315813452629 138634908156658100469449)
                ·
                  rfl

theorem cell20_911218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 9].length) (baseStart_911218 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_911218 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_911218 prefixEnd_911218 := by exact prefixLift 911218
  have htrace : WordTrace (prefixWord ++ tailWord_911218) baseStart_911218 baseEnd_911218 := by
    simpa [prefixWord, tailWord_911218, baseEnd_911218] using wordTrace_append hprefix tailTrace_911218
  have hstable : (prefixWord ++ tailWord_911218).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911218).length < 2 ^ (prefixWord ++ tailWord_911218).sum := by decide
  have hdescent : baseEnd_911218 < baseStart_911218 := by decide
  rcases family_descends (prefixWord ++ tailWord_911218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911235 : List Nat := [1, 1, 1, 3, 4, 2, 4, 4]
def baseStart_911235 : Nat := 118140960795 + 911235 * 2 ^ 59
def prefixEnd_911235 : Nat := 4983230072969 + 3 ^ 40 * 911235 * 2
def baseEnd_911235 : Nat := 138637494577732599280537

theorem tailTrace_911235 : CollatzResearch.WordTrace tailWord_911235 prefixEnd_911235 138637494577732599280537 := by
  unfold tailWord_911235
  simp only [CollatzResearch.WordTrace]
  refine ⟨33235470853758696393047159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22156980569172464262031439 33235470853758696393047159)
  ·
    refine ⟨49853206280638044589570739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33235470853758696393047159 49853206280638044589570739)
    ·
      refine ⟨74779809420957066884356109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49853206280638044589570739 74779809420957066884356109)
      ·
        refine ⟨28042428532858900081633541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74779809420957066884356109 28042428532858900081633541)
        ·
          refine ⟨5257955349911043765306289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28042428532858900081633541 5257955349911043765306289)
          ·
            refine ⟨3943466512433282823979717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5257955349911043765306289 3943466512433282823979717)
            ·
              refine ⟨739399971081240529496197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3943466512433282823979717 739399971081240529496197)
              ·
                refine ⟨138637494577732599280537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 739399971081240529496197 138637494577732599280537)
                ·
                  rfl

theorem cell20_911235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 4, 4].length) (baseStart_911235 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_911235 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_911235 prefixEnd_911235 := by exact prefixLift 911235
  have htrace : WordTrace (prefixWord ++ tailWord_911235) baseStart_911235 baseEnd_911235 := by
    simpa [prefixWord, tailWord_911235, baseEnd_911235] using wordTrace_append hprefix tailTrace_911235
  have hstable : (prefixWord ++ tailWord_911235).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911235).length < 2 ^ (prefixWord ++ tailWord_911235).sum := by decide
  have hdescent : baseEnd_911235 < baseStart_911235 := by decide
  rcases family_descends (prefixWord ++ tailWord_911235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911272 : List Nat := [2, 1, 6, 2, 1, 2, 2, 1, 3]
def baseStart_911272 : Nat := 118140960795 + 911272 * 2 ^ 59
def prefixEnd_911272 : Nat := 4983230072969 + 3 ^ 40 * 911272 * 2
def baseEnd_911272 : Nat := 415929371541390113608127

theorem tailTrace_911272 : CollatzResearch.WordTrace tailWord_911272 prefixEnd_911272 415929371541390113608127 := by
  unfold tailWord_911272
  simp only [CollatzResearch.WordTrace]
  refine ⟨16618410177312325856072035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22157880236416434474762713 16618410177312325856072035)
  ·
    refine ⟨24927615265968488784108053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16618410177312325856072035 24927615265968488784108053)
    ·
      refine ⟨1168481965592272911755065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 24927615265968488784108053 1168481965592272911755065)
      ·
        refine ⟨876361474194204683816299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1168481965592272911755065 876361474194204683816299)
        ·
          refine ⟨1314542211291307025724449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 876361474194204683816299 1314542211291307025724449)
          ·
            refine ⟨985906658468480269293337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1314542211291307025724449 985906658468480269293337)
            ·
              refine ⟨739429993851360201970003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 985906658468480269293337 739429993851360201970003)
              ·
                refine ⟨1109144990777040302955005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 739429993851360201970003 1109144990777040302955005)
                ·
                  refine ⟨415929371541390113608127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1109144990777040302955005 415929371541390113608127)
                  ·
                    rfl

theorem cell20_911272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 2, 1, 3].length) (baseStart_911272 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_911272 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_911272 prefixEnd_911272 := by exact prefixLift 911272
  have htrace : WordTrace (prefixWord ++ tailWord_911272) baseStart_911272 baseEnd_911272 := by
    simpa [prefixWord, tailWord_911272, baseEnd_911272] using wordTrace_append hprefix tailTrace_911272
  have hstable : (prefixWord ++ tailWord_911272).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911272).length < 2 ^ (prefixWord ++ tailWord_911272).sum := by decide
  have hdescent : baseEnd_911272 < baseStart_911272 := by decide
  rcases family_descends (prefixWord ++ tailWord_911272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911301 : List Nat := [1, 3, 1, 1, 1, 1, 1, 6, 5]
def baseStart_911301 : Nat := 118140960795 + 911301 * 2 ^ 59
def prefixEnd_911301 : Nat := 4983230072969 + 3 ^ 40 * 911301 * 2
def baseEnd_911301 : Nat := 415942607931594901641341

theorem tailTrace_911301 : CollatzResearch.WordTrace tailWord_911301 prefixEnd_911301 415942607931594901641341 := by
  unfold tailWord_911301
  simp only [CollatzResearch.WordTrace]
  refine ⟨33237878071519589664949757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22158585381013059776633171 33237878071519589664949757)
  ·
    refine ⟨12464204276819846124356159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33237878071519589664949757 12464204276819846124356159)
    ·
      refine ⟨18696306415229769186534239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12464204276819846124356159 18696306415229769186534239)
      ·
        refine ⟨28044459622844653779801359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18696306415229769186534239 28044459622844653779801359)
        ·
          refine ⟨42066689434266980669702039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28044459622844653779801359 42066689434266980669702039)
          ·
            refine ⟨63100034151400471004553059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42066689434266980669702039 63100034151400471004553059)
            ·
              refine ⟨94650051227100706506829589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63100034151400471004553059 94650051227100706506829589)
              ·
                refine ⟨4436721151270345617507637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 94650051227100706506829589 4436721151270345617507637)
                ·
                  refine ⟨415942607931594901641341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4436721151270345617507637 415942607931594901641341)
                  ·
                    rfl

theorem cell20_911301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 6, 5].length) (baseStart_911301 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_911301 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_911301 prefixEnd_911301 := by exact prefixLift 911301
  have htrace : WordTrace (prefixWord ++ tailWord_911301) baseStart_911301 baseEnd_911301 := by
    simpa [prefixWord, tailWord_911301, baseEnd_911301] using wordTrace_append hprefix tailTrace_911301
  have hstable : (prefixWord ++ tailWord_911301).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911301).length < 2 ^ (prefixWord ++ tailWord_911301).sum := by decide
  have hdescent : baseEnd_911301 < baseStart_911301 := by decide
  rcases family_descends (prefixWord ++ tailWord_911301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911314 : List Nat := [3, 2, 2, 3, 2, 1, 2, 2, 3]
def baseStart_911314 : Nat := 118140960795 + 911314 * 2 ^ 59
def prefixEnd_911314 : Nat := 4983230072969 + 3 ^ 40 * 911314 * 2
def baseEnd_911314 : Nat := 415948541485824634207955

theorem tailTrace_911314 : CollatzResearch.WordTrace tailWord_911314 prefixEnd_911314 415948541485824634207955 := by
  unfold tailWord_911314
  simp only [CollatzResearch.WordTrace]
  refine ⟨8309588055118123221293249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22158901480314995256781997 8309588055118123221293249)
  ·
    refine ⟨6232191041338592415969937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8309588055118123221293249 6232191041338592415969937)
    ·
      refine ⟨4674143281003944311977453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6232191041338592415969937 4674143281003944311977453)
      ·
        refine ⟨1752803730376479116991545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4674143281003944311977453 1752803730376479116991545)
        ·
          refine ⟨1314602797782359337743659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1752803730376479116991545 1314602797782359337743659)
          ·
            refine ⟨1971904196673539006615489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1314602797782359337743659 1971904196673539006615489)
            ·
              refine ⟨1478928147505154254961617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1971904196673539006615489 1478928147505154254961617)
              ·
                refine ⟨1109196110628865691221213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1478928147505154254961617 1109196110628865691221213)
                ·
                  refine ⟨415948541485824634207955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1109196110628865691221213 415948541485824634207955)
                  ·
                    rfl

theorem cell20_911314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 2, 2, 3].length) (baseStart_911314 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_911314 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_911314 prefixEnd_911314 := by exact prefixLift 911314
  have htrace : WordTrace (prefixWord ++ tailWord_911314) baseStart_911314 baseEnd_911314 := by
    simpa [prefixWord, tailWord_911314, baseEnd_911314] using wordTrace_append hprefix tailTrace_911314
  have hstable : (prefixWord ++ tailWord_911314).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911314).length < 2 ^ (prefixWord ++ tailWord_911314).sum := by decide
  have hdescent : baseEnd_911314 < baseStart_911314 := by decide
  rcases family_descends (prefixWord ++ tailWord_911314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911321 : List Nat := [1, 2, 1, 2, 6, 1, 1, 4, 2]
def baseStart_911321 : Nat := 118140960795 + 911321 * 2 ^ 59
def prefixEnd_911321 : Nat := 4983230072969 + 3 ^ 40 * 911321 * 2
def baseEnd_911321 : Nat := 415951736476563720974593

theorem tailTrace_911321 : CollatzResearch.WordTrace tailWord_911321 prefixEnd_911321 415951736476563720974593 := by
  unfold tailWord_911321
  simp only [CollatzResearch.WordTrace]
  refine ⟨33238607531447133080677817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22159071687631422053785211 33238607531447133080677817)
  ·
    refine ⟨24928955648585349810508363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33238607531447133080677817 24928955648585349810508363)
    ·
      refine ⟨37393433472878024715762545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24928955648585349810508363 37393433472878024715762545)
      ·
        refine ⟨28045075104658518536821909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37393433472878024715762545 28045075104658518536821909)
        ·
          refine ⟨1314612895530868056413527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 28045075104658518536821909 1314612895530868056413527)
          ·
            refine ⟨1971919343296302084620291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1314612895530868056413527 1971919343296302084620291)
            ·
              refine ⟨2957879014944453126930437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1971919343296302084620291 2957879014944453126930437)
              ·
                refine ⟨554602315302084961299457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2957879014944453126930437 554602315302084961299457)
                ·
                  refine ⟨415951736476563720974593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 554602315302084961299457 415951736476563720974593)
                  ·
                    rfl

theorem cell20_911321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 4, 2].length) (baseStart_911321 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_911321 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_911321 prefixEnd_911321 := by exact prefixLift 911321
  have htrace : WordTrace (prefixWord ++ tailWord_911321) baseStart_911321 baseEnd_911321 := by
    simpa [prefixWord, tailWord_911321, baseEnd_911321] using wordTrace_append hprefix tailTrace_911321
  have hstable : (prefixWord ++ tailWord_911321).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911321).length < 2 ^ (prefixWord ++ tailWord_911321).sum := by decide
  have hdescent : baseEnd_911321 < baseStart_911321 := by decide
  rcases family_descends (prefixWord ++ tailWord_911321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911324 : List Nat := [2, 2, 6, 1, 1, 2, 1, 5]
def baseStart_911324 : Nat := 118140960795 + 911324 * 2 ^ 59
def prefixEnd_911324 : Nat := 4983230072969 + 3 ^ 40 * 911324 * 2
def baseEnd_911324 : Nat := 138651035252769681291527

theorem tailTrace_911324 : CollatzResearch.WordTrace tailWord_911324 prefixEnd_911324 138651035252769681291527 := by
  unfold tailWord_911324
  simp only [CollatzResearch.WordTrace]
  refine ⟨16619358475218132296518513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22159144633624176395358017 16619358475218132296518513)
  ·
    refine ⟨12464518856413599222388885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16619358475218132296518513 12464518856413599222388885)
    ·
      refine ⟨584274321394387463549479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 12464518856413599222388885 584274321394387463549479)
      ·
        refine ⟨876411482091581195324219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 584274321394387463549479 876411482091581195324219)
        ·
          refine ⟨1314617223137371792986329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 876411482091581195324219 1314617223137371792986329)
          ·
            refine ⟨985962917353028844739747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1314617223137371792986329 985962917353028844739747)
            ·
              refine ⟨1478944376029543267109621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 985962917353028844739747 1478944376029543267109621)
              ·
                refine ⟨138651035252769681291527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1478944376029543267109621 138651035252769681291527)
                ·
                  rfl

theorem cell20_911324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 1, 5].length) (baseStart_911324 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_911324 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_911324 prefixEnd_911324 := by exact prefixLift 911324
  have htrace : WordTrace (prefixWord ++ tailWord_911324) baseStart_911324 baseEnd_911324 := by
    simpa [prefixWord, tailWord_911324, baseEnd_911324] using wordTrace_append hprefix tailTrace_911324
  have hstable : (prefixWord ++ tailWord_911324).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911324).length < 2 ^ (prefixWord ++ tailWord_911324).sum := by decide
  have hdescent : baseEnd_911324 < baseStart_911324 := by decide
  rcases family_descends (prefixWord ++ tailWord_911324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911342 : List Nat := [4, 1, 2, 1, 3, 2, 1, 2, 4]
def baseStart_911342 : Nat := 118140960795 + 911342 * 2 ^ 59
def prefixEnd_911342 : Nat := 4983230072969 + 3 ^ 40 * 911342 * 2
def baseEnd_911342 : Nat := 415961321448780981274507

theorem tailTrace_911342 : CollatzResearch.WordTrace tailWord_911342 prefixEnd_911342 415961321448780981274507 := by
  unfold tailWord_911342
  simp only [CollatzResearch.WordTrace]
  refine ⟨4154921683046381708399035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22159582309580702444794853 4154921683046381708399035)
  ·
    refine ⟨6232382524569572562598553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4154921683046381708399035 6232382524569572562598553)
    ·
      refine ⟨4674286893427179421948915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6232382524569572562598553 4674286893427179421948915)
      ·
        refine ⟨7011430340140769132923373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4674286893427179421948915 7011430340140769132923373)
        ·
          refine ⟨2629286377552788424846265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7011430340140769132923373 2629286377552788424846265)
          ·
            refine ⟨1971964783164591318634699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2629286377552788424846265 1971964783164591318634699)
            ·
              refine ⟨2957947174746886977952049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1971964783164591318634699 2957947174746886977952049)
              ·
                refine ⟨2218460381060165233464037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2957947174746886977952049 2218460381060165233464037)
                ·
                  refine ⟨415961321448780981274507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2218460381060165233464037 415961321448780981274507)
                  ·
                    rfl

theorem cell20_911342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 2, 4].length) (baseStart_911342 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_911342 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_911342 prefixEnd_911342 := by exact prefixLift 911342
  have htrace : WordTrace (prefixWord ++ tailWord_911342) baseStart_911342 baseEnd_911342 := by
    simpa [prefixWord, tailWord_911342, baseEnd_911342] using wordTrace_append hprefix tailTrace_911342
  have hstable : (prefixWord ++ tailWord_911342).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911342).length < 2 ^ (prefixWord ++ tailWord_911342).sum := by decide
  have hdescent : baseEnd_911342 < baseStart_911342 := by decide
  rcases family_descends (prefixWord ++ tailWord_911342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911400 : List Nat := [2, 1, 5, 3, 2, 1, 2, 4]
def baseStart_911400 : Nat := 118140960795 + 911400 * 2 ^ 59
def prefixEnd_911400 : Nat := 4983230072969 + 3 ^ 40 * 911400 * 2
def baseEnd_911400 : Nat := 138662598076396852446979

theorem tailTrace_911400 : CollatzResearch.WordTrace tailWord_911400 prefixEnd_911400 138662598076396852446979 := by
  unfold tailWord_911400
  simp only [CollatzResearch.WordTrace]
  refine ⟨16620744449080464786401827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22160992598773953048535769 16620744449080464786401827)
  ·
    refine ⟨24931116673620697179602741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16620744449080464786401827 24931116673620697179602741)
    ·
      refine ⟨2337292188151940360587757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24931116673620697179602741 2337292188151940360587757)
      ·
        refine ⟨876484570556977635220409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2337292188151940360587757 876484570556977635220409)
        ·
          refine ⟨657363427917733226415307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 876484570556977635220409 657363427917733226415307)
          ·
            refine ⟨986045141876599839622961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 657363427917733226415307 986045141876599839622961)
            ·
              refine ⟨739533856407449879717221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 986045141876599839622961 739533856407449879717221)
              ·
                refine ⟨138662598076396852446979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 739533856407449879717221 138662598076396852446979)
                ·
                  rfl

theorem cell20_911400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 2, 4].length) (baseStart_911400 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_911400 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_911400 prefixEnd_911400 := by exact prefixLift 911400
  have htrace : WordTrace (prefixWord ++ tailWord_911400) baseStart_911400 baseEnd_911400 := by
    simpa [prefixWord, tailWord_911400, baseEnd_911400] using wordTrace_append hprefix tailTrace_911400
  have hstable : (prefixWord ++ tailWord_911400).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911400).length < 2 ^ (prefixWord ++ tailWord_911400).sum := by decide
  have hdescent : baseEnd_911400 < baseStart_911400 := by decide
  rcases family_descends (prefixWord ++ tailWord_911400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911408 : List Nat := [2, 1, 1, 1, 2, 6, 1, 6]
def baseStart_911408 : Nat := 118140960795 + 911408 * 2 ^ 59
def prefixEnd_911408 : Nat := 4983230072969 + 3 ^ 40 * 911408 * 2
def baseEnd_911408 : Nat := 138663815215726028358079

theorem tailTrace_911408 : CollatzResearch.WordTrace tailWord_911408 prefixEnd_911408 138663815215726028358079 := by
  unfold tailWord_911408
  simp only [CollatzResearch.WordTrace]
  refine ⟨16620890341065973469547439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22161187121421297959396585 16620890341065973469547439)
  ·
    refine ⟨24931335511598960204321159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16620890341065973469547439 24931335511598960204321159)
    ·
      refine ⟨37397003267398440306481739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24931335511598960204321159 37397003267398440306481739)
      ·
        refine ⟨56095504901097660459722609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37397003267398440306481739 56095504901097660459722609)
        ·
          refine ⟨42071628675823245344791957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56095504901097660459722609 42071628675823245344791957)
          ·
            refine ⟨1972107594179214625537123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 42071628675823245344791957 1972107594179214625537123)
            ·
              refine ⟨2958161391268821938305685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1972107594179214625537123 2958161391268821938305685)
              ·
                refine ⟨138663815215726028358079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2958161391268821938305685 138663815215726028358079)
                ·
                  rfl

theorem cell20_911408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 6].length) (baseStart_911408 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_911408 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_911408 prefixEnd_911408 := by exact prefixLift 911408
  have htrace : WordTrace (prefixWord ++ tailWord_911408) baseStart_911408 baseEnd_911408 := by
    simpa [prefixWord, tailWord_911408, baseEnd_911408] using wordTrace_append hprefix tailTrace_911408
  have hstable : (prefixWord ++ tailWord_911408).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911408).length < 2 ^ (prefixWord ++ tailWord_911408).sum := by decide
  have hdescent : baseEnd_911408 < baseStart_911408 := by decide
  rcases family_descends (prefixWord ++ tailWord_911408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911415 : List Nat := [1, 1, 3, 1, 2, 2, 3, 2, 5]
def baseStart_911415 : Nat := 118140960795 + 911415 * 2 ^ 59
def prefixEnd_911415 : Nat := 4983230072969 + 3 ^ 40 * 911415 * 2
def baseEnd_911415 : Nat := 415994640637917171840875

theorem tailTrace_911415 : CollatzResearch.WordTrace tailWord_911415 prefixEnd_911415 415994640637917171840875 := by
  unfold tailWord_911415
  simp only [CollatzResearch.WordTrace]
  refine ⟨33242035993106587134599699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22161357328737724756399799 33242035993106587134599699)
  ·
    refine ⟨49863053989659880701899549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33242035993106587134599699 49863053989659880701899549)
    ·
      refine ⟨18698645246122455263212331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49863053989659880701899549 18698645246122455263212331)
      ·
        refine ⟨28047967869183682894818497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18698645246122455263212331 28047967869183682894818497)
        ·
          refine ⟨21035975901887762171113873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28047967869183682894818497 21035975901887762171113873)
          ·
            refine ⟨15776981926415821628335405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21035975901887762171113873 15776981926415821628335405)
            ·
              refine ⟨5916368222405933110625777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15776981926415821628335405 5916368222405933110625777)
              ·
                refine ⟨4437276166804449832969333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5916368222405933110625777 4437276166804449832969333)
                ·
                  refine ⟨415994640637917171840875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4437276166804449832969333 415994640637917171840875)
                  ·
                    rfl

theorem cell20_911415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 2, 5].length) (baseStart_911415 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_911415 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_911415 prefixEnd_911415 := by exact prefixLift 911415
  have htrace : WordTrace (prefixWord ++ tailWord_911415) baseStart_911415 baseEnd_911415 := by
    simpa [prefixWord, tailWord_911415, baseEnd_911415] using wordTrace_append hprefix tailTrace_911415
  have hstable : (prefixWord ++ tailWord_911415).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911415).length < 2 ^ (prefixWord ++ tailWord_911415).sum := by decide
  have hdescent : baseEnd_911415 < baseStart_911415 := by decide
  rcases family_descends (prefixWord ++ tailWord_911415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911425 : List Nat := [1, 2, 5, 1, 2, 3, 6]
def baseStart_911425 : Nat := 118140960795 + 911425 * 2 ^ 59
def prefixEnd_911425 : Nat := 4983230072969 + 3 ^ 40 * 911425 * 2
def baseEnd_911425 : Nat := 46222133878933509056389

theorem tailTrace_911425 : CollatzResearch.WordTrace tailWord_911425 prefixEnd_911425 46222133878933509056389 := by
  unfold tailWord_911425
  simp only [CollatzResearch.WordTrace]
  refine ⟨33242400723070358842463729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22161600482046905894975819 33242400723070358842463729)
  ·
    refine ⟨24931800542302769131847797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33242400723070358842463729 24931800542302769131847797)
    ·
      refine ⟨2337356300840884606110731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24931800542302769131847797 2337356300840884606110731)
      ·
        refine ⟨3506034451261326909166097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2337356300840884606110731 3506034451261326909166097)
        ·
          refine ⟨2629525838445995181874573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3506034451261326909166097 2629525838445995181874573)
          ·
            refine ⟨986072189417248193202965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2629525838445995181874573 986072189417248193202965)
            ·
              refine ⟨46222133878933509056389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 986072189417248193202965 46222133878933509056389)
              ·
                rfl

theorem cell20_911425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 6].length) (baseStart_911425 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_911425 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_911425 prefixEnd_911425 := by exact prefixLift 911425
  have htrace : WordTrace (prefixWord ++ tailWord_911425) baseStart_911425 baseEnd_911425 := by
    simpa [prefixWord, tailWord_911425, baseEnd_911425] using wordTrace_append hprefix tailTrace_911425
  have hstable : (prefixWord ++ tailWord_911425).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911425).length < 2 ^ (prefixWord ++ tailWord_911425).sum := by decide
  have hdescent : baseEnd_911425 < baseStart_911425 := by decide
  rcases family_descends (prefixWord ++ tailWord_911425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911546 : List Nat := [3, 1, 1, 1, 2, 2, 5, 2, 3]
def baseStart_911546 : Nat := 118140960795 + 911546 * 2 ^ 59
def prefixEnd_911546 : Nat := 4983230072969 + 3 ^ 40 * 911546 * 2
def baseEnd_911546 : Nat := 416054432607462938473673

theorem tailTrace_911546 : CollatzResearch.WordTrace tailWord_911546 prefixEnd_911546 416054432607462938473673 := by
  unfold tailWord_911546
  simp only [CollatzResearch.WordTrace]
  refine ⟨8311703488907999126904623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22164542637087997671745661 8311703488907999126904623)
  ·
    refine ⟨12467555233361998690356935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8311703488907999126904623 12467555233361998690356935)
    ·
      refine ⟨18701332850042998035535403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12467555233361998690356935 18701332850042998035535403)
      ·
        refine ⟨28051999275064497053303105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18701332850042998035535403 28051999275064497053303105)
        ·
          refine ⟨21038999456298372789977329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28051999275064497053303105 21038999456298372789977329)
          ·
            refine ⟨15779249592223779592482997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21038999456298372789977329 15779249592223779592482997)
            ·
              refine ⟨1479304649270979336795281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15779249592223779592482997 1479304649270979336795281)
              ·
                refine ⟨1109478486953234502596461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1479304649270979336795281 1109478486953234502596461)
                ·
                  refine ⟨416054432607462938473673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1109478486953234502596461 416054432607462938473673)
                  ·
                    rfl

theorem cell20_911546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 5, 2, 3].length) (baseStart_911546 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_911546 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_911546 prefixEnd_911546 := by exact prefixLift 911546
  have htrace : WordTrace (prefixWord ++ tailWord_911546) baseStart_911546 baseEnd_911546 := by
    simpa [prefixWord, tailWord_911546, baseEnd_911546] using wordTrace_append hprefix tailTrace_911546
  have hstable : (prefixWord ++ tailWord_911546).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911546).length < 2 ^ (prefixWord ++ tailWord_911546).sum := by decide
  have hdescent : baseEnd_911546 < baseStart_911546 := by decide
  rcases family_descends (prefixWord ++ tailWord_911546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911573 : List Nat := [1, 3, 2, 4, 3, 1, 2, 4]
def baseStart_911573 : Nat := 118140960795 + 911573 * 2 ^ 59
def prefixEnd_911573 : Nat := 4983230072969 + 3 ^ 40 * 911573 * 2
def baseEnd_911573 : Nat := 138688918714390281524521

theorem tailTrace_911573 : CollatzResearch.WordTrace tailWord_911573 prefixEnd_911573 138688918714390281524521 := by
  unfold tailWord_911573
  simp only [CollatzResearch.WordTrace]
  refine ⟨33247798726534180118851373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22165199151022786745900915 33247798726534180118851373)
  ·
    refine ⟨12467924522450317544569265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33247798726534180118851373 12467924522450317544569265)
    ·
      refine ⟨9350943391837738158426949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12467924522450317544569265 9350943391837738158426949)
      ·
        refine ⟨1753301885969575904705053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9350943391837738158426949 1753301885969575904705053)
        ·
          refine ⟨657488207238590964264395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1753301885969575904705053 657488207238590964264395)
          ·
            refine ⟨986232310857886446396593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 657488207238590964264395 986232310857886446396593)
            ·
              refine ⟨739674233143414834797445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 986232310857886446396593 739674233143414834797445)
              ·
                refine ⟨138688918714390281524521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 739674233143414834797445 138688918714390281524521)
                ·
                  rfl

theorem cell20_911573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 2, 4].length) (baseStart_911573 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_911573 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_911573 prefixEnd_911573 := by exact prefixLift 911573
  have htrace : WordTrace (prefixWord ++ tailWord_911573) baseStart_911573 baseEnd_911573 := by
    simpa [prefixWord, tailWord_911573, baseEnd_911573] using wordTrace_append hprefix tailTrace_911573
  have hstable : (prefixWord ++ tailWord_911573).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911573).length < 2 ^ (prefixWord ++ tailWord_911573).sum := by decide
  have hdescent : baseEnd_911573 < baseStart_911573 := by decide
  rcases family_descends (prefixWord ++ tailWord_911573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911618 : List Nat := [3, 4, 1, 1, 2, 1, 4, 1, 3]
def baseStart_911618 : Nat := 118140960795 + 911618 * 2 ^ 59
def prefixEnd_911618 : Nat := 4983230072969 + 3 ^ 40 * 911618 * 2
def baseEnd_911618 : Nat := 416087295369350688073379

theorem tailTrace_911618 : CollatzResearch.WordTrace tailWord_911618 prefixEnd_911618 416087295369350688073379 := by
  unfold tailWord_911618
  simp only [CollatzResearch.WordTrace]
  refine ⟨8312360002842788201059877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22166293340914101869493005 8312360002842788201059877)
  ·
    refine ⟨1558567500533022787698727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8312360002842788201059877 1558567500533022787698727)
    ·
      refine ⟨2337851250799534181548091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1558567500533022787698727 2337851250799534181548091)
      ·
        refine ⟨3506776876199301272322137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2337851250799534181548091 3506776876199301272322137)
        ·
          refine ⟨2630082657149475954241603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3506776876199301272322137 2630082657149475954241603)
          ·
            refine ⟨3945123985724213931362405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2630082657149475954241603 3945123985724213931362405)
            ·
              refine ⟨739710747323290112130451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3945123985724213931362405 739710747323290112130451)
              ·
                refine ⟨1109566120984935168195677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 739710747323290112130451 1109566120984935168195677)
                ·
                  refine ⟨416087295369350688073379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1109566120984935168195677 416087295369350688073379)
                  ·
                    rfl

theorem cell20_911618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_911618 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_911618 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_911618 prefixEnd_911618 := by exact prefixLift 911618
  have htrace : WordTrace (prefixWord ++ tailWord_911618) baseStart_911618 baseEnd_911618 := by
    simpa [prefixWord, tailWord_911618, baseEnd_911618] using wordTrace_append hprefix tailTrace_911618
  have hstable : (prefixWord ++ tailWord_911618).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911618).length < 2 ^ (prefixWord ++ tailWord_911618).sum := by decide
  have hdescent : baseEnd_911618 < baseStart_911618 := by decide
  rcases family_descends (prefixWord ++ tailWord_911618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911655 : List Nat := [1, 1, 8, 1, 2, 1, 2, 2, 2]
def baseStart_911655 : Nat := 118140960795 + 911655 * 2 ^ 59
def prefixEnd_911655 : Nat := 4983230072969 + 3 ^ 40 * 911655 * 2
def baseEnd_911655 : Nat := 416104183177543003839895

theorem tailTrace_911655 : CollatzResearch.WordTrace tailWord_911655 prefixEnd_911655 416104183177543003839895 := by
  unfold tailWord_911655
  simp only [CollatzResearch.WordTrace]
  refine ⟨33250789512237108123336419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22167193008158072082224279 33250789512237108123336419)
  ·
    refine ⟨49876184268355662185004629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33250789512237108123336419 49876184268355662185004629)
    ·
      refine ⟨584486534394792916230523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 49876184268355662185004629 584486534394792916230523)
      ·
        refine ⟨876729801592189374345785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 584486534394792916230523 876729801592189374345785)
        ·
          refine ⟨657547351194142030759339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 876729801592189374345785 657547351194142030759339)
          ·
            refine ⟨986321026791213046139009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 657547351194142030759339 986321026791213046139009)
            ·
              refine ⟨739740770093409784604257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 986321026791213046139009 739740770093409784604257)
              ·
                refine ⟨554805577570057338453193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 739740770093409784604257 554805577570057338453193)
                ·
                  refine ⟨416104183177543003839895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 554805577570057338453193 416104183177543003839895)
                  ·
                    rfl

theorem cell20_911655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 2, 2, 2].length) (baseStart_911655 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_911655 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_911655 prefixEnd_911655 := by exact prefixLift 911655
  have htrace : WordTrace (prefixWord ++ tailWord_911655) baseStart_911655 baseEnd_911655 := by
    simpa [prefixWord, tailWord_911655, baseEnd_911655] using wordTrace_append hprefix tailTrace_911655
  have hstable : (prefixWord ++ tailWord_911655).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911655).length < 2 ^ (prefixWord ++ tailWord_911655).sum := by decide
  have hdescent : baseEnd_911655 < baseStart_911655 := by decide
  rcases family_descends (prefixWord ++ tailWord_911655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911674 : List Nat := [3, 1, 1, 1, 4, 2, 3, 5]
def baseStart_911674 : Nat := 118140960795 + 911674 * 2 ^ 59
def prefixEnd_911674 : Nat := 4983230072969 + 3 ^ 40 * 911674 * 2
def baseEnd_911674 : Nat := 138704285098421127402161

theorem tailTrace_911674 : CollatzResearch.WordTrace tailWord_911674 prefixEnd_911674 138704285098421127402161 := by
  unfold tailWord_911674
  simp only [CollatzResearch.WordTrace]
  refine ⟨8312870624792068592069519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22167654999445516245518717 8312870624792068592069519)
  ·
    refine ⟨12469305937188102888104279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8312870624792068592069519 12469305937188102888104279)
    ·
      refine ⟨18703958905782154332156419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12469305937188102888104279 18703958905782154332156419)
      ·
        refine ⟨28055938358673231498234629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18703958905782154332156419 28055938358673231498234629)
        ·
          refine ⟨5260488442251230905918993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28055938358673231498234629 5260488442251230905918993)
          ·
            refine ⟨3945366331688423179439245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5260488442251230905918993 3945366331688423179439245)
            ·
              refine ⟨1479512374383158692289717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3945366331688423179439245 1479512374383158692289717)
              ·
                refine ⟨138704285098421127402161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1479512374383158692289717 138704285098421127402161)
                ·
                  rfl

theorem cell20_911674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 3, 5].length) (baseStart_911674 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_911674 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_911674 prefixEnd_911674 := by exact prefixLift 911674
  have htrace : WordTrace (prefixWord ++ tailWord_911674) baseStart_911674 baseEnd_911674 := by
    simpa [prefixWord, tailWord_911674, baseEnd_911674] using wordTrace_append hprefix tailTrace_911674
  have hstable : (prefixWord ++ tailWord_911674).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911674).length < 2 ^ (prefixWord ++ tailWord_911674).sum := by decide
  have hdescent : baseEnd_911674 < baseStart_911674 := by decide
  rcases family_descends (prefixWord ++ tailWord_911674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911688 : List Nat := [2, 1, 3, 1, 1, 2, 3, 1, 6]
def baseStart_911688 : Nat := 118140960795 + 911688 * 2 ^ 59
def prefixEnd_911688 : Nat := 4983230072969 + 3 ^ 40 * 911688 * 2
def baseEnd_911688 : Nat := 416119245276741555739759

theorem tailTrace_911688 : CollatzResearch.WordTrace tailWord_911688 prefixEnd_911688 416119245276741555739759 := by
  unfold tailWord_911688
  simp only [CollatzResearch.WordTrace]
  refine ⟨16625996560558777379643859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22167995414078369839525145 16625996560558777379643859)
  ·
    refine ⟨24938994840838166069465789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16625996560558777379643859 24938994840838166069465789)
    ·
      refine ⟨9352123065314312276049671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24938994840838166069465789 9352123065314312276049671)
      ·
        refine ⟨14028184597971468414074507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9352123065314312276049671 14028184597971468414074507)
        ·
          refine ⟨21042276896957202621111761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14028184597971468414074507 21042276896957202621111761)
          ·
            refine ⟨15781707672717901965833821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21042276896957202621111761 15781707672717901965833821)
            ·
              refine ⟨5918140377269213237187683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15781707672717901965833821 5918140377269213237187683)
              ·
                refine ⟨8877210565903819855781525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5918140377269213237187683 8877210565903819855781525)
                ·
                  refine ⟨416119245276741555739759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8877210565903819855781525 416119245276741555739759)
                  ·
                    rfl

theorem cell20_911688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 1, 6].length) (baseStart_911688 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_911688 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_911688 prefixEnd_911688 := by exact prefixLift 911688
  have htrace : WordTrace (prefixWord ++ tailWord_911688) baseStart_911688 baseEnd_911688 := by
    simpa [prefixWord, tailWord_911688, baseEnd_911688] using wordTrace_append hprefix tailTrace_911688
  have hstable : (prefixWord ++ tailWord_911688).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911688).length < 2 ^ (prefixWord ++ tailWord_911688).sum := by decide
  have hdescent : baseEnd_911688 < baseStart_911688 := by decide
  rcases family_descends (prefixWord ++ tailWord_911688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911701 : List Nat := [1, 3, 2, 2, 4, 1, 2, 3, 2]
def baseStart_911701 : Nat := 118140960795 + 911701 * 2 ^ 59
def prefixEnd_911701 : Nat := 4983230072969 + 3 ^ 40 * 911701 * 2
def baseEnd_911701 : Nat := 416125178830971288306373

theorem tailTrace_911701 : CollatzResearch.WordTrace tailWord_911701 prefixEnd_911701 416125178830971288306373 := by
  unfold tailWord_911701
  simp only [CollatzResearch.WordTrace]
  refine ⟨33252467270070457979510957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22168311513380305319673971 33252467270070457979510957)
  ·
    refine ⟨12469675226276421742316609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33252467270070457979510957 12469675226276421742316609)
    ·
      refine ⟨9352256419707316306737457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12469675226276421742316609 9352256419707316306737457)
      ·
        refine ⟨7014192314780487230053093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9352256419707316306737457 7014192314780487230053093)
        ·
          refine ⟨1315161059021341355634955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7014192314780487230053093 1315161059021341355634955)
          ·
            refine ⟨1972741588532012033452433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1315161059021341355634955 1972741588532012033452433)
            ·
              refine ⟨1479556191399009025089325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1972741588532012033452433 1479556191399009025089325)
              ·
                refine ⟨554833571774628384408497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1479556191399009025089325 554833571774628384408497)
                ·
                  refine ⟨416125178830971288306373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 554833571774628384408497 416125178830971288306373)
                  ·
                    rfl

theorem cell20_911701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 2, 3, 2].length) (baseStart_911701 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_911701 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_911701 prefixEnd_911701 := by exact prefixLift 911701
  have htrace : WordTrace (prefixWord ++ tailWord_911701) baseStart_911701 baseEnd_911701 := by
    simpa [prefixWord, tailWord_911701, baseEnd_911701] using wordTrace_append hprefix tailTrace_911701
  have hstable : (prefixWord ++ tailWord_911701).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911701).length < 2 ^ (prefixWord ++ tailWord_911701).sum := by decide
  have hdescent : baseEnd_911701 < baseStart_911701 := by decide
  rcases family_descends (prefixWord ++ tailWord_911701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911712 : List Nat := [2, 1, 1, 3, 5, 1, 7]
def baseStart_911712 : Nat := 118140960795 + 911712 * 2 ^ 59
def prefixEnd_911712 : Nat := 4983230072969 + 3 ^ 40 * 911712 * 2
def baseEnd_911712 : Nat := 46236688836744904326629

theorem tailTrace_911712 : CollatzResearch.WordTrace tailWord_911712 prefixEnd_911712 46236688836744904326629 := by
  unfold tailWord_911712
  simp only [CollatzResearch.WordTrace]
  refine ⟨16626434236515303429080695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22168578982020404572107593 16626434236515303429080695)
  ·
    refine ⟨24939651354772955143621043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16626434236515303429080695 24939651354772955143621043)
    ·
      refine ⟨37409477032159432715431565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24939651354772955143621043 37409477032159432715431565)
      ·
        refine ⟨14028553887059787268286837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37409477032159432715431565 14028553887059787268286837)
        ·
          refine ⟨1315176926911855056401891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14028553887059787268286837 1315176926911855056401891)
          ·
            refine ⟨1972765390367782584602837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1315176926911855056401891 1972765390367782584602837)
            ·
              refine ⟨46236688836744904326629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1972765390367782584602837 46236688836744904326629)
              ·
                rfl

theorem cell20_911712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 7].length) (baseStart_911712 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_911712 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_911712 prefixEnd_911712 := by exact prefixLift 911712
  have htrace : WordTrace (prefixWord ++ tailWord_911712) baseStart_911712 baseEnd_911712 := by
    simpa [prefixWord, tailWord_911712, baseEnd_911712] using wordTrace_append hprefix tailTrace_911712
  have hstable : (prefixWord ++ tailWord_911712).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911712).length < 2 ^ (prefixWord ++ tailWord_911712).sum := by decide
  have hdescent : baseEnd_911712 < baseStart_911712 := by decide
  rcases family_descends (prefixWord ++ tailWord_911712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911722 : List Nat := [3, 1, 3, 3, 1, 2, 2, 1, 4]
def baseStart_911722 : Nat := 118140960795 + 911722 * 2 ^ 59
def prefixEnd_911722 : Nat := 4983230072969 + 3 ^ 40 * 911722 * 2
def baseEnd_911722 : Nat := 416134763803188548606287

theorem tailTrace_911722 : CollatzResearch.WordTrace tailWord_911722 prefixEnd_911722 416134763803188548606287 := by
  unfold tailWord_911722
  simp only [CollatzResearch.WordTrace]
  refine ⟨8313308300748594641506355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22168822135329585710683613 8313308300748594641506355)
  ·
    refine ⟨12469962451122891962259533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8313308300748594641506355 12469962451122891962259533)
    ·
      refine ⟨4676235919171084485847325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12469962451122891962259533 4676235919171084485847325)
      ·
        refine ⟨1753588469689156682192747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4676235919171084485847325 1753588469689156682192747)
        ·
          refine ⟨2630382704533735023289121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1753588469689156682192747 2630382704533735023289121)
          ·
            refine ⟨1972787028400301267466841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2630382704533735023289121 1972787028400301267466841)
            ·
              refine ⟨1479590271300225950600131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1972787028400301267466841 1479590271300225950600131)
              ·
                refine ⟨2219385406950338925900197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1479590271300225950600131 2219385406950338925900197)
                ·
                  refine ⟨416134763803188548606287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2219385406950338925900197 416134763803188548606287)
                  ·
                    rfl

theorem cell20_911722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 2, 1, 4].length) (baseStart_911722 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_911722 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_911722 prefixEnd_911722 := by exact prefixLift 911722
  have htrace : WordTrace (prefixWord ++ tailWord_911722) baseStart_911722 baseEnd_911722 := by
    simpa [prefixWord, tailWord_911722, baseEnd_911722] using wordTrace_append hprefix tailTrace_911722
  have hstable : (prefixWord ++ tailWord_911722).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911722).length < 2 ^ (prefixWord ++ tailWord_911722).sum := by decide
  have hdescent : baseEnd_911722 < baseStart_911722 := by decide
  rcases family_descends (prefixWord ++ tailWord_911722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911746 : List Nat := [3, 4, 2, 1, 2, 1, 1, 6]
def baseStart_911746 : Nat := 118140960795 + 911746 * 2 ^ 59
def prefixEnd_911746 : Nat := 4983230072969 + 3 ^ 40 * 911746 * 2
def baseEnd_911746 : Nat := 138715239352383710602063

theorem tailTrace_911746 : CollatzResearch.WordTrace tailWord_911746 prefixEnd_911746 138715239352383710602063 := by
  unfold tailWord_911746
  simp only [CollatzResearch.WordTrace]
  refine ⟨8313527138726857666224773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22169405703271620443266061 8313527138726857666224773)
  ·
    refine ⟨1558786338511285812417145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8313527138726857666224773 1558786338511285812417145)
    ·
      refine ⟨1169089753883464359312859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1558786338511285812417145 1169089753883464359312859)
      ·
        refine ⟨1753634630825196538969289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1169089753883464359312859 1753634630825196538969289)
        ·
          refine ⟨1315225973118897404226967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1753634630825196538969289 1315225973118897404226967)
          ·
            refine ⟨1972838959678346106340451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1315225973118897404226967 1972838959678346106340451)
            ·
              refine ⟨2959258439517519159510677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1972838959678346106340451 2959258439517519159510677)
              ·
                refine ⟨138715239352383710602063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2959258439517519159510677 138715239352383710602063)
                ·
                  rfl

theorem cell20_911746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 6].length) (baseStart_911746 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_911746 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_911746 prefixEnd_911746 := by exact prefixLift 911746
  have htrace : WordTrace (prefixWord ++ tailWord_911746) baseStart_911746 baseEnd_911746 := by
    simpa [prefixWord, tailWord_911746, baseEnd_911746] using wordTrace_append hprefix tailTrace_911746
  have hstable : (prefixWord ++ tailWord_911746).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911746).length < 2 ^ (prefixWord ++ tailWord_911746).sum := by decide
  have hdescent : baseEnd_911746 < baseStart_911746 := by decide
  rcases family_descends (prefixWord ++ tailWord_911746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911777 : List Nat := [1, 2, 3, 5, 1, 2, 1, 1, 4]
def baseStart_911777 : Nat := 118140960795 + 911777 * 2 ^ 59
def prefixEnd_911777 : Nat := 4983230072969 + 3 ^ 40 * 911777 * 2
def baseEnd_911777 : Nat := 416159867301852801772729

theorem tailTrace_911777 : CollatzResearch.WordTrace tailWord_911777 prefixEnd_911777 416159867301852801772729 := by
  unfold tailWord_911777
  simp only [CollatzResearch.WordTrace]
  refine ⟨33255239217795122959277585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22170159478530081972851723 33255239217795122959277585)
  ·
    refine ⟨24941429413346342219458189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33255239217795122959277585 24941429413346342219458189)
    ·
      refine ⟨9353036030004878332296821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24941429413346342219458189 9353036030004878332296821)
      ·
        refine ⟨876847127812957343652827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9353036030004878332296821 876847127812957343652827)
        ·
          refine ⟨1315270691719436015479241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 876847127812957343652827 1315270691719436015479241)
          ·
            refine ⟨986453018789577011609431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1315270691719436015479241 986453018789577011609431)
            ·
              refine ⟨1479679528184365517414147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 986453018789577011609431 1479679528184365517414147)
              ·
                refine ⟨2219519292276548276121221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1479679528184365517414147 2219519292276548276121221)
                ·
                  refine ⟨416159867301852801772729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2219519292276548276121221 416159867301852801772729)
                  ·
                    rfl

theorem cell20_911777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 1, 1, 4].length) (baseStart_911777 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_911777 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_911777 prefixEnd_911777 := by exact prefixLift 911777
  have htrace : WordTrace (prefixWord ++ tailWord_911777) baseStart_911777 baseEnd_911777 := by
    simpa [prefixWord, tailWord_911777, baseEnd_911777] using wordTrace_append hprefix tailTrace_911777
  have hstable : (prefixWord ++ tailWord_911777).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911777).length < 2 ^ (prefixWord ++ tailWord_911777).sum := by decide
  have hdescent : baseEnd_911777 < baseStart_911777 := by decide
  rcases family_descends (prefixWord ++ tailWord_911777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911802 : List Nat := [3, 1, 1, 1, 2, 1, 1, 6, 4]
def baseStart_911802 : Nat := 118140960795 + 911802 * 2 ^ 59
def prefixEnd_911802 : Nat := 4983230072969 + 3 ^ 40 * 911802 * 2
def baseEnd_911802 : Nat := 416171277983063825939293

theorem tailTrace_911802 : CollatzResearch.WordTrace tailWord_911802 prefixEnd_911802 416171277983063825939293 := by
  unfold tailWord_911802
  simp only [CollatzResearch.WordTrace]
  refine ⟨8314037760676138057234415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22170767361803034819291773 8314037760676138057234415)
  ·
    refine ⟨12471056641014207085851623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8314037760676138057234415 12471056641014207085851623)
    ·
      refine ⟨18706584961521310628777435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12471056641014207085851623 18706584961521310628777435)
      ·
        refine ⟨28059877442281965943166153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18706584961521310628777435 28059877442281965943166153)
        ·
          refine ⟨21044908081711474457374615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28059877442281965943166153 21044908081711474457374615)
          ·
            refine ⟨31567362122567211686061923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21044908081711474457374615 31567362122567211686061923)
            ·
              refine ⟨47351043183850817529092885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31567362122567211686061923 47351043183850817529092885)
              ·
                refine ⟨2219580149243007071676229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 47351043183850817529092885 2219580149243007071676229)
                ·
                  refine ⟨416171277983063825939293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2219580149243007071676229 416171277983063825939293)
                  ·
                    rfl

theorem cell20_911802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 6, 4].length) (baseStart_911802 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_911802 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_911802 prefixEnd_911802 := by exact prefixLift 911802
  have htrace : WordTrace (prefixWord ++ tailWord_911802) baseStart_911802 baseEnd_911802 := by
    simpa [prefixWord, tailWord_911802, baseEnd_911802] using wordTrace_append hprefix tailTrace_911802
  have hstable : (prefixWord ++ tailWord_911802).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911802).length < 2 ^ (prefixWord ++ tailWord_911802).sum := by decide
  have hdescent : baseEnd_911802 < baseStart_911802 := by decide
  rcases family_descends (prefixWord ++ tailWord_911802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911819 : List Nat := [1, 1, 1, 1, 3, 3, 1, 7, 2]
def baseStart_911819 : Nat := 118140960795 + 911819 * 2 ^ 59
def prefixEnd_911819 : Nat := 4983230072969 + 3 ^ 40 * 911819 * 2
def baseEnd_911819 : Nat := 416179037246287322372557

theorem tailTrace_911819 : CollatzResearch.WordTrace tailWord_911819 prefixEnd_911819 416179037246287322372557 := by
  unfold tailWord_911819
  simp only [CollatzResearch.WordTrace]
  refine ⟨33256771083642964132306511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22171180722428642754871007 33256771083642964132306511)
  ·
    refine ⟨49885156625464446198459767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33256771083642964132306511 49885156625464446198459767)
    ·
      refine ⟨74827734938196669297689651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49885156625464446198459767 74827734938196669297689651)
      ·
        refine ⟨112241602407295003946534477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74827734938196669297689651 112241602407295003946534477)
        ·
          refine ⟨42090600902735626479950429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112241602407295003946534477 42090600902735626479950429)
          ·
            refine ⟨15783975338525859929981411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42090600902735626479950429 15783975338525859929981411)
            ·
              refine ⟨23675963007788789894972117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15783975338525859929981411 23675963007788789894972117)
              ·
                refine ⟨554905382995049763163409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 23675963007788789894972117 554905382995049763163409)
                ·
                  refine ⟨416179037246287322372557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 554905382995049763163409 416179037246287322372557)
                  ·
                    rfl

theorem cell20_911819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 7, 2].length) (baseStart_911819 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_911819 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_911819 prefixEnd_911819 := by exact prefixLift 911819
  have htrace : WordTrace (prefixWord ++ tailWord_911819) baseStart_911819 baseEnd_911819 := by
    simpa [prefixWord, tailWord_911819, baseEnd_911819] using wordTrace_append hprefix tailTrace_911819
  have hstable : (prefixWord ++ tailWord_911819).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911819).length < 2 ^ (prefixWord ++ tailWord_911819).sum := by decide
  have hdescent : baseEnd_911819 < baseStart_911819 := by decide
  rcases family_descends (prefixWord ++ tailWord_911819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911826 : List Nat := [3, 2, 2, 4, 9]
def baseStart_911826 : Nat := 118140960795 + 911826 * 2 ^ 59
def prefixEnd_911826 : Nat := 4983230072969 + 3 ^ 40 * 911826 * 2
def baseEnd_911826 : Nat := 5138052249839832211595

theorem tailTrace_911826 : CollatzResearch.WordTrace tailWord_911826 prefixEnd_911826 5138052249839832211595 := by
  unfold tailWord_911826
  simp only [CollatzResearch.WordTrace]
  refine ⟨8314256598654401081952833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22171350929745069551874221 8314256598654401081952833)
  ·
    refine ⟨6235692448990800811464625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8314256598654401081952833 6235692448990800811464625)
    ·
      refine ⟨4676769336743100608598469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6235692448990800811464625 4676769336743100608598469)
      ·
        refine ⟨876894250639331364112213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4676769336743100608598469 876894250639331364112213)
        ·
          refine ⟨5138052249839832211595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 876894250639331364112213 5138052249839832211595)
          ·
            rfl

theorem cell20_911826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 9].length) (baseStart_911826 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_911826 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_911826 prefixEnd_911826 := by exact prefixLift 911826
  have htrace : WordTrace (prefixWord ++ tailWord_911826) baseStart_911826 baseEnd_911826 := by
    simpa [prefixWord, tailWord_911826, baseEnd_911826] using wordTrace_append hprefix tailTrace_911826
  have hstable : (prefixWord ++ tailWord_911826).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911826).length < 2 ^ (prefixWord ++ tailWord_911826).sum := by decide
  have hdescent : baseEnd_911826 < baseStart_911826 := by decide
  rcases family_descends (prefixWord ++ tailWord_911826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911840 : List Nat := [2, 1, 1, 3, 1, 1, 4, 3, 4]
def baseStart_911840 : Nat := 118140960795 + 911840 * 2 ^ 59
def prefixEnd_911840 : Nat := 4983230072969 + 3 ^ 40 * 911840 * 2
def baseEnd_911840 : Nat := 416188622218504582672471

theorem tailTrace_911840 : CollatzResearch.WordTrace tailWord_911840 prefixEnd_911840 416188622218504582672471 := by
  unfold tailWord_911840
  simp only [CollatzResearch.WordTrace]
  refine ⟨16628768508283442359410487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22171691344377923145880649 16628768508283442359410487)
  ·
    refine ⟨24943152762425163539115731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16628768508283442359410487 24943152762425163539115731)
    ·
      refine ⟨37414729143637745308673597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24943152762425163539115731 37414729143637745308673597)
      ·
        refine ⟨14030523428864154490752599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37414729143637745308673597 14030523428864154490752599)
        ·
          refine ⟨21045785143296231736128899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14030523428864154490752599 21045785143296231736128899)
          ·
            refine ⟨31568677714944347604193349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21045785143296231736128899 31568677714944347604193349)
            ·
              refine ⟨5919127071552065175786253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31568677714944347604193349 5919127071552065175786253)
              ·
                refine ⟨2219672651832024440919845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5919127071552065175786253 2219672651832024440919845)
                ·
                  refine ⟨416188622218504582672471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2219672651832024440919845 416188622218504582672471)
                  ·
                    rfl

theorem cell20_911840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 3, 4].length) (baseStart_911840 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_911840 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_911840 prefixEnd_911840 := by exact prefixLift 911840
  have htrace : WordTrace (prefixWord ++ tailWord_911840) baseStart_911840 baseEnd_911840 := by
    simpa [prefixWord, tailWord_911840, baseEnd_911840] using wordTrace_append hprefix tailTrace_911840
  have hstable : (prefixWord ++ tailWord_911840).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911840).length < 2 ^ (prefixWord ++ tailWord_911840).sum := by decide
  have hdescent : baseEnd_911840 < baseStart_911840 := by decide
  rcases family_descends (prefixWord ++ tailWord_911840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911843 : List Nat := [1, 1, 1, 6, 3, 2, 1, 5]
def baseStart_911843 : Nat := 118140960795 + 911843 * 2 ^ 59
def prefixEnd_911843 : Nat := 4983230072969 + 3 ^ 40 * 911843 * 2
def baseEnd_911843 : Nat := 138729997166749968524153

theorem tailTrace_911843 : CollatzResearch.WordTrace tailWord_911843 prefixEnd_911843 138729997166749968524153 := by
  unfold tailWord_911843
  simp only [CollatzResearch.WordTrace]
  refine ⟨33257646435556016231180183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22171764290370677487453455 33257646435556016231180183)
  ·
    refine ⟨49886469653334024346770275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33257646435556016231180183 49886469653334024346770275)
    ·
      refine ⟨74829704480001036520155413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49886469653334024346770275 74829704480001036520155413)
      ·
        refine ⟨3507642397500048586882285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 74829704480001036520155413 3507642397500048586882285)
        ·
          refine ⟨1315365899062518220080857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3507642397500048586882285 1315365899062518220080857)
          ·
            refine ⟨986524424296888665060643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1315365899062518220080857 986524424296888665060643)
            ·
              refine ⟨1479786636445332997590965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 986524424296888665060643 1479786636445332997590965)
              ·
                refine ⟨138729997166749968524153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1479786636445332997590965 138729997166749968524153)
                ·
                  rfl

theorem cell20_911843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 1, 5].length) (baseStart_911843 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_911843 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_911843 prefixEnd_911843 := by exact prefixLift 911843
  have htrace : WordTrace (prefixWord ++ tailWord_911843) baseStart_911843 baseEnd_911843 := by
    simpa [prefixWord, tailWord_911843, baseEnd_911843] using wordTrace_append hprefix tailTrace_911843
  have hstable : (prefixWord ++ tailWord_911843).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911843).length < 2 ^ (prefixWord ++ tailWord_911843).sum := by decide
  have hdescent : baseEnd_911843 < baseStart_911843 := by decide
  rcases family_descends (prefixWord ++ tailWord_911843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911850 : List Nat := [3, 1, 3, 1, 3, 1, 2, 3, 3]
def baseStart_911850 : Nat := 118140960795 + 911850 * 2 ^ 59
def prefixEnd_911850 : Nat := 4983230072969 + 3 ^ 40 * 911850 * 2
def baseEnd_911850 : Nat := 416193186490988992339097

theorem tailTrace_911850 : CollatzResearch.WordTrace tailWord_911850 prefixEnd_911850 416193186490988992339097 := by
  unfold tailWord_911850
  simp only [CollatzResearch.WordTrace]
  refine ⟨8314475436632664106671251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22171934497687104284456669 8314475436632664106671251)
  ·
    refine ⟨12471713154948996160006877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8314475436632664106671251 12471713154948996160006877)
    ·
      refine ⟨4676892433105873560002579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12471713154948996160006877 4676892433105873560002579)
      ·
        refine ⟨7015338649658810340003869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4676892433105873560002579 7015338649658810340003869)
        ·
          refine ⟨2630751993622053877501451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7015338649658810340003869 2630751993622053877501451)
          ·
            refine ⟨3946127990433080816252177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2630751993622053877501451 3946127990433080816252177)
            ·
              refine ⟨2959595992824810612189133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3946127990433080816252177 2959595992824810612189133)
              ·
                refine ⟨1109848497309303979570925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2959595992824810612189133 1109848497309303979570925)
                ·
                  refine ⟨416193186490988992339097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1109848497309303979570925 416193186490988992339097)
                  ·
                    rfl

theorem cell20_911850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 3, 3].length) (baseStart_911850 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_911850 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_911850 prefixEnd_911850 := by exact prefixLift 911850
  have htrace : WordTrace (prefixWord ++ tailWord_911850) baseStart_911850 baseEnd_911850 := by
    simpa [prefixWord, tailWord_911850, baseEnd_911850] using wordTrace_append hprefix tailTrace_911850
  have hstable : (prefixWord ++ tailWord_911850).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911850).length < 2 ^ (prefixWord ++ tailWord_911850).sum := by decide
  have hdescent : baseEnd_911850 < baseStart_911850 := by decide
  rcases family_descends (prefixWord ++ tailWord_911850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911864 : List Nat := [2, 1, 2, 1, 1, 4, 5, 4]
def baseStart_911864 : Nat := 118140960795 + 911864 * 2 ^ 59
def prefixEnd_911864 : Nat := 4983230072969 + 3 ^ 40 * 911864 * 2
def baseEnd_911864 : Nat := 138733192157489055290791

theorem tailTrace_911864 : CollatzResearch.WordTrace tailWord_911864 prefixEnd_911864 138733192157489055290791 := by
  unfold tailWord_911864
  simp only [CollatzResearch.WordTrace]
  refine ⟨16629206184239968408847323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22172274912319957878463097 16629206184239968408847323)
  ·
    refine ⟨24943809276359952613270985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16629206184239968408847323 24943809276359952613270985)
    ·
      refine ⟨18707856957269964459953239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24943809276359952613270985 18707856957269964459953239)
      ·
        refine ⟨28061785435904946689929859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18707856957269964459953239 28061785435904946689929859)
        ·
          refine ⟨42092678153857420034894789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28061785435904946689929859 42092678153857420034894789)
          ·
            refine ⟨7892377153848266256542773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42092678153857420034894789 7892377153848266256542773)
            ·
              refine ⟨739910358173274961550885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7892377153848266256542773 739910358173274961550885)
              ·
                refine ⟨138733192157489055290791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 739910358173274961550885 138733192157489055290791)
                ·
                  rfl

theorem cell20_911864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 5, 4].length) (baseStart_911864 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_911864 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_911864 prefixEnd_911864 := by exact prefixLift 911864
  have htrace : WordTrace (prefixWord ++ tailWord_911864) baseStart_911864 baseEnd_911864 := by
    simpa [prefixWord, tailWord_911864, baseEnd_911864] using wordTrace_append hprefix tailTrace_911864
  have hstable : (prefixWord ++ tailWord_911864).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911864).length < 2 ^ (prefixWord ++ tailWord_911864).sum := by decide
  have hdescent : baseEnd_911864 < baseStart_911864 := by decide
  rcases family_descends (prefixWord ++ tailWord_911864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911909 : List Nat := [1, 3, 1, 2, 2, 1, 2, 5, 3]
def baseStart_911909 : Nat := 118140960795 + 911909 * 2 ^ 59
def prefixEnd_911909 : Nat := 4983230072969 + 3 ^ 40 * 911909 * 2
def baseEnd_911909 : Nat := 416220115698647009372189

theorem tailTrace_911909 : CollatzResearch.WordTrace tailWord_911909 prefixEnd_911909 416220115698647009372189 := by
  unfold tailWord_911909
  simp only [CollatzResearch.WordTrace]
  refine ⟨33260053653316909503082781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22173369102211273002055187 33260053653316909503082781)
  ·
    refine ⟨12472520119993841063656043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33260053653316909503082781 12472520119993841063656043)
    ·
      refine ⟨18708780179990761595484065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12472520119993841063656043 18708780179990761595484065)
      ·
        refine ⟨14031585134993071196613049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18708780179990761595484065 14031585134993071196613049)
        ·
          refine ⟨10523688851244803397459787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14031585134993071196613049 10523688851244803397459787)
          ·
            refine ⟨15785533276867205096189681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10523688851244803397459787 15785533276867205096189681)
            ·
              refine ⟨11839149957650403822142261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15785533276867205096189681 11839149957650403822142261)
              ·
                refine ⟨1109920308529725358325837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11839149957650403822142261 1109920308529725358325837)
                ·
                  refine ⟨416220115698647009372189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1109920308529725358325837 416220115698647009372189)
                  ·
                    rfl

theorem cell20_911909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 5, 3].length) (baseStart_911909 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_911909 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_911909 prefixEnd_911909 := by exact prefixLift 911909
  have htrace : WordTrace (prefixWord ++ tailWord_911909) baseStart_911909 baseEnd_911909 := by
    simpa [prefixWord, tailWord_911909, baseEnd_911909] using wordTrace_append hprefix tailTrace_911909
  have hstable : (prefixWord ++ tailWord_911909).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911909).length < 2 ^ (prefixWord ++ tailWord_911909).sum := by decide
  have hdescent : baseEnd_911909 < baseStart_911909 := by decide
  rcases family_descends (prefixWord ++ tailWord_911909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911923 : List Nat := [1, 1, 1, 2, 4, 2, 3, 6]
def baseStart_911923 : Nat := 118140960795 + 911923 * 2 ^ 59
def prefixEnd_911923 : Nat := 4983230072969 + 3 ^ 40 * 911923 * 2
def baseEnd_911923 : Nat := 138742168560041727635155

theorem tailTrace_911923 : CollatzResearch.WordTrace tailWord_911923 prefixEnd_911923 138742168560041727635155 := by
  unfold tailWord_911923
  simp only [CollatzResearch.WordTrace]
  refine ⟨33260564275266189894092423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22173709516844126596061615 33260564275266189894092423)
  ·
    refine ⟨49890846412899284841138635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33260564275266189894092423 49890846412899284841138635)
    ·
      refine ⟨74836269619348927261707953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49890846412899284841138635 74836269619348927261707953)
      ·
        refine ⟨56127202214511695446280965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74836269619348927261707953 56127202214511695446280965)
        ·
          refine ⟨10523850415220942896177681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56127202214511695446280965 10523850415220942896177681)
          ·
            refine ⟨7892887811415707172133261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10523850415220942896177681 7892887811415707172133261)
            ·
              refine ⟨2959832929280890189549973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7892887811415707172133261 2959832929280890189549973)
              ·
                refine ⟨138742168560041727635155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2959832929280890189549973 138742168560041727635155)
                ·
                  rfl

theorem cell20_911923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 6].length) (baseStart_911923 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_911923 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_911923 prefixEnd_911923 := by exact prefixLift 911923
  have htrace : WordTrace (prefixWord ++ tailWord_911923) baseStart_911923 baseEnd_911923 := by
    simpa [prefixWord, tailWord_911923, baseEnd_911923] using wordTrace_append hprefix tailTrace_911923
  have hstable : (prefixWord ++ tailWord_911923).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911923).length < 2 ^ (prefixWord ++ tailWord_911923).sum := by decide
  have hdescent : baseEnd_911923 < baseStart_911923 := by decide
  rcases family_descends (prefixWord ++ tailWord_911923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_911926 : List Nat := [5, 1, 2, 1, 2, 1, 1, 2, 5]
def baseStart_911926 : Nat := 118140960795 + 911926 * 2 ^ 59
def prefixEnd_911926 : Nat := 4983230072969 + 3 ^ 40 * 911926 * 2
def baseEnd_911926 : Nat := 416227874961870505805453

theorem tailTrace_911926 : CollatzResearch.WordTrace tailWord_911926 prefixEnd_911926 416227874961870505805453 := by
  unfold tailWord_911926
  simp only [CollatzResearch.WordTrace]
  refine ⟨2078792105890957587903227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22173782462836880937634421 2078792105890957587903227)
  ·
    refine ⟨3118188158836436381854841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2078792105890957587903227 3118188158836436381854841)
    ·
      refine ⟨2338641119127327286391131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3118188158836436381854841 2338641119127327286391131)
      ·
        refine ⟨3507961678690990929586697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2338641119127327286391131 3507961678690990929586697)
        ·
          refine ⟨2630971259018243197190023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3507961678690990929586697 2630971259018243197190023)
          ·
            refine ⟨3946456888527364795785035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2630971259018243197190023 3946456888527364795785035)
            ·
              refine ⟨5919685332791047193677553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3946456888527364795785035 5919685332791047193677553)
              ·
                refine ⟨4439763999593285395258165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5919685332791047193677553 4439763999593285395258165)
                ·
                  refine ⟨416227874961870505805453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4439763999593285395258165 416227874961870505805453)
                  ·
                    rfl

theorem cell20_911926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_911926 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_911926 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_911926 prefixEnd_911926 := by exact prefixLift 911926
  have htrace : WordTrace (prefixWord ++ tailWord_911926) baseStart_911926 baseEnd_911926 := by
    simpa [prefixWord, tailWord_911926, baseEnd_911926] using wordTrace_append hprefix tailTrace_911926
  have hstable : (prefixWord ++ tailWord_911926).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_911926).length < 2 ^ (prefixWord ++ tailWord_911926).sum := by decide
  have hdescent : baseEnd_911926 < baseStart_911926 := by decide
  rcases family_descends (prefixWord ++ tailWord_911926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912005 : List Nat := [1, 3, 1, 1, 4, 4, 2, 2, 2]
def baseStart_912005 : Nat := 118140960795 + 912005 * 2 ^ 59
def prefixEnd_912005 : Nat := 4983230072969 + 3 ^ 40 * 912005 * 2
def baseEnd_912005 : Nat := 416263932714497342171797

theorem tailTrace_912005 : CollatzResearch.WordTrace tailWord_912005 prefixEnd_912005 416263932714497342171797 := by
  unfold tailWord_912005
  simp only [CollatzResearch.WordTrace]
  refine ⟨33263555060969117898577469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22175703373979411932384979 33263555060969117898577469)
  ·
    refine ⟨12473833147863419211966551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33263555060969117898577469 12473833147863419211966551)
    ·
      refine ⟨18710749721795128817949827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12473833147863419211966551 18710749721795128817949827)
      ·
        refine ⟨28066124582692693226924741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18710749721795128817949827 28066124582692693226924741)
        ·
          refine ⟨5262398359254879980048389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28066124582692693226924741 5262398359254879980048389)
          ·
            refine ⟨986699692360289996259073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5262398359254879980048389 986699692360289996259073)
            ·
              refine ⟨740024769270217497194305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 986699692360289996259073 740024769270217497194305)
              ·
                refine ⟨555018576952663122895729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 740024769270217497194305 555018576952663122895729)
                ·
                  refine ⟨416263932714497342171797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 555018576952663122895729 416263932714497342171797)
                  ·
                    rfl

theorem cell20_912005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 2, 2, 2].length) (baseStart_912005 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_912005 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_912005 prefixEnd_912005 := by exact prefixLift 912005
  have htrace : WordTrace (prefixWord ++ tailWord_912005) baseStart_912005 baseEnd_912005 := by
    simpa [prefixWord, tailWord_912005, baseEnd_912005] using wordTrace_append hprefix tailTrace_912005
  have hstable : (prefixWord ++ tailWord_912005).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912005).length < 2 ^ (prefixWord ++ tailWord_912005).sum := by decide
  have hdescent : baseEnd_912005 < baseStart_912005 := by decide
  rcases family_descends (prefixWord ++ tailWord_912005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912023 : List Nat := [1, 1, 3, 3, 2, 1, 1, 5, 3]
def baseStart_912023 : Nat := 118140960795 + 912023 * 2 ^ 59
def prefixEnd_912023 : Nat := 4983230072969 + 3 ^ 40 * 912023 * 2
def baseEnd_912023 : Nat := 416272148404969279571723

theorem tailTrace_912023 : CollatzResearch.WordTrace tailWord_912023 prefixEnd_912023 416272148404969279571723 := by
  unfold tailWord_912023
  simp only [CollatzResearch.WordTrace]
  refine ⟨33264211574903906972732723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22176141049935937981821815 33264211574903906972732723)
  ·
    refine ⟨49896317362355860459099085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33264211574903906972732723 49896317362355860459099085)
    ·
      refine ⟨18711119010883447672162157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49896317362355860459099085 18711119010883447672162157)
      ·
        refine ⟨7016669629081292877060809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18711119010883447672162157 7016669629081292877060809)
        ·
          refine ⟨5262502221810969657795607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7016669629081292877060809 5262502221810969657795607)
          ·
            refine ⟨7893753332716454486693411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5262502221810969657795607 7893753332716454486693411)
            ·
              refine ⟨11840629999074681730040117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7893753332716454486693411 11840629999074681730040117)
              ·
                refine ⟨1110059062413251412191261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11840629999074681730040117 1110059062413251412191261)
                ·
                  refine ⟨416272148404969279571723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1110059062413251412191261 416272148404969279571723)
                  ·
                    rfl

theorem cell20_912023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 5, 3].length) (baseStart_912023 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_912023 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_912023 prefixEnd_912023 := by exact prefixLift 912023
  have htrace : WordTrace (prefixWord ++ tailWord_912023) baseStart_912023 baseEnd_912023 := by
    simpa [prefixWord, tailWord_912023, baseEnd_912023] using wordTrace_append hprefix tailTrace_912023
  have hstable : (prefixWord ++ tailWord_912023).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912023).length < 2 ^ (prefixWord ++ tailWord_912023).sum := by decide
  have hdescent : baseEnd_912023 < baseStart_912023 := by decide
  rcases family_descends (prefixWord ++ tailWord_912023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912026 : List Nat := [3, 1, 1, 6, 1, 1, 1, 2, 4]
def baseStart_912026 : Nat := 118140960795 + 912026 * 2 ^ 59
def prefixEnd_912026 : Nat := 4983230072969 + 3 ^ 40 * 912026 * 2
def baseEnd_912026 : Nat := 416273517686714602471711

theorem tailTrace_912026 : CollatzResearch.WordTrace tailWord_912026 prefixEnd_912026 416273517686714602471711 := by
  unfold tailWord_912026
  simp only [CollatzResearch.WordTrace]
  refine ⟨8316080248473259621272983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22176213995928692323394621 8316080248473259621272983)
  ·
    refine ⟨12474120372709889431909475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8316080248473259621272983 12474120372709889431909475)
    ·
      refine ⟨18711180559064834147864213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12474120372709889431909475 18711180559064834147864213)
      ·
        refine ⟨877086588706164100681135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 18711180559064834147864213 877086588706164100681135)
        ·
          refine ⟨1315629883059246151021703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 877086588706164100681135 1315629883059246151021703)
          ·
            refine ⟨1973444824588869226532555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1315629883059246151021703 1973444824588869226532555)
            ·
              refine ⟨2960167236883303839798833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1973444824588869226532555 2960167236883303839798833)
              ·
                refine ⟨2220125427662477879849125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2960167236883303839798833 2220125427662477879849125)
                ·
                  refine ⟨416273517686714602471711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2220125427662477879849125 416273517686714602471711)
                  ·
                    rfl

theorem cell20_912026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 2, 4].length) (baseStart_912026 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_912026 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_912026 prefixEnd_912026 := by exact prefixLift 912026
  have htrace : WordTrace (prefixWord ++ tailWord_912026) baseStart_912026 baseEnd_912026 := by
    simpa [prefixWord, tailWord_912026, baseEnd_912026] using wordTrace_append hprefix tailTrace_912026
  have hstable : (prefixWord ++ tailWord_912026).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912026).length < 2 ^ (prefixWord ++ tailWord_912026).sum := by decide
  have hdescent : baseEnd_912026 < baseStart_912026 := by decide
  rcases family_descends (prefixWord ++ tailWord_912026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912033 : List Nat := [1, 2, 3, 3, 3, 1, 3, 4]
def baseStart_912033 : Nat := 118140960795 + 912033 * 2 ^ 59
def prefixEnd_912033 : Nat := 4983230072969 + 3 ^ 40 * 912033 * 2
def baseEnd_912033 : Nat := 138758904225817896412783

theorem tailTrace_912033 : CollatzResearch.WordTrace tailWord_912033 prefixEnd_912033 138758904225817896412783 := by
  unfold tailWord_912033
  simp only [CollatzResearch.WordTrace]
  refine ⟨33264576304867678680596753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22176384203245119120397835 33264576304867678680596753)
  ·
    refine ⟨24948432228650759010447565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33264576304867678680596753 24948432228650759010447565)
    ·
      refine ⟨9355662085744034628917837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24948432228650759010447565 9355662085744034628917837)
      ·
        refine ⟨3508373282154012985844189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9355662085744034628917837 3508373282154012985844189)
        ·
          refine ⟨1315639980807754869691571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3508373282154012985844189 1315639980807754869691571)
          ·
            refine ⟨1973459971211632304537357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1315639980807754869691571 1973459971211632304537357)
            ·
              refine ⟨740047489204362114201509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1973459971211632304537357 740047489204362114201509)
              ·
                refine ⟨138758904225817896412783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 740047489204362114201509 138758904225817896412783)
                ·
                  rfl

theorem cell20_912033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 3, 4].length) (baseStart_912033 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_912033 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_912033 prefixEnd_912033 := by exact prefixLift 912033
  have htrace : WordTrace (prefixWord ++ tailWord_912033) baseStart_912033 baseEnd_912033 := by
    simpa [prefixWord, tailWord_912033, baseEnd_912033] using wordTrace_append hprefix tailTrace_912033
  have hstable : (prefixWord ++ tailWord_912033).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912033).length < 2 ^ (prefixWord ++ tailWord_912033).sum := by decide
  have hdescent : baseEnd_912033 < baseStart_912033 := by decide
  rcases family_descends (prefixWord ++ tailWord_912033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912047 : List Nat := [1, 1, 2, 1, 2, 5, 1, 5, 2]
def baseStart_912047 : Nat := 118140960795 + 912047 * 2 ^ 59
def prefixEnd_912047 : Nat := 4983230072969 + 3 ^ 40 * 912047 * 2
def baseEnd_912047 : Nat := 416283102658931862771625

theorem tailTrace_912047 : CollatzResearch.WordTrace tailWord_912047 prefixEnd_912047 416283102658931862771625 := by
  unfold tailWord_912047
  simp only [CollatzResearch.WordTrace]
  refine ⟨33265086926816959071606395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22176724617877972714404263 33265086926816959071606395)
  ·
    refine ⟨49897630390225438607409593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33265086926816959071606395 49897630390225438607409593)
    ·
      refine ⟨37423222792669078955557195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49897630390225438607409593 37423222792669078955557195)
      ·
        refine ⟨56134834189003618433335793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37423222792669078955557195 56134834189003618433335793)
        ·
          refine ⟨42101125641752713825001845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56134834189003618433335793 42101125641752713825001845)
          ·
            refine ⟨3946980528914316921093923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42101125641752713825001845 3946980528914316921093923)
            ·
              refine ⟨5920470793371475381640885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3946980528914316921093923 5920470793371475381640885)
              ·
                refine ⟨555044136878575817028833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5920470793371475381640885 555044136878575817028833)
                ·
                  refine ⟨416283102658931862771625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 555044136878575817028833 416283102658931862771625)
                  ·
                    rfl

theorem cell20_912047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 5, 2].length) (baseStart_912047 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_912047 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_912047 prefixEnd_912047 := by exact prefixLift 912047
  have htrace : WordTrace (prefixWord ++ tailWord_912047) baseStart_912047 baseEnd_912047 := by
    simpa [prefixWord, tailWord_912047, baseEnd_912047] using wordTrace_append hprefix tailTrace_912047
  have hstable : (prefixWord ++ tailWord_912047).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912047).length < 2 ^ (prefixWord ++ tailWord_912047).sum := by decide
  have hdescent : baseEnd_912047 < baseStart_912047 := by decide
  rcases family_descends (prefixWord ++ tailWord_912047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912061 : List Nat := [1, 4, 1, 2, 1, 4, 1, 1, 5]
def baseStart_912061 : Nat := 118140960795 + 912061 * 2 ^ 59
def prefixEnd_912061 : Nat := 4983230072969 + 3 ^ 40 * 912061 * 2
def baseEnd_912061 : Nat := 416289492640410036304901

theorem tailTrace_912061 : CollatzResearch.WordTrace tailWord_912061 prefixEnd_912061 416289492640410036304901 := by
  unfold tailWord_912061
  simp only [CollatzResearch.WordTrace]
  refine ⟨33265597548766239462616037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22177065032510826308410691 33265597548766239462616037)
  ·
    refine ⟨6237299540393669899240507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33265597548766239462616037 6237299540393669899240507)
    ·
      refine ⟨9355949310590504848860761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6237299540393669899240507 9355949310590504848860761)
      ·
        refine ⟨7016961982942878636645571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9355949310590504848860761 7016961982942878636645571)
        ·
          refine ⟨10525442974414317954968357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7016961982942878636645571 10525442974414317954968357)
          ·
            refine ⟨1973520557702684616556567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10525442974414317954968357 1973520557702684616556567)
            ·
              refine ⟨2960280836554026924834851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1973520557702684616556567 2960280836554026924834851)
              ·
                refine ⟨4440421254831040387252277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2960280836554026924834851 4440421254831040387252277)
                ·
                  refine ⟨416289492640410036304901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4440421254831040387252277 416289492640410036304901)
                  ·
                    rfl

theorem cell20_912061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 1, 5].length) (baseStart_912061 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_912061 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_912061 prefixEnd_912061 := by exact prefixLift 912061
  have htrace : WordTrace (prefixWord ++ tailWord_912061) baseStart_912061 baseEnd_912061 := by
    simpa [prefixWord, tailWord_912061, baseEnd_912061] using wordTrace_append hprefix tailTrace_912061
  have hstable : (prefixWord ++ tailWord_912061).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912061).length < 2 ^ (prefixWord ++ tailWord_912061).sum := by decide
  have hdescent : baseEnd_912061 < baseStart_912061 := by decide
  rcases family_descends (prefixWord ++ tailWord_912061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912099 : List Nat := [1, 1, 1, 7, 1, 1, 1, 2, 5]
def baseStart_912099 : Nat := 118140960795 + 912099 * 2 ^ 59
def prefixEnd_912099 : Nat := 4983230072969 + 3 ^ 40 * 912099 * 2
def baseEnd_912099 : Nat := 416306836875850793038079

theorem tailTrace_912099 : CollatzResearch.WordTrace tailWord_912099 prefixEnd_912099 416306836875850793038079 := by
  unfold tailWord_912099
  simp only [CollatzResearch.WordTrace]
  refine ⟨33266983522628571952499351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22177989015085714634999567 33266983522628571952499351)
  ·
    refine ⟨49900475283942857928749027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33266983522628571952499351 49900475283942857928749027)
    ·
      refine ⟨74850712925914286893123541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49900475283942857928749027 74850712925914286893123541)
      ·
        refine ⟨1754313584201116099057583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 74850712925914286893123541 1754313584201116099057583)
        ·
          refine ⟨2631470376301674148586375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1754313584201116099057583 2631470376301674148586375)
          ·
            refine ⟨3947205564452511222879563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2631470376301674148586375 3947205564452511222879563)
            ·
              refine ⟨5920808346678766834319345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3947205564452511222879563 5920808346678766834319345)
              ·
                refine ⟨4440606260009075125739509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5920808346678766834319345 4440606260009075125739509)
                ·
                  refine ⟨416306836875850793038079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4440606260009075125739509 416306836875850793038079)
                  ·
                    rfl

theorem cell20_912099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 2, 5].length) (baseStart_912099 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_912099 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_912099 prefixEnd_912099 := by exact prefixLift 912099
  have htrace : WordTrace (prefixWord ++ tailWord_912099) baseStart_912099 baseEnd_912099 := by
    simpa [prefixWord, tailWord_912099, baseEnd_912099] using wordTrace_append hprefix tailTrace_912099
  have hstable : (prefixWord ++ tailWord_912099).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912099).length < 2 ^ (prefixWord ++ tailWord_912099).sum := by decide
  have hdescent : baseEnd_912099 < baseStart_912099 := by decide
  rcases family_descends (prefixWord ++ tailWord_912099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912120 : List Nat := [2, 1, 2, 1, 1, 2, 3, 3, 5]
def baseStart_912120 : Nat := 118140960795 + 912120 * 2 ^ 59
def prefixEnd_912120 : Nat := 4983230072969 + 3 ^ 40 * 912120 * 2
def baseEnd_912120 : Nat := 416316421848068053337993

theorem tailTrace_912120 : CollatzResearch.WordTrace tailWord_912120 prefixEnd_912120 416316421848068053337993 := by
  unfold tailWord_912120
  simp only [CollatzResearch.WordTrace]
  refine ⟨16633874727776246269506907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22178499637034995026009209 16633874727776246269506907)
  ·
    refine ⟨24950812091664369404260361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16633874727776246269506907 24950812091664369404260361)
    ·
      refine ⟨18713109068748277053195271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24950812091664369404260361 18713109068748277053195271)
      ·
        refine ⟨28069663603122415579792907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18713109068748277053195271 28069663603122415579792907)
        ·
          refine ⟨42104495404683623369689361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28069663603122415579792907 42104495404683623369689361)
          ·
            refine ⟨31578371553512717527267021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42104495404683623369689361 31578371553512717527267021)
            ·
              refine ⟨11841889332567269072725133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31578371553512717527267021 11841889332567269072725133)
              ·
                refine ⟨4440708499712725902271925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11841889332567269072725133 4440708499712725902271925)
                ·
                  refine ⟨416316421848068053337993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4440708499712725902271925 416316421848068053337993)
                  ·
                    rfl

theorem cell20_912120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 3, 5].length) (baseStart_912120 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_912120 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_912120 prefixEnd_912120 := by exact prefixLift 912120
  have htrace : WordTrace (prefixWord ++ tailWord_912120) baseStart_912120 baseEnd_912120 := by
    simpa [prefixWord, tailWord_912120, baseEnd_912120] using wordTrace_append hprefix tailTrace_912120
  have hstable : (prefixWord ++ tailWord_912120).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912120).length < 2 ^ (prefixWord ++ tailWord_912120).sum := by decide
  have hdescent : baseEnd_912120 < baseStart_912120 := by decide
  rcases family_descends (prefixWord ++ tailWord_912120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912130 : List Nat := [3, 4, 1, 1, 1, 2, 1, 7]
def baseStart_912130 : Nat := 118140960795 + 912130 * 2 ^ 59
def prefixEnd_912130 : Nat := 4983230072969 + 3 ^ 40 * 912130 * 2
def baseEnd_912130 : Nat := 138773662040184154334873

theorem tailTrace_912130 : CollatzResearch.WordTrace tailWord_912130 prefixEnd_912130 138773662040184154334873 := by
  unfold tailWord_912130
  simp only [CollatzResearch.WordTrace]
  refine ⟨8317028546379066061719461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22178742790344176164585229 8317028546379066061719461)
  ·
    refine ⟨1559442852446074886572399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8317028546379066061719461 1559442852446074886572399)
    ·
      refine ⟨2339164278669112329858599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1559442852446074886572399 2339164278669112329858599)
      ·
        refine ⟨3508746418003668494787899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2339164278669112329858599 3508746418003668494787899)
        ·
          refine ⟨5263119627005502742181849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3508746418003668494787899 5263119627005502742181849)
          ·
            refine ⟨3947339720254127056636387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5263119627005502742181849 3947339720254127056636387)
            ·
              refine ⟨5921009580381190584954581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3947339720254127056636387 5921009580381190584954581)
              ·
                refine ⟨138773662040184154334873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5921009580381190584954581 138773662040184154334873)
                ·
                  rfl

theorem cell20_912130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 7].length) (baseStart_912130 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_912130 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_912130 prefixEnd_912130 := by exact prefixLift 912130
  have htrace : WordTrace (prefixWord ++ tailWord_912130) baseStart_912130 baseEnd_912130 := by
    simpa [prefixWord, tailWord_912130, baseEnd_912130] using wordTrace_append hprefix tailTrace_912130
  have hstable : (prefixWord ++ tailWord_912130).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912130).length < 2 ^ (prefixWord ++ tailWord_912130).sum := by decide
  have hdescent : baseEnd_912130 < baseStart_912130 := by decide
  rcases family_descends (prefixWord ++ tailWord_912130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912161 : List Nat := [1, 2, 3, 2, 1, 2, 2, 5, 2]
def baseStart_912161 : Nat := 118140960795 + 912161 * 2 ^ 59
def prefixEnd_912161 : Nat := 4983230072969 + 3 ^ 40 * 912161 * 2
def baseEnd_912161 : Nat := 416335135365254132971159

theorem tailTrace_912161 : CollatzResearch.WordTrace tailWord_912161 prefixEnd_912161 416335135365254132971159 := by
  unfold tailWord_912161
  simp only [CollatzResearch.WordTrace]
  refine ⟨33269244848403956541256337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22179496565602637694170891 33269244848403956541256337)
  ·
    refine ⟨24951933636302967405942253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33269244848403956541256337 24951933636302967405942253)
    ·
      refine ⟨9356975113613612777228345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24951933636302967405942253 9356975113613612777228345)
      ·
        refine ⟨7017731335210209582921259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9356975113613612777228345 7017731335210209582921259)
        ·
          refine ⟨10526597002815314374381889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7017731335210209582921259 10526597002815314374381889)
          ·
            refine ⟨7894947752111485780786417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10526597002815314374381889 7894947752111485780786417)
            ·
              refine ⟨5921210814083614335589813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7894947752111485780786417 5921210814083614335589813)
              ·
                refine ⟨555113513820338843961545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5921210814083614335589813 555113513820338843961545)
                ·
                  refine ⟨416335135365254132971159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 555113513820338843961545 416335135365254132971159)
                  ·
                    rfl

theorem cell20_912161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 5, 2].length) (baseStart_912161 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_912161 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_912161 prefixEnd_912161 := by exact prefixLift 912161
  have htrace : WordTrace (prefixWord ++ tailWord_912161) baseStart_912161 baseEnd_912161 := by
    simpa [prefixWord, tailWord_912161, baseEnd_912161] using wordTrace_append hprefix tailTrace_912161
  have hstable : (prefixWord ++ tailWord_912161).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912161).length < 2 ^ (prefixWord ++ tailWord_912161).sum := by decide
  have hdescent : baseEnd_912161 < baseStart_912161 := by decide
  rcases family_descends (prefixWord ++ tailWord_912161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912174 : List Nat := [4, 1, 3, 2, 1, 3, 2, 2, 2]
def baseStart_912174 : Nat := 118140960795 + 912174 * 2 ^ 59
def prefixEnd_912174 : Nat := 4983230072969 + 3 ^ 40 * 912174 * 2
def baseEnd_912174 : Nat := 416341068919483865537773

theorem tailTrace_912174 : CollatzResearch.WordTrace tailWord_912174 prefixEnd_912174 416341068919483865537773 := by
  unfold tailWord_912174
  simp only [CollatzResearch.WordTrace]
  refine ⟨4158714874669607470184947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22179812664904573174319717 4158714874669607470184947)
  ·
    refine ⟨6238072312004411205277421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4158714874669607470184947 6238072312004411205277421)
    ·
      refine ⟨2339277117001654201979033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6238072312004411205277421 2339277117001654201979033)
      ·
        refine ⟨1754457837751240651484275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2339277117001654201979033 1754457837751240651484275)
        ·
          refine ⟨2631686756626860977226413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1754457837751240651484275 2631686756626860977226413)
          ·
            refine ⟨986882533735072866459905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2631686756626860977226413 986882533735072866459905)
            ·
              refine ⟨740161900301304649844929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 986882533735072866459905 740161900301304649844929)
              ·
                refine ⟨555121425225978487383697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 740161900301304649844929 555121425225978487383697)
                ·
                  refine ⟨416341068919483865537773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 555121425225978487383697 416341068919483865537773)
                  ·
                    rfl

theorem cell20_912174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 2, 2, 2].length) (baseStart_912174 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_912174 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_912174 prefixEnd_912174 := by exact prefixLift 912174
  have htrace : WordTrace (prefixWord ++ tailWord_912174) baseStart_912174 baseEnd_912174 := by
    simpa [prefixWord, tailWord_912174, baseEnd_912174] using wordTrace_append hprefix tailTrace_912174
  have hstable : (prefixWord ++ tailWord_912174).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912174).length < 2 ^ (prefixWord ++ tailWord_912174).sum := by decide
  have hdescent : baseEnd_912174 < baseStart_912174 := by decide
  rcases family_descends (prefixWord ++ tailWord_912174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_912226 : List Nat := [3, 3, 2, 1, 4, 1, 1, 2, 3]
def baseStart_912226 : Nat := 118140960795 + 912226 * 2 ^ 59
def prefixEnd_912226 : Nat := 4983230072969 + 3 ^ 40 * 912226 * 2
def baseEnd_912226 : Nat := 416364803136402795804227

theorem tailTrace_912226 : CollatzResearch.WordTrace tailWord_912226 prefixEnd_912226 416364803136402795804227 := by
  unfold tailWord_912226
  simp only [CollatzResearch.WordTrace]
  refine ⟨8317903898292118160593133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22181077062112315094915021 8317903898292118160593133)
  ·
    refine ⟨3119213961859544310222425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8317903898292118160593133 3119213961859544310222425)
    ·
      refine ⟨2339410471394658232666819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3119213961859544310222425 2339410471394658232666819)
      ·
        refine ⟨3509115707091987349000229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2339410471394658232666819 3509115707091987349000229)
        ·
          refine ⟨657959195079747627937543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3509115707091987349000229 657959195079747627937543)
          ·
            refine ⟨986938792619621441906315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 657959195079747627937543 986938792619621441906315)
            ·
              refine ⟨1480408188929432162859473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 986938792619621441906315 1480408188929432162859473)
              ·
                refine ⟨1110306141697074122144605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1480408188929432162859473 1110306141697074122144605)
                ·
                  refine ⟨416364803136402795804227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1110306141697074122144605 416364803136402795804227)
                  ·
                    rfl

theorem cell20_912226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 1, 2, 3].length) (baseStart_912226 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_912226 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_912226 prefixEnd_912226 := by exact prefixLift 912226
  have htrace : WordTrace (prefixWord ++ tailWord_912226) baseStart_912226 baseEnd_912226 := by
    simpa [prefixWord, tailWord_912226, baseEnd_912226] using wordTrace_append hprefix tailTrace_912226
  have hstable : (prefixWord ++ tailWord_912226).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_912226).length < 2 ^ (prefixWord ++ tailWord_912226).sum := by decide
  have hdescent : baseEnd_912226 < baseStart_912226 := by decide
  rcases family_descends (prefixWord ++ tailWord_912226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
