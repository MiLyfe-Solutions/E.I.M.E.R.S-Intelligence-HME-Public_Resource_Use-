import V185TrunkScan23Chunk0387

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2292850 : List Nat := [3, 2, 1, 2, 2, 1, 3, 4, 1, 4]
def baseStart_2292850 : Nat := 118140960795 + 2292850 * 2 ^ 59
def prefixEnd_2292850 : Nat := 4983230072969 + 3 ^ 40 * 2292850 * 2
def baseEnd_2292850 : Nat := 392444706220486482510127

theorem tailTrace_2292850 : CollatzResearch.WordTrace tailWord_2292850 prefixEnd_2292850 392444706220486482510127 := by
  unfold tailWord_2292850
  simp only [CollatzResearch.WordTrace]
  refine ⟨20906777435850878112307001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55751406495602341632818669 20906777435850878112307001)
  ·
    refine ⟨15680083076888158584230251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20906777435850878112307001 15680083076888158584230251)
    ·
      refine ⟨23520124615332237876345377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15680083076888158584230251 23520124615332237876345377)
      ·
        refine ⟨17640093461499178407259033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23520124615332237876345377 17640093461499178407259033)
        ·
          refine ⟨13230070096124383805444275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17640093461499178407259033 13230070096124383805444275)
          ·
            refine ⟨19845105144186575708166413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13230070096124383805444275 19845105144186575708166413)
            ·
              refine ⟨7441914429069965890562405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19845105144186575708166413 7441914429069965890562405)
              ·
                refine ⟨1395358955450618604480451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7441914429069965890562405 1395358955450618604480451)
                ·
                  refine ⟨2093038433175927906720677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1395358955450618604480451 2093038433175927906720677)
                  ·
                    refine ⟨392444706220486482510127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2093038433175927906720677 392444706220486482510127)
                    ·
                      rfl

theorem cell23_2292850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 4, 1, 4].length) (baseStart_2292850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2292850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2292850 prefixEnd_2292850 := by exact prefixLift 2292850
  have htrace : WordTrace (prefixWord ++ tailWord_2292850) baseStart_2292850 baseEnd_2292850 := by
    simpa [prefixWord, tailWord_2292850, baseEnd_2292850] using wordTrace_append hprefix tailTrace_2292850
  have hstable : (prefixWord ++ tailWord_2292850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2292850).length < 2 ^ (prefixWord ++ tailWord_2292850).sum := by decide
  have hdescent : baseEnd_2292850 < baseStart_2292850 := by decide
  rcases family_descends (prefixWord ++ tailWord_2292850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2292873 : List Nat := [1, 2, 1, 1, 4, 3, 1, 1, 5, 1, 3]
def baseStart_2292873 : Nat := 118140960795 + 2292873 * 2 ^ 59
def prefixEnd_2292873 : Nat := 4983230072969 + 3 ^ 40 * 2292873 * 2
def baseEnd_2292873 : Nat := 1177345928716512857542775

theorem tailTrace_2292873 : CollatzResearch.WordTrace tailWord_2292873 prefixEnd_2292873 1177345928716512857542775 := by
  unfold tailWord_2292873
  simp only [CollatzResearch.WordTrace]
  refine ⟨83627948622320187377315273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55751965748213458251543515 83627948622320187377315273)
  ·
    refine ⟨62720961466740140532986455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83627948622320187377315273 62720961466740140532986455)
    ·
      refine ⟨94081442200110210799479683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62720961466740140532986455 94081442200110210799479683)
      ·
        refine ⟨141122163300165316199219525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94081442200110210799479683 141122163300165316199219525)
        ·
          refine ⟨26460405618780996787353661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 141122163300165316199219525 26460405618780996787353661)
          ·
            refine ⟨9922652107042873795257623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26460405618780996787353661 9922652107042873795257623)
            ·
              refine ⟨14883978160564310692886435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9922652107042873795257623 14883978160564310692886435)
              ·
                refine ⟨22325967240846466039329653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14883978160564310692886435 22325967240846466039329653)
                ·
                  refine ⟨2093059428829356191187155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22325967240846466039329653 2093059428829356191187155)
                  ·
                    refine ⟨3139589143244034286780733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2093059428829356191187155 3139589143244034286780733)
                    ·
                      refine ⟨1177345928716512857542775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3139589143244034286780733 1177345928716512857542775)
                      ·
                        rfl

theorem cell23_2292873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 1, 5, 1, 3].length) (baseStart_2292873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2292873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2292873 prefixEnd_2292873 := by exact prefixLift 2292873
  have htrace : WordTrace (prefixWord ++ tailWord_2292873) baseStart_2292873 baseEnd_2292873 := by
    simpa [prefixWord, tailWord_2292873, baseEnd_2292873] using wordTrace_append hprefix tailTrace_2292873
  have hstable : (prefixWord ++ tailWord_2292873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2292873).length < 2 ^ (prefixWord ++ tailWord_2292873).sum := by decide
  have hdescent : baseEnd_2292873 < baseStart_2292873 := by decide
  rcases family_descends (prefixWord ++ tailWord_2292873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2292879 : List Nat := [1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 10]
def baseStart_2292879 : Nat := 118140960795 + 2292879 * 2 ^ 59
def prefixEnd_2292879 : Nat := 4983230072969 + 3 ^ 40 * 2292879 * 2
def baseEnd_2292879 : Nat := 1177349009600439834067747

theorem tailTrace_2292879 : CollatzResearch.WordTrace tailWord_2292879 prefixEnd_2292879 1177349009600439834067747 := by
  unfold tailWord_2292879
  simp only [CollatzResearch.WordTrace]
  refine ⟨83628167460298450402033691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55752111640198966934689127 83628167460298450402033691)
  ·
    refine ⟨125442251190447675603050537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83628167460298450402033691 125442251190447675603050537)
    ·
      refine ⟨94081688392835756702287903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125442251190447675603050537 94081688392835756702287903)
      ·
        refine ⟨141122532589253635053431855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94081688392835756702287903 141122532589253635053431855)
        ·
          refine ⟨211683798883880452580147783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141122532589253635053431855 211683798883880452580147783)
          ·
            refine ⟨317525698325820678870221675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 211683798883880452580147783 317525698325820678870221675)
            ·
              refine ⟨476288547488731018305332513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 317525698325820678870221675 476288547488731018305332513)
              ·
                refine ⟨357216410616548263728999385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 476288547488731018305332513 357216410616548263728999385)
                ·
                  refine ⟨267912307962411197796749539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 357216410616548263728999385 267912307962411197796749539)
                  ·
                    refine ⟨401868461943616796695124309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 267912307962411197796749539 401868461943616796695124309)
                    ·
                      refine ⟨1177349009600439834067747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 401868461943616796695124309 1177349009600439834067747)
                      ·
                        rfl

theorem cell23_2292879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 10].length) (baseStart_2292879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2292879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2292879 prefixEnd_2292879 := by exact prefixLift 2292879
  have htrace : WordTrace (prefixWord ++ tailWord_2292879) baseStart_2292879 baseEnd_2292879 := by
    simpa [prefixWord, tailWord_2292879, baseEnd_2292879] using wordTrace_append hprefix tailTrace_2292879
  have hstable : (prefixWord ++ tailWord_2292879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2292879).length < 2 ^ (prefixWord ++ tailWord_2292879).sum := by decide
  have hdescent : baseEnd_2292879 < baseStart_2292879 := by decide
  rcases family_descends (prefixWord ++ tailWord_2292879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2292893 : List Nat := [1, 4, 2, 1, 1, 2, 3, 3, 1, 5]
def baseStart_2292893 : Nat := 118140960795 + 2292893 * 2 ^ 59
def prefixEnd_2292893 : Nat := 4983230072969 + 3 ^ 40 * 2292893 * 2
def baseEnd_2292893 : Nat := 392452066109867593097561

theorem tailTrace_2292893 : CollatzResearch.WordTrace tailWord_2292893 prefixEnd_2292893 392452066109867593097561 := by
  unfold tailWord_2292893
  simp only [CollatzResearch.WordTrace]
  refine ⟨83628678082247730793043333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55752452054831820528695555 83628678082247730793043333)
  ·
    refine ⟨15680377140421449523695625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83628678082247730793043333 15680377140421449523695625)
    ·
      refine ⟨11760282855316087142771719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15680377140421449523695625 11760282855316087142771719)
      ·
        refine ⟨17640424282974130714157579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11760282855316087142771719 17640424282974130714157579)
        ·
          refine ⟨26460636424461196071236369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17640424282974130714157579 26460636424461196071236369)
          ·
            refine ⟨19845477318345897053427277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26460636424461196071236369 19845477318345897053427277)
            ·
              refine ⟨7442053994379711395035229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19845477318345897053427277 7442053994379711395035229)
              ·
                refine ⟨2790770247892391773138211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7442053994379711395035229 2790770247892391773138211)
                ·
                  refine ⟨4186155371838587659707317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2790770247892391773138211 4186155371838587659707317)
                  ·
                    refine ⟨392452066109867593097561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4186155371838587659707317 392452066109867593097561)
                    ·
                      rfl

theorem cell23_2292893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 3, 1, 5].length) (baseStart_2292893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2292893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2292893 prefixEnd_2292893 := by exact prefixLift 2292893
  have htrace : WordTrace (prefixWord ++ tailWord_2292893) baseStart_2292893 baseEnd_2292893 := by
    simpa [prefixWord, tailWord_2292893, baseEnd_2292893] using wordTrace_append hprefix tailTrace_2292893
  have hstable : (prefixWord ++ tailWord_2292893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2292893).length < 2 ^ (prefixWord ++ tailWord_2292893).sum := by decide
  have hdescent : baseEnd_2292893 < baseStart_2292893 := by decide
  rcases family_descends (prefixWord ++ tailWord_2292893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2293043 : List Nat := [1, 1, 1, 2, 5, 3, 1, 2, 7]
def baseStart_2293043 : Nat := 118140960795 + 2293043 * 2 ^ 59
def prefixEnd_2293043 : Nat := 4983230072969 + 3 ^ 40 * 2293043 * 2
def baseEnd_2293043 : Nat := 130825913380864132490777

theorem tailTrace_2293043 : CollatzResearch.WordTrace tailWord_2293043 prefixEnd_2293043 130825913380864132490777 := by
  unfold tailWord_2293043
  simp only [CollatzResearch.WordTrace]
  refine ⟨83634149031704306411003783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55756099354469537607335855 83634149031704306411003783)
  ·
    refine ⟨125451223547556459616505675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83634149031704306411003783 125451223547556459616505675)
    ·
      refine ⟨188176835321334689424758513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125451223547556459616505675 188176835321334689424758513)
      ·
        refine ⟨141132626491001017068568885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 188176835321334689424758513 141132626491001017068568885)
        ·
          refine ⟨13231183733531345350178333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 141132626491001017068568885 13231183733531345350178333)
          ·
            refine ⟨4961693900074254506316875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13231183733531345350178333 4961693900074254506316875)
            ·
              refine ⟨7442540850111381759475313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4961693900074254506316875 7442540850111381759475313)
              ·
                refine ⟨5581905637583536319606485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7442540850111381759475313 5581905637583536319606485)
                ·
                  refine ⟨130825913380864132490777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5581905637583536319606485 130825913380864132490777)
                  ·
                    rfl

theorem cell23_2293043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 2, 7].length) (baseStart_2293043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2293043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2293043 prefixEnd_2293043 := by exact prefixLift 2293043
  have htrace : WordTrace (prefixWord ++ tailWord_2293043) baseStart_2293043 baseEnd_2293043 := by
    simpa [prefixWord, tailWord_2293043, baseEnd_2293043] using wordTrace_append hprefix tailTrace_2293043
  have hstable : (prefixWord ++ tailWord_2293043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2293043).length < 2 ^ (prefixWord ++ tailWord_2293043).sum := by decide
  have hdescent : baseEnd_2293043 < baseStart_2293043 := by decide
  rcases family_descends (prefixWord ++ tailWord_2293043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2293073 : List Nat := [1, 2, 2, 1, 4, 1, 2, 1, 4, 5]
def baseStart_2293073 : Nat := 118140960795 + 2293073 * 2 ^ 59
def prefixEnd_2293073 : Nat := 4983230072969 + 3 ^ 40 * 2293073 * 2
def baseEnd_2293073 : Nat := 392482874949137358347285

theorem tailTrace_2293073 : CollatzResearch.WordTrace tailWord_2293073 prefixEnd_2293073 392482874949137358347285 := by
  unfold tailWord_2293073
  simp only [CollatzResearch.WordTrace]
  refine ⟨83635243221595621534595873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55756828814397081023063915 83635243221595621534595873)
  ·
    refine ⟨62726432416196716150946905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83635243221595621534595873 62726432416196716150946905)
    ·
      refine ⟨47044824312147537113210179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62726432416196716150946905 47044824312147537113210179)
      ·
        refine ⟨70567236468221305669815269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47044824312147537113210179 70567236468221305669815269)
        ·
          refine ⟨13231356837791494813090363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 70567236468221305669815269 13231356837791494813090363)
          ·
            refine ⟨19847035256687242219635545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13231356837791494813090363 19847035256687242219635545)
            ·
              refine ⟨14885276442515431664726659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19847035256687242219635545 14885276442515431664726659)
              ·
                refine ⟨22327914663773147497089989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14885276442515431664726659 22327914663773147497089989)
                ·
                  refine ⟨4186483999457465155704373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22327914663773147497089989 4186483999457465155704373)
                  ·
                    refine ⟨392482874949137358347285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4186483999457465155704373 392482874949137358347285)
                    ·
                      rfl

theorem cell23_2293073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 1, 4, 5].length) (baseStart_2293073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2293073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2293073 prefixEnd_2293073 := by exact prefixLift 2293073
  have htrace : WordTrace (prefixWord ++ tailWord_2293073) baseStart_2293073 baseEnd_2293073 := by
    simpa [prefixWord, tailWord_2293073, baseEnd_2293073] using wordTrace_append hprefix tailTrace_2293073
  have hstable : (prefixWord ++ tailWord_2293073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2293073).length < 2 ^ (prefixWord ++ tailWord_2293073).sum := by decide
  have hdescent : baseEnd_2293073 < baseStart_2293073 := by decide
  rcases family_descends (prefixWord ++ tailWord_2293073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2293093 : List Nat := [1, 3, 1, 3, 1, 2, 1, 1, 3, 3, 4]
def baseStart_2293093 : Nat := 118140960795 + 2293093 * 2 ^ 59
def prefixEnd_2293093 : Nat := 4983230072969 + 3 ^ 40 * 2293093 * 2
def baseEnd_2293093 : Nat := 1177458894460501996791763

theorem tailTrace_2293093 : CollatzResearch.WordTrace tailWord_2293093 prefixEnd_2293093 1177458894460501996791763 := by
  unfold tailWord_2293093
  simp only [CollatzResearch.WordTrace]
  refine ⟨83635972681523164950323933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55757315121015443300215955 83635972681523164950323933)
  ·
    refine ⟨31363489755571186856371475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83635972681523164950323933 31363489755571186856371475)
    ·
      refine ⟨47045234633356780284557213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31363489755571186856371475 47045234633356780284557213)
      ·
        refine ⟨17641962987508792606708955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47045234633356780284557213 17641962987508792606708955)
        ·
          refine ⟨26462944481263188910063433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17641962987508792606708955 26462944481263188910063433)
          ·
            refine ⟨19847208360947391682547575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26462944481263188910063433 19847208360947391682547575)
            ·
              refine ⟨29770812541421087523821363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19847208360947391682547575 29770812541421087523821363)
              ·
                refine ⟨44656218812131631285732045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29770812541421087523821363 44656218812131631285732045)
                ·
                  refine ⟨16746082054549361732149517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44656218812131631285732045 16746082054549361732149517)
                  ·
                    refine ⟨6279780770456010649556069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16746082054549361732149517 6279780770456010649556069)
                    ·
                      refine ⟨1177458894460501996791763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6279780770456010649556069 1177458894460501996791763)
                      ·
                        rfl

theorem cell23_2293093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 1, 3, 3, 4].length) (baseStart_2293093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2293093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2293093 prefixEnd_2293093 := by exact prefixLift 2293093
  have htrace : WordTrace (prefixWord ++ tailWord_2293093) baseStart_2293093 baseEnd_2293093 := by
    simpa [prefixWord, tailWord_2293093, baseEnd_2293093] using wordTrace_append hprefix tailTrace_2293093
  have hstable : (prefixWord ++ tailWord_2293093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2293093).length < 2 ^ (prefixWord ++ tailWord_2293093).sum := by decide
  have hdescent : baseEnd_2293093 < baseStart_2293093 := by decide
  rcases family_descends (prefixWord ++ tailWord_2293093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2293187 : List Nat := [1, 1, 1, 3, 1, 1, 6, 2, 2, 3, 2]
def baseStart_2293187 : Nat := 118140960795 + 2293187 * 2 ^ 59
def prefixEnd_2293187 : Nat := 4983230072969 + 3 ^ 40 * 2293187 * 2
def baseEnd_2293187 : Nat := 1177507161642024629016331

theorem tailTrace_2293187 : CollatzResearch.WordTrace tailWord_2293187 prefixEnd_2293187 1177507161642024629016331 := by
  unfold tailWord_2293187
  simp only [CollatzResearch.WordTrace]
  refine ⟨83639401143182619004245815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55759600762121746002830543 83639401143182619004245815)
  ·
    refine ⟨125459101714773928506368723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83639401143182619004245815 125459101714773928506368723)
    ·
      refine ⟨188188652572160892759553085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125459101714773928506368723 188188652572160892759553085)
      ·
        refine ⟨70570744714560334784832407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 188188652572160892759553085 70570744714560334784832407)
        ·
          refine ⟨105856117071840502177248611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70570744714560334784832407 105856117071840502177248611)
          ·
            refine ⟨158784175607760753265872917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105856117071840502177248611 158784175607760753265872917)
            ·
              refine ⟨7443008231613785309337793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 158784175607760753265872917 7443008231613785309337793)
              ·
                refine ⟨5582256173710338982003345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7443008231613785309337793 5582256173710338982003345)
                ·
                  refine ⟨4186692130282754236502509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5582256173710338982003345 4186692130282754236502509)
                  ·
                    refine ⟨1570009548856032838688441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4186692130282754236502509 1570009548856032838688441)
                    ·
                      refine ⟨1177507161642024629016331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1570009548856032838688441 1177507161642024629016331)
                      ·
                        rfl

theorem cell23_2293187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 2, 2, 3, 2].length) (baseStart_2293187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2293187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2293187 prefixEnd_2293187 := by exact prefixLift 2293187
  have htrace : WordTrace (prefixWord ++ tailWord_2293187) baseStart_2293187 baseEnd_2293187 := by
    simpa [prefixWord, tailWord_2293187, baseEnd_2293187] using wordTrace_append hprefix tailTrace_2293187
  have hstable : (prefixWord ++ tailWord_2293187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2293187).length < 2 ^ (prefixWord ++ tailWord_2293187).sum := by decide
  have hdescent : baseEnd_2293187 < baseStart_2293187 := by decide
  rcases family_descends (prefixWord ++ tailWord_2293187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2293188 : List Nat := [2, 3, 3, 2, 1, 3, 2, 2, 1, 4]
def baseStart_2293188 : Nat := 118140960795 + 2293188 * 2 ^ 59
def prefixEnd_2293188 : Nat := 4983230072969 + 3 ^ 40 * 2293188 * 2
def baseEnd_2293188 : Nat := 392502558374226375034609

theorem tailTrace_2293188 : CollatzResearch.WordTrace tailWord_2293188 prefixEnd_2293188 392502558374226375034609 := by
  unfold tailWord_2293188
  simp only [CollatzResearch.WordTrace]
  refine ⟨41819718808089498087516109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55759625077452664116688145 41819718808089498087516109)
  ·
    refine ⟨15682394553033561782818541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41819718808089498087516109 15682394553033561782818541)
    ·
      refine ⟨5880897957387585668556953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15682394553033561782818541 5880897957387585668556953)
      ·
        refine ⟨4410673468040689251417715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5880897957387585668556953 4410673468040689251417715)
        ·
          refine ⟨6616010202061033877126573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4410673468040689251417715 6616010202061033877126573)
          ·
            refine ⟨2481003825772887703922465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6616010202061033877126573 2481003825772887703922465)
            ·
              refine ⟨1860752869329665777941849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2481003825772887703922465 1860752869329665777941849)
              ·
                refine ⟨1395564651997249333456387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1860752869329665777941849 1395564651997249333456387)
                ·
                  refine ⟨2093346977995874000184581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1395564651997249333456387 2093346977995874000184581)
                  ·
                    refine ⟨392502558374226375034609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2093346977995874000184581 392502558374226375034609)
                    ·
                      rfl

theorem cell23_2293188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 2, 2, 1, 4].length) (baseStart_2293188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2293188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2293188 prefixEnd_2293188 := by exact prefixLift 2293188
  have htrace : WordTrace (prefixWord ++ tailWord_2293188) baseStart_2293188 baseEnd_2293188 := by
    simpa [prefixWord, tailWord_2293188, baseEnd_2293188] using wordTrace_append hprefix tailTrace_2293188
  have hstable : (prefixWord ++ tailWord_2293188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2293188).length < 2 ^ (prefixWord ++ tailWord_2293188).sum := by decide
  have hdescent : baseEnd_2293188 < baseStart_2293188 := by decide
  rcases family_descends (prefixWord ++ tailWord_2293188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2293193 : List Nat := [1, 2, 1, 1, 2, 1, 3, 1, 5, 6]
def baseStart_2293193 : Nat := 118140960795 + 2293193 * 2 ^ 59
def prefixEnd_2293193 : Nat := 4983230072969 + 3 ^ 40 * 2293193 * 2
def baseEnd_2293193 : Nat := 392503414175317201847101

theorem tailTrace_2293193 : CollatzResearch.WordTrace tailWord_2293193 prefixEnd_2293193 392503414175317201847101 := by
  unfold tailWord_2293193
  simp only [CollatzResearch.WordTrace]
  refine ⟨83639619981160882028964233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55759746654107254685976155 83639619981160882028964233)
  ·
    refine ⟨62729714985870661521723175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83639619981160882028964233 62729714985870661521723175)
    ·
      refine ⟨94094572478805992282584763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62729714985870661521723175 94094572478805992282584763)
      ·
        refine ⟨141141858718208988423877145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94094572478805992282584763 141141858718208988423877145)
        ·
          refine ⟨105856394038656741317907859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 141141858718208988423877145 105856394038656741317907859)
          ·
            refine ⟨158784591057985111976861789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105856394038656741317907859 158784591057985111976861789)
            ·
              refine ⟨59544221646744416991323171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 158784591057985111976861789 59544221646744416991323171)
              ·
                refine ⟨89316332470116625486984757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59544221646744416991323171 89316332470116625486984757)
                ·
                  refine ⟨8373406169073433639404821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 89316332470116625486984757 8373406169073433639404821)
                  ·
                    refine ⟨392503414175317201847101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8373406169073433639404821 392503414175317201847101)
                    ·
                      rfl

theorem cell23_2293193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 5, 6].length) (baseStart_2293193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2293193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2293193 prefixEnd_2293193 := by exact prefixLift 2293193
  have htrace : WordTrace (prefixWord ++ tailWord_2293193) baseStart_2293193 baseEnd_2293193 := by
    simpa [prefixWord, tailWord_2293193, baseEnd_2293193] using wordTrace_append hprefix tailTrace_2293193
  have hstable : (prefixWord ++ tailWord_2293193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2293193).length < 2 ^ (prefixWord ++ tailWord_2293193).sum := by decide
  have hdescent : baseEnd_2293193 < baseStart_2293193 := by decide
  rcases family_descends (prefixWord ++ tailWord_2293193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2293210 : List Nat := [3, 1, 1, 2, 3, 2, 1, 3, 1, 6]
def baseStart_2293210 : Nat := 118140960795 + 2293210 * 2 ^ 59
def prefixEnd_2293210 : Nat := 4983230072969 + 3 ^ 40 * 2293210 * 2
def baseEnd_2293210 : Nat := 392506323899026013009575

theorem tailTrace_2293210 : CollatzResearch.WordTrace tailWord_2293210 prefixEnd_2293210 392506323899026013009575 := by
  unfold tailWord_2293210
  simp only [CollatzResearch.WordTrace]
  refine ⟨20910060005524823483083271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55760160014732862621555389 20910060005524823483083271)
  ·
    refine ⟨31365090008287235224624907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20910060005524823483083271 31365090008287235224624907)
    ·
      refine ⟨47047635012430852836937361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31365090008287235224624907 47047635012430852836937361)
      ·
        refine ⟨35285726259323139627703021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47047635012430852836937361 35285726259323139627703021)
        ·
          refine ⟨13232147347246177360388633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35285726259323139627703021 13232147347246177360388633)
          ·
            refine ⟨9924110510434633020291475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13232147347246177360388633 9924110510434633020291475)
            ·
              refine ⟨14886165765651949530437213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9924110510434633020291475 14886165765651949530437213)
              ·
                refine ⟨5582312162119481073913955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14886165765651949530437213 5582312162119481073913955)
                ·
                  refine ⟨8373468243179221610870933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5582312162119481073913955 8373468243179221610870933)
                  ·
                    refine ⟨392506323899026013009575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8373468243179221610870933 392506323899026013009575)
                    ·
                      rfl

theorem cell23_2293210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 3, 1, 6].length) (baseStart_2293210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2293210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2293210 prefixEnd_2293210 := by exact prefixLift 2293210
  have htrace : WordTrace (prefixWord ++ tailWord_2293210) baseStart_2293210 baseEnd_2293210 := by
    simpa [prefixWord, tailWord_2293210, baseEnd_2293210] using wordTrace_append hprefix tailTrace_2293210
  have hstable : (prefixWord ++ tailWord_2293210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2293210).length < 2 ^ (prefixWord ++ tailWord_2293210).sum := by decide
  have hdescent : baseEnd_2293210 < baseStart_2293210 := by decide
  rcases family_descends (prefixWord ++ tailWord_2293210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2293221 : List Nat := [1, 3, 1, 5, 1, 3, 1, 1, 2, 3, 2]
def baseStart_2293221 : Nat := 118140960795 + 2293221 * 2 ^ 59
def prefixEnd_2293221 : Nat := 4983230072969 + 3 ^ 40 * 2293221 * 2
def baseEnd_2293221 : Nat := 1177524619984277495991175

theorem tailTrace_2293221 : CollatzResearch.WordTrace tailWord_2293221 prefixEnd_2293221 1177524619984277495991175 := by
  unfold tailWord_2293221
  simp only [CollatzResearch.WordTrace]
  refine ⟨83640641225059442810983517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55760427483372961873989011 83640641225059442810983517)
  ·
    refine ⟨31365240459397291054118819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83640641225059442810983517 31365240459397291054118819)
    ·
      refine ⟨47047860689095936581178229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31365240459397291054118819 47047860689095936581178229)
      ·
        refine ⟨4410736939602744054485459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 47047860689095936581178229 4410736939602744054485459)
        ·
          refine ⟨6616105409404116081728189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4410736939602744054485459 6616105409404116081728189)
          ·
            refine ⟨2481039528526543530648071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6616105409404116081728189 2481039528526543530648071)
            ·
              refine ⟨3721559292789815295972107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2481039528526543530648071 3721559292789815295972107)
              ·
                refine ⟨5582338939184722943958161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3721559292789815295972107 5582338939184722943958161)
                ·
                  refine ⟨4186754204388542207968621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5582338939184722943958161 4186754204388542207968621)
                  ·
                    refine ⟨1570032826645703327988233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4186754204388542207968621 1570032826645703327988233)
                    ·
                      refine ⟨1177524619984277495991175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1570032826645703327988233 1177524619984277495991175)
                      ·
                        rfl

theorem cell23_2293221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 1, 1, 2, 3, 2].length) (baseStart_2293221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2293221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2293221 prefixEnd_2293221 := by exact prefixLift 2293221
  have htrace : WordTrace (prefixWord ++ tailWord_2293221) baseStart_2293221 baseEnd_2293221 := by
    simpa [prefixWord, tailWord_2293221, baseEnd_2293221] using wordTrace_append hprefix tailTrace_2293221
  have hstable : (prefixWord ++ tailWord_2293221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2293221).length < 2 ^ (prefixWord ++ tailWord_2293221).sum := by decide
  have hdescent : baseEnd_2293221 < baseStart_2293221 := by decide
  rcases family_descends (prefixWord ++ tailWord_2293221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2293234 : List Nat := [3, 2, 1, 4, 1, 2, 1, 3, 1, 1, 4]
def baseStart_2293234 : Nat := 118140960795 + 2293234 * 2 ^ 59
def prefixEnd_2293234 : Nat := 4983230072969 + 3 ^ 40 * 2293234 * 2
def baseEnd_2293234 : Nat := 1177531295232785945128615

theorem tailTrace_2293234 : CollatzResearch.WordTrace tailWord_2293234 prefixEnd_2293234 1177531295232785945128615 := by
  unfold tailWord_2293234
  simp only [CollatzResearch.WordTrace]
  refine ⟨20910278843503086507801689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55760743582674897354137837 20910278843503086507801689)
  ·
    refine ⟨15682709132627314880851267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20910278843503086507801689 15682709132627314880851267)
    ·
      refine ⟨23524063698940972321276901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15682709132627314880851267 23524063698940972321276901)
      ·
        refine ⟨4410761943551432310239419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23524063698940972321276901 4410761943551432310239419)
        ·
          refine ⟨6616142915327148465359129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4410761943551432310239419 6616142915327148465359129)
          ·
            refine ⟨4962107186495361349019347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6616142915327148465359129 4962107186495361349019347)
            ·
              refine ⟨7443160779743042023529021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4962107186495361349019347 7443160779743042023529021)
              ·
                refine ⟨2791185292403640758823383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7443160779743042023529021 2791185292403640758823383)
                ·
                  refine ⟨4186777938605461138235075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2791185292403640758823383 4186777938605461138235075)
                  ·
                    refine ⟨6280166907908191707352613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4186777938605461138235075 6280166907908191707352613)
                    ·
                      refine ⟨1177531295232785945128615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6280166907908191707352613 1177531295232785945128615)
                      ·
                        rfl

theorem cell23_2293234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_2293234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2293234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2293234 prefixEnd_2293234 := by exact prefixLift 2293234
  have htrace : WordTrace (prefixWord ++ tailWord_2293234) baseStart_2293234 baseEnd_2293234 := by
    simpa [prefixWord, tailWord_2293234, baseEnd_2293234] using wordTrace_append hprefix tailTrace_2293234
  have hstable : (prefixWord ++ tailWord_2293234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2293234).length < 2 ^ (prefixWord ++ tailWord_2293234).sum := by decide
  have hdescent : baseEnd_2293234 < baseStart_2293234 := by decide
  rcases family_descends (prefixWord ++ tailWord_2293234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2293267 : List Nat := [1, 1, 1, 2, 1, 6, 3, 1, 1, 3, 3]
def baseStart_2293267 : Nat := 118140960795 + 2293267 * 2 ^ 59
def prefixEnd_2293267 : Nat := 4983230072969 + 3 ^ 40 * 2293267 * 2
def baseEnd_2293267 : Nat := 1177548240094384316015963

theorem tailTrace_2293267 : CollatzResearch.WordTrace tailWord_2293267 prefixEnd_2293267 1177548240094384316015963 := by
  unfold tailWord_2293267
  simp only [CollatzResearch.WordTrace]
  refine ⟨83642318982892792667158055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55761545988595195111438703 83642318982892792667158055)
  ·
    refine ⟨125463478474339189000737083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83642318982892792667158055 125463478474339189000737083)
    ·
      refine ⟨188195217711508783501105625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125463478474339189000737083 188195217711508783501105625)
      ·
        refine ⟨141146413283631587625829219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 188195217711508783501105625 141146413283631587625829219)
        ·
          refine ⟨211719619925447381438743829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141146413283631587625829219 211719619925447381438743829)
          ·
            refine ⟨9924357184005346004941117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 211719619925447381438743829 9924357184005346004941117)
            ·
              refine ⟨3721633944002004751852919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9924357184005346004941117 3721633944002004751852919)
              ·
                refine ⟨5582450916003007127779379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3721633944002004751852919 5582450916003007127779379)
                ·
                  refine ⟨8373676374004510691669069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5582450916003007127779379 8373676374004510691669069)
                  ·
                    refine ⟨3140128640251691509375901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8373676374004510691669069 3140128640251691509375901)
                    ·
                      refine ⟨1177548240094384316015963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3140128640251691509375901 1177548240094384316015963)
                      ·
                        rfl

theorem cell23_2293267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 3, 1, 1, 3, 3].length) (baseStart_2293267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2293267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2293267 prefixEnd_2293267 := by exact prefixLift 2293267
  have htrace : WordTrace (prefixWord ++ tailWord_2293267) baseStart_2293267 baseEnd_2293267 := by
    simpa [prefixWord, tailWord_2293267, baseEnd_2293267] using wordTrace_append hprefix tailTrace_2293267
  have hstable : (prefixWord ++ tailWord_2293267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2293267).length < 2 ^ (prefixWord ++ tailWord_2293267).sum := by decide
  have hdescent : baseEnd_2293267 < baseStart_2293267 := by decide
  rcases family_descends (prefixWord ++ tailWord_2293267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2293302 : List Nat := [5, 1, 2, 1, 3, 1, 3, 2, 1, 2, 2]
def baseStart_2293302 : Nat := 118140960795 + 2293302 * 2 ^ 59
def prefixEnd_2293302 : Nat := 4983230072969 + 3 ^ 40 * 2293302 * 2
def baseEnd_2293302 : Nat := 1177566211917291679078303

theorem tailTrace_2293302 : CollatzResearch.WordTrace tailWord_2293302 prefixEnd_2293302 1177566211917291679078303 := by
  unfold tailWord_2293302
  simp only [CollatzResearch.WordTrace]
  refine ⟨5227724721110374602792635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 55762397025177329096454773 5227724721110374602792635)
  ·
    refine ⟨7841587081665561904188953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5227724721110374602792635 7841587081665561904188953)
    ·
      refine ⟨5881190311249171428141715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7841587081665561904188953 5881190311249171428141715)
      ·
        refine ⟨8821785466873757142212573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5881190311249171428141715 8821785466873757142212573)
        ·
          refine ⟨3308169550077658928329715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8821785466873757142212573 3308169550077658928329715)
          ·
            refine ⟨4962254325116488392494573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3308169550077658928329715 4962254325116488392494573)
            ·
              refine ⟨1860845371918683147185465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4962254325116488392494573 1860845371918683147185465)
              ·
                refine ⟨1395634028939012360389099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1860845371918683147185465 1395634028939012360389099)
                ·
                  refine ⟨2093451043408518540583649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1395634028939012360389099 2093451043408518540583649)
                  ·
                    refine ⟨1570088282556388905437737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2093451043408518540583649 1570088282556388905437737)
                    ·
                      refine ⟨1177566211917291679078303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1570088282556388905437737 1177566211917291679078303)
                      ·
                        rfl

theorem cell23_2293302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 3, 2, 1, 2, 2].length) (baseStart_2293302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2293302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2293302 prefixEnd_2293302 := by exact prefixLift 2293302
  have htrace : WordTrace (prefixWord ++ tailWord_2293302) baseStart_2293302 baseEnd_2293302 := by
    simpa [prefixWord, tailWord_2293302, baseEnd_2293302] using wordTrace_append hprefix tailTrace_2293302
  have hstable : (prefixWord ++ tailWord_2293302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2293302).length < 2 ^ (prefixWord ++ tailWord_2293302).sum := by decide
  have hdescent : baseEnd_2293302 < baseStart_2293302 := by decide
  rcases family_descends (prefixWord ++ tailWord_2293302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2293370 : List Nat := [3, 1, 1, 1, 1, 1, 1, 5, 1, 1, 7]
def baseStart_2293370 : Nat := 118140960795 + 2293370 * 2 ^ 59
def prefixEnd_2293370 : Nat := 4983230072969 + 3 ^ 40 * 2293370 * 2
def baseEnd_2293370 : Nat := 1177601128601797413027989

theorem tailTrace_2293370 : CollatzResearch.WordTrace tailWord_2293370 prefixEnd_2293370 1177601128601797413027989 := by
  unfold tailWord_2293370
  simp only [CollatzResearch.WordTrace]
  refine ⟨20911518925379910314539391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55764050467679760838771709 20911518925379910314539391)
  ·
    refine ⟨31367278388069865471809087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20911518925379910314539391 31367278388069865471809087)
    ·
      refine ⟨47050917582104798207713631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31367278388069865471809087 47050917582104798207713631)
      ·
        refine ⟨70576376373157197311570447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47050917582104798207713631 70576376373157197311570447)
        ·
          refine ⟨105864564559735795967355671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70576376373157197311570447 105864564559735795967355671)
          ·
            refine ⟨158796846839603693951033507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105864564559735795967355671 158796846839603693951033507)
            ·
              refine ⟨238195270259405540926550261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 158796846839603693951033507 238195270259405540926550261)
              ·
                refine ⟨22330806586819269461864087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 238195270259405540926550261 22330806586819269461864087)
                ·
                  refine ⟨33496209880228904192796131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22330806586819269461864087 33496209880228904192796131)
                  ·
                    refine ⟨50244314820343356289194197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33496209880228904192796131 50244314820343356289194197)
                    ·
                      refine ⟨1177601128601797413027989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 50244314820343356289194197 1177601128601797413027989)
                      ·
                        rfl

theorem cell23_2293370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 5, 1, 1, 7].length) (baseStart_2293370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2293370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2293370 prefixEnd_2293370 := by exact prefixLift 2293370
  have htrace : WordTrace (prefixWord ++ tailWord_2293370) baseStart_2293370 baseEnd_2293370 := by
    simpa [prefixWord, tailWord_2293370, baseEnd_2293370] using wordTrace_append hprefix tailTrace_2293370
  have hstable : (prefixWord ++ tailWord_2293370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2293370).length < 2 ^ (prefixWord ++ tailWord_2293370).sum := by decide
  have hdescent : baseEnd_2293370 < baseStart_2293370 := by decide
  rcases family_descends (prefixWord ++ tailWord_2293370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2293394 : List Nat := [3, 2, 3, 1, 3, 1, 1, 1, 1, 7]
def baseStart_2293394 : Nat := 118140960795 + 2293394 * 2 ^ 59
def prefixEnd_2293394 : Nat := 4983230072969 + 3 ^ 40 * 2293394 * 2
def baseEnd_2293394 : Nat := 392537817379168439709293

theorem tailTrace_2293394 : CollatzResearch.WordTrace tailWord_2293394 prefixEnd_2293394 392537817379168439709293 := by
  unfold tailWord_2293394
  simp only [CollatzResearch.WordTrace]
  refine ⟨20911737763358173339257809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55764634035621795571354157 20911737763358173339257809)
  ·
    refine ⟨15683803322518630004443357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20911737763358173339257809 15683803322518630004443357)
    ·
      refine ⟨5881426245944486251666259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15683803322518630004443357 5881426245944486251666259)
      ·
        refine ⟨8822139368916729377499389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5881426245944486251666259 8822139368916729377499389)
        ·
          refine ⟨3308302263343773516562271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8822139368916729377499389 3308302263343773516562271)
          ·
            refine ⟨4962453395015660274843407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3308302263343773516562271 4962453395015660274843407)
            ·
              refine ⟨7443680092523490412265111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4962453395015660274843407 7443680092523490412265111)
              ·
                refine ⟨11165520138785235618397667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7443680092523490412265111 11165520138785235618397667)
                ·
                  refine ⟨16748280208177853427596501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11165520138785235618397667 16748280208177853427596501)
                  ·
                    refine ⟨392537817379168439709293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16748280208177853427596501 392537817379168439709293)
                    ·
                      rfl

theorem cell23_2293394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 1, 1, 7].length) (baseStart_2293394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2293394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2293394 prefixEnd_2293394 := by exact prefixLift 2293394
  have htrace : WordTrace (prefixWord ++ tailWord_2293394) baseStart_2293394 baseEnd_2293394 := by
    simpa [prefixWord, tailWord_2293394, baseEnd_2293394] using wordTrace_append hprefix tailTrace_2293394
  have hstable : (prefixWord ++ tailWord_2293394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2293394).length < 2 ^ (prefixWord ++ tailWord_2293394).sum := by decide
  have hdescent : baseEnd_2293394 < baseStart_2293394 := by decide
  rcases family_descends (prefixWord ++ tailWord_2293394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2293447 : List Nat := [1, 1, 4, 1, 1, 1, 3, 1, 2, 5, 3]
def baseStart_2293447 : Nat := 118140960795 + 2293447 * 2 ^ 59
def prefixEnd_2293447 : Nat := 4983230072969 + 3 ^ 40 * 2293447 * 2
def baseEnd_2293447 : Nat := 1177640666612193611765135

theorem tailTrace_2293447 : CollatzResearch.WordTrace tailWord_2293447 prefixEnd_2293447 1177640666612193611765135 := by
  unfold tailWord_2293447
  simp only [CollatzResearch.WordTrace]
  refine ⟨83648884122240683408710595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55765922748160455605807063 83648884122240683408710595)
  ·
    refine ⟨125473326183361025113065893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83648884122240683408710595 125473326183361025113065893)
    ·
      refine ⟨23526248659380192208699855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 125473326183361025113065893 23526248659380192208699855)
      ·
        refine ⟨35289372989070288313049783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23526248659380192208699855 35289372989070288313049783)
        ·
          refine ⟨52934059483605432469574675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35289372989070288313049783 52934059483605432469574675)
          ·
            refine ⟨79401089225408148704362013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52934059483605432469574675 79401089225408148704362013)
            ·
              refine ⟨29775408459528055764135755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79401089225408148704362013 29775408459528055764135755)
              ·
                refine ⟨44663112689292083646203633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29775408459528055764135755 44663112689292083646203633)
                ·
                  refine ⟨33497334516969062734652725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44663112689292083646203633 33497334516969062734652725)
                  ·
                    refine ⟨3140375110965849631373693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33497334516969062734652725 3140375110965849631373693)
                    ·
                      refine ⟨1177640666612193611765135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3140375110965849631373693 1177640666612193611765135)
                      ·
                        rfl

theorem cell23_2293447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 1, 2, 5, 3].length) (baseStart_2293447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2293447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2293447 prefixEnd_2293447 := by exact prefixLift 2293447
  have htrace : WordTrace (prefixWord ++ tailWord_2293447) baseStart_2293447 baseEnd_2293447 := by
    simpa [prefixWord, tailWord_2293447, baseEnd_2293447] using wordTrace_append hprefix tailTrace_2293447
  have hstable : (prefixWord ++ tailWord_2293447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2293447).length < 2 ^ (prefixWord ++ tailWord_2293447).sum := by decide
  have hdescent : baseEnd_2293447 < baseStart_2293447 := by decide
  rcases family_descends (prefixWord ++ tailWord_2293447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2293458 : List Nat := [3, 2, 2, 2, 2, 1, 3, 3, 1, 4]
def baseStart_2293458 : Nat := 118140960795 + 2293458 * 2 ^ 59
def prefixEnd_2293458 : Nat := 4983230072969 + 3 ^ 40 * 2293458 * 2
def baseEnd_2293458 : Nat := 392548771633131022909195

theorem tailTrace_2293458 : CollatzResearch.WordTrace tailWord_2293458 prefixEnd_2293458 392548771633131022909195 := by
  unfold tailWord_2293458
  simp only [CollatzResearch.WordTrace]
  refine ⟨20912321331300208071840257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55766190216800554858240685 20912321331300208071840257)
  ·
    refine ⟨15684240998475156053880193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20912321331300208071840257 15684240998475156053880193)
    ·
      refine ⟨11763180748856367040410145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15684240998475156053880193 11763180748856367040410145)
      ·
        refine ⟨8822385561642275280307609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11763180748856367040410145 8822385561642275280307609)
        ·
          refine ⟨6616789171231706460230707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8822385561642275280307609 6616789171231706460230707)
          ·
            refine ⟨9925183756847559690346061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6616789171231706460230707 9925183756847559690346061)
            ·
              refine ⟨3721943908817834883879773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9925183756847559690346061 3721943908817834883879773)
              ·
                refine ⟨1395728965806688081454915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3721943908817834883879773 1395728965806688081454915)
                ·
                  refine ⟨2093593448710032122182373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1395728965806688081454915 2093593448710032122182373)
                  ·
                    refine ⟨392548771633131022909195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2093593448710032122182373 392548771633131022909195)
                    ·
                      rfl

theorem cell23_2293458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 3, 3, 1, 4].length) (baseStart_2293458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2293458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2293458 prefixEnd_2293458 := by exact prefixLift 2293458
  have htrace : WordTrace (prefixWord ++ tailWord_2293458) baseStart_2293458 baseEnd_2293458 := by
    simpa [prefixWord, tailWord_2293458, baseEnd_2293458] using wordTrace_append hprefix tailTrace_2293458
  have hstable : (prefixWord ++ tailWord_2293458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2293458).length < 2 ^ (prefixWord ++ tailWord_2293458).sum := by decide
  have hdescent : baseEnd_2293458 < baseStart_2293458 := by decide
  rcases family_descends (prefixWord ++ tailWord_2293458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2293468 : List Nat := [2, 2, 5, 1, 2, 1, 1, 2, 2, 2, 3]
def baseStart_2293468 : Nat := 118140960795 + 2293468 * 2 ^ 59
def prefixEnd_2293468 : Nat := 4983230072969 + 3 ^ 40 * 2293468 * 2
def baseEnd_2293468 : Nat := 1177651449705938029602539

theorem tailTrace_2293468 : CollatzResearch.WordTrace tailWord_2293468 prefixEnd_2293468 1177651449705938029602539 := by
  unfold tailWord_2293468
  simp only [CollatzResearch.WordTrace]
  refine ⟨41824825027582301997612529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55766433370109735996816705 41824825027582301997612529)
  ·
    refine ⟨31368618770686726498209397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41824825027582301997612529 31368618770686726498209397)
    ·
      refine ⟨2940808009751880609207131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 31368618770686726498209397 2940808009751880609207131)
      ·
        refine ⟨4411212014627820913810697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2940808009751880609207131 4411212014627820913810697)
        ·
          refine ⟨3308409010970865685358023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4411212014627820913810697 3308409010970865685358023)
          ·
            refine ⟨4962613516456298528037035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3308409010970865685358023 4962613516456298528037035)
            ·
              refine ⟨7443920274684447792055553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4962613516456298528037035 7443920274684447792055553)
              ·
                refine ⟨5582940206013335844041665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7443920274684447792055553 5582940206013335844041665)
                ·
                  refine ⟨4187205154510001883031249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5582940206013335844041665 4187205154510001883031249)
                  ·
                    refine ⟨3140403865882501412273437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4187205154510001883031249 3140403865882501412273437)
                    ·
                      refine ⟨1177651449705938029602539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3140403865882501412273437 1177651449705938029602539)
                      ·
                        rfl

theorem cell23_2293468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_2293468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2293468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2293468 prefixEnd_2293468 := by exact prefixLift 2293468
  have htrace : WordTrace (prefixWord ++ tailWord_2293468) baseStart_2293468 baseEnd_2293468 := by
    simpa [prefixWord, tailWord_2293468, baseEnd_2293468] using wordTrace_append hprefix tailTrace_2293468
  have hstable : (prefixWord ++ tailWord_2293468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2293468).length < 2 ^ (prefixWord ++ tailWord_2293468).sum := by decide
  have hdescent : baseEnd_2293468 < baseStart_2293468 := by decide
  rcases family_descends (prefixWord ++ tailWord_2293468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2293475 : List Nat := [1, 1, 1, 7, 2, 1, 3, 2, 1, 4]
def baseStart_2293475 : Nat := 118140960795 + 2293475 * 2 ^ 59
def prefixEnd_2293475 : Nat := 4983230072969 + 3 ^ 40 * 2293475 * 2
def baseEnd_2293475 : Nat := 392551681356839834071669

theorem tailTrace_2293475 : CollatzResearch.WordTrace tailWord_2293475 prefixEnd_2293475 392551681356839834071669 := by
  unfold tailWord_2293475
  simp only [CollatzResearch.WordTrace]
  refine ⟨83649905366139244190729879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55766603577426162793819919 83649905366139244190729879)
  ·
    refine ⟨125474858049208866286094819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83649905366139244190729879 125474858049208866286094819)
    ·
      refine ⟨188212287073813299429142229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125474858049208866286094819 188212287073813299429142229)
      ·
        refine ⟨4411225478292499205370521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 188212287073813299429142229 4411225478292499205370521)
        ·
          refine ⟨3308419108719374404027891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4411225478292499205370521 3308419108719374404027891)
          ·
            refine ⟨4962628663079061606041837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3308419108719374404027891 4962628663079061606041837)
            ·
              refine ⟨1860985748654648102265689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4962628663079061606041837 1860985748654648102265689)
              ·
                refine ⟨1395739311490986076699267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1860985748654648102265689 1395739311490986076699267)
                ·
                  refine ⟨2093608967236479115048901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1395739311490986076699267 2093608967236479115048901)
                  ·
                    refine ⟨392551681356839834071669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2093608967236479115048901 392551681356839834071669)
                    ·
                      rfl

theorem cell23_2293475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 3, 2, 1, 4].length) (baseStart_2293475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2293475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2293475 prefixEnd_2293475 := by exact prefixLift 2293475
  have htrace : WordTrace (prefixWord ++ tailWord_2293475) baseStart_2293475 baseEnd_2293475 := by
    simpa [prefixWord, tailWord_2293475, baseEnd_2293475] using wordTrace_append hprefix tailTrace_2293475
  have hstable : (prefixWord ++ tailWord_2293475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2293475).length < 2 ^ (prefixWord ++ tailWord_2293475).sum := by decide
  have hdescent : baseEnd_2293475 < baseStart_2293475 := by decide
  rcases family_descends (prefixWord ++ tailWord_2293475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2293507 : List Nat := [1, 1, 1, 3, 2, 2, 2, 2, 3, 1, 5]
def baseStart_2293507 : Nat := 118140960795 + 2293507 * 2 ^ 59
def prefixEnd_2293507 : Nat := 4983230072969 + 3 ^ 40 * 2293507 * 2
def baseEnd_2293507 : Nat := 1177671475451463377014859

theorem tailTrace_2293507 : CollatzResearch.WordTrace tailWord_2293507 prefixEnd_2293507 1177671475451463377014859 := by
  unfold tailWord_2293507
  simp only [CollatzResearch.WordTrace]
  refine ⟨83651072502023313655894775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55767381668015542437263183 83651072502023313655894775)
  ·
    refine ⟨125476608753034970483842163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83651072502023313655894775 125476608753034970483842163)
    ·
      refine ⟨188214913129552455725763245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125476608753034970483842163 188214913129552455725763245)
      ·
        refine ⟨70580592423582170897161217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 188214913129552455725763245 70580592423582170897161217)
        ·
          refine ⟨52935444317686628172870913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70580592423582170897161217 52935444317686628172870913)
          ·
            refine ⟨39701583238264971129653185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52935444317686628172870913 39701583238264971129653185)
            ·
              refine ⟨29776187428698728347239889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39701583238264971129653185 29776187428698728347239889)
              ·
                refine ⟨22332140571524046260429917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29776187428698728347239889 22332140571524046260429917)
                ·
                  refine ⟨8374552714321517347661219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22332140571524046260429917 8374552714321517347661219)
                  ·
                    refine ⟨12561829071482276021491829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8374552714321517347661219 12561829071482276021491829)
                    ·
                      refine ⟨1177671475451463377014859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12561829071482276021491829 1177671475451463377014859)
                      ·
                        rfl

theorem cell23_2293507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 2, 3, 1, 5].length) (baseStart_2293507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2293507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2293507 prefixEnd_2293507 := by exact prefixLift 2293507
  have htrace : WordTrace (prefixWord ++ tailWord_2293507) baseStart_2293507 baseEnd_2293507 := by
    simpa [prefixWord, tailWord_2293507, baseEnd_2293507] using wordTrace_append hprefix tailTrace_2293507
  have hstable : (prefixWord ++ tailWord_2293507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2293507).length < 2 ^ (prefixWord ++ tailWord_2293507).sum := by decide
  have hdescent : baseEnd_2293507 < baseStart_2293507 := by decide
  rcases family_descends (prefixWord ++ tailWord_2293507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2293508 : List Nat := [2, 3, 2, 2, 1, 3, 2, 1, 2, 3, 2]
def baseStart_2293508 : Nat := 118140960795 + 2293508 * 2 ^ 59
def prefixEnd_2293508 : Nat := 4983230072969 + 3 ^ 40 * 2293508 * 2
def baseEnd_2293508 : Nat := 1177671988932117873102355

theorem tailTrace_2293508 : CollatzResearch.WordTrace tailWord_2293508 prefixEnd_2293508 1177671988932117873102355 := by
  unfold tailWord_2293508
  simp only [CollatzResearch.WordTrace]
  refine ⟨41825554487509845413340589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55767405983346460551120785 41825554487509845413340589)
  ·
    refine ⟨15684582932816192030002721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41825554487509845413340589 15684582932816192030002721)
    ·
      refine ⟨11763437199612144022502041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15684582932816192030002721 11763437199612144022502041)
      ·
        refine ⟨8822577899709108016876531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11763437199612144022502041 8822577899709108016876531)
        ·
          refine ⟨13233866849563662025314797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8822577899709108016876531 13233866849563662025314797)
          ·
            refine ⟨4962700068586373259493049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13233866849563662025314797 4962700068586373259493049)
            ·
              refine ⟨3722025051439779944619787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4962700068586373259493049 3722025051439779944619787)
              ·
                refine ⟨5583037577159669916929681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3722025051439779944619787 5583037577159669916929681)
                ·
                  refine ⟨4187278182869752437697261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5583037577159669916929681 4187278182869752437697261)
                  ·
                    refine ⟨1570229318576157164136473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4187278182869752437697261 1570229318576157164136473)
                    ·
                      refine ⟨1177671988932117873102355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1570229318576157164136473 1177671988932117873102355)
                      ·
                        rfl

theorem cell23_2293508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 2, 1, 2, 3, 2].length) (baseStart_2293508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2293508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2293508 prefixEnd_2293508 := by exact prefixLift 2293508
  have htrace : WordTrace (prefixWord ++ tailWord_2293508) baseStart_2293508 baseEnd_2293508 := by
    simpa [prefixWord, tailWord_2293508, baseEnd_2293508] using wordTrace_append hprefix tailTrace_2293508
  have hstable : (prefixWord ++ tailWord_2293508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2293508).length < 2 ^ (prefixWord ++ tailWord_2293508).sum := by decide
  have hdescent : baseEnd_2293508 < baseStart_2293508 := by decide
  rcases family_descends (prefixWord ++ tailWord_2293508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2293514 : List Nat := [3, 1, 2, 2, 1, 4, 1, 2, 1, 6]
def baseStart_2293514 : Nat := 118140960795 + 2293514 * 2 ^ 59
def prefixEnd_2293514 : Nat := 4983230072969 + 3 ^ 40 * 2293514 * 2
def baseEnd_2293514 : Nat := 392558356605348283209109

theorem tailTrace_2293514 : CollatzResearch.WordTrace tailWord_2293514 prefixEnd_2293514 392558356605348283209109 := by
  unfold tailWord_2293514
  simp only [CollatzResearch.WordTrace]
  refine ⟨20912831953249488462849899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55767551875331969234266397 20912831953249488462849899)
  ·
    refine ⟨31369247929874232694274849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20912831953249488462849899 31369247929874232694274849)
    ·
      refine ⟨23526935947405674520706137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31369247929874232694274849 23526935947405674520706137)
      ·
        refine ⟨17645201960554255890529603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23526935947405674520706137 17645201960554255890529603)
        ·
          refine ⟨26467802940831383835794405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17645201960554255890529603 26467802940831383835794405)
          ·
            refine ⟨4962713051405884469211451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26467802940831383835794405 4962713051405884469211451)
            ·
              refine ⟨7444069577108826703817177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4962713051405884469211451 7444069577108826703817177)
              ·
                refine ⟨5583052182831620027862883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7444069577108826703817177 5583052182831620027862883)
                ·
                  refine ⟨8374578274247430041794325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5583052182831620027862883 8374578274247430041794325)
                  ·
                    refine ⟨392558356605348283209109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8374578274247430041794325 392558356605348283209109)
                    ·
                      rfl

theorem cell23_2293514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 2, 1, 6].length) (baseStart_2293514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2293514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2293514 prefixEnd_2293514 := by exact prefixLift 2293514
  have htrace : WordTrace (prefixWord ++ tailWord_2293514) baseStart_2293514 baseEnd_2293514 := by
    simpa [prefixWord, tailWord_2293514, baseEnd_2293514] using wordTrace_append hprefix tailTrace_2293514
  have hstable : (prefixWord ++ tailWord_2293514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2293514).length < 2 ^ (prefixWord ++ tailWord_2293514).sum := by decide
  have hdescent : baseEnd_2293514 < baseStart_2293514 := by decide
  rcases family_descends (prefixWord ++ tailWord_2293514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2293527 : List Nat := [1, 1, 3, 4, 2, 12]
def baseStart_2293527 : Nat := 118140960795 + 2293527 * 2 ^ 59
def prefixEnd_2293527 : Nat := 4983230072969 + 3 ^ 40 * 2293527 * 2
def baseEnd_2293527 : Nat := 4846426934422030036069

theorem tailTrace_2293527 : CollatzResearch.WordTrace tailWord_2293527 prefixEnd_2293527 4846426934422030036069 := by
  unfold tailWord_2293527
  simp only [CollatzResearch.WordTrace]
  refine ⟨83651801961950857071622835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55767867974633904714415223 83651801961950857071622835)
  ·
    refine ⟨125477702942926285607434253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83651801961950857071622835 125477702942926285607434253)
    ·
      refine ⟨47054138603597357102787845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 125477702942926285607434253 47054138603597357102787845)
      ·
        refine ⟨8822650988174504456772721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47054138603597357102787845 8822650988174504456772721)
        ·
          refine ⟨6616988241130878342579541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8822650988174504456772721 6616988241130878342579541)
          ·
            refine ⟨4846426934422030036069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 6616988241130878342579541 4846426934422030036069)
            ·
              rfl

theorem cell23_2293527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 12].length) (baseStart_2293527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2293527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2293527 prefixEnd_2293527 := by exact prefixLift 2293527
  have htrace : WordTrace (prefixWord ++ tailWord_2293527) baseStart_2293527 baseEnd_2293527 := by
    simpa [prefixWord, tailWord_2293527, baseEnd_2293527] using wordTrace_append hprefix tailTrace_2293527
  have hstable : (prefixWord ++ tailWord_2293527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2293527).length < 2 ^ (prefixWord ++ tailWord_2293527).sum := by decide
  have hdescent : baseEnd_2293527 < baseStart_2293527 := by decide
  rcases family_descends (prefixWord ++ tailWord_2293527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2293538 : List Nat := [3, 3, 1, 1, 2, 1, 2, 3, 3, 2, 2]
def baseStart_2293538 : Nat := 118140960795 + 2293538 * 2 ^ 59
def prefixEnd_2293538 : Nat := 4983230072969 + 3 ^ 40 * 2293538 * 2
def baseEnd_2293538 : Nat := 1177687393351752755727217

theorem tailTrace_2293538 : CollatzResearch.WordTrace tailWord_2293538 prefixEnd_2293538 1177687393351752755727217 := by
  unfold tailWord_2293538
  simp only [CollatzResearch.WordTrace]
  refine ⟨20913050791227751487568317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55768135443274003966848845 20913050791227751487568317)
  ·
    refine ⟨7842394046710406807838119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20913050791227751487568317 7842394046710406807838119)
    ·
      refine ⟨11763591070065610211757179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7842394046710406807838119 11763591070065610211757179)
      ·
        refine ⟨17645386605098415317635769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11763591070065610211757179 17645386605098415317635769)
        ·
          refine ⟨13234039953823811488226827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17645386605098415317635769 13234039953823811488226827)
          ·
            refine ⟨19851059930735717232340241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13234039953823811488226827 19851059930735717232340241)
            ·
              refine ⟨14888294948051787924255181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19851059930735717232340241 14888294948051787924255181)
              ·
                refine ⟨5583110605519420471595693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14888294948051787924255181 5583110605519420471595693)
                ·
                  refine ⟨2093666477069782676848385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5583110605519420471595693 2093666477069782676848385)
                  ·
                    refine ⟨1570249857802337007636289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2093666477069782676848385 1570249857802337007636289)
                    ·
                      refine ⟨1177687393351752755727217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1570249857802337007636289 1177687393351752755727217)
                      ·
                        rfl

theorem cell23_2293538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 3, 3, 2, 2].length) (baseStart_2293538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2293538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2293538 prefixEnd_2293538 := by exact prefixLift 2293538
  have htrace : WordTrace (prefixWord ++ tailWord_2293538) baseStart_2293538 baseEnd_2293538 := by
    simpa [prefixWord, tailWord_2293538, baseEnd_2293538] using wordTrace_append hprefix tailTrace_2293538
  have hstable : (prefixWord ++ tailWord_2293538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2293538).length < 2 ^ (prefixWord ++ tailWord_2293538).sum := by decide
  have hdescent : baseEnd_2293538 < baseStart_2293538 := by decide
  rcases family_descends (prefixWord ++ tailWord_2293538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2293544 : List Nat := [2, 1, 5, 1, 1, 2, 3, 8]
def baseStart_2293544 : Nat := 118140960795 + 2293544 * 2 ^ 59
def prefixEnd_2293544 : Nat := 4983230072969 + 3 ^ 40 * 2293544 * 2
def baseEnd_2293544 : Nat := 43618165712432582676007

theorem tailTrace_2293544 : CollatzResearch.WordTrace tailWord_2293544 prefixEnd_2293544 43618165712432582676007 := by
  unfold tailWord_2293544
  simp only [CollatzResearch.WordTrace]
  refine ⟨41826211001444634487495843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55768281335259512649994457 41826211001444634487495843)
  ·
    refine ⟨62739316502166951731243765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41826211001444634487495843 62739316502166951731243765)
    ·
      refine ⟨5881810922078151724804103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 62739316502166951731243765 5881810922078151724804103)
      ·
        refine ⟨8822716383117227587206155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5881810922078151724804103 8822716383117227587206155)
        ·
          refine ⟨13234074574675841380809233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8822716383117227587206155 13234074574675841380809233)
          ·
            refine ⟨9925555931006881035606925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13234074574675841380809233 9925555931006881035606925)
            ·
              refine ⟨3722083474127580388352597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9925555931006881035606925 3722083474127580388352597)
              ·
                refine ⟨43618165712432582676007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3722083474127580388352597 43618165712432582676007)
                ·
                  rfl

theorem cell23_2293544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 3, 8].length) (baseStart_2293544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2293544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2293544 prefixEnd_2293544 := by exact prefixLift 2293544
  have htrace : WordTrace (prefixWord ++ tailWord_2293544) baseStart_2293544 baseEnd_2293544 := by
    simpa [prefixWord, tailWord_2293544, baseEnd_2293544] using wordTrace_append hprefix tailTrace_2293544
  have hstable : (prefixWord ++ tailWord_2293544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2293544).length < 2 ^ (prefixWord ++ tailWord_2293544).sum := by decide
  have hdescent : baseEnd_2293544 < baseStart_2293544 := by decide
  rcases family_descends (prefixWord ++ tailWord_2293544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2293558 : List Nat := [5, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3]
def baseStart_2293558 : Nat := 118140960795 + 2293558 * 2 ^ 59
def prefixEnd_2293558 : Nat := 4983230072969 + 3 ^ 40 * 2293558 * 2
def baseEnd_2293558 : Nat := 1177697662964842677477125

theorem tailTrace_2293558 : CollatzResearch.WordTrace tailWord_2293558 prefixEnd_2293558 1177697662964842677477125 := by
  unfold tailWord_2293558
  simp only [CollatzResearch.WordTrace]
  refine ⟨5228308289052409335375083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 55768621749892366244000885 5228308289052409335375083)
  ·
    refine ⟨7842462433578614003062625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5228308289052409335375083 7842462433578614003062625)
    ·
      refine ⟨5881846825183960502296969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7842462433578614003062625 5881846825183960502296969)
      ·
        refine ⟨4411385118887970376722727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5881846825183960502296969 4411385118887970376722727)
        ·
          refine ⟨6617077678331955565084091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4411385118887970376722727 6617077678331955565084091)
          ·
            refine ⟨9925616517497933347626137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6617077678331955565084091 9925616517497933347626137)
            ·
              refine ⟨7444212388123450010719603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9925616517497933347626137 7444212388123450010719603)
              ·
                refine ⟨11166318582185175016079405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7444212388123450010719603 11166318582185175016079405)
                ·
                  refine ⟨4187369468319440631029777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11166318582185175016079405 4187369468319440631029777)
                  ·
                    refine ⟨3140527101239580473272333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4187369468319440631029777 3140527101239580473272333)
                    ·
                      refine ⟨1177697662964842677477125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3140527101239580473272333 1177697662964842677477125)
                      ·
                        rfl

theorem cell23_2293558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_2293558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2293558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2293558 prefixEnd_2293558 := by exact prefixLift 2293558
  have htrace : WordTrace (prefixWord ++ tailWord_2293558) baseStart_2293558 baseEnd_2293558 := by
    simpa [prefixWord, tailWord_2293558, baseEnd_2293558] using wordTrace_append hprefix tailTrace_2293558
  have hstable : (prefixWord ++ tailWord_2293558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2293558).length < 2 ^ (prefixWord ++ tailWord_2293558).sum := by decide
  have hdescent : baseEnd_2293558 < baseStart_2293558 := by decide
  rcases family_descends (prefixWord ++ tailWord_2293558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2293588 : List Nat := [2, 4, 1, 1, 3, 2, 1, 1, 4, 1, 3]
def baseStart_2293588 : Nat := 118140960795 + 2293588 * 2 ^ 59
def prefixEnd_2293588 : Nat := 4983230072969 + 3 ^ 40 * 2293588 * 2
def baseEnd_2293588 : Nat := 1177713067384477560101987

theorem tailTrace_2293588 : CollatzResearch.WordTrace tailWord_2293588 prefixEnd_2293588 1177713067384477560101987 := by
  unfold tailWord_2293588
  simp only [CollatzResearch.WordTrace]
  refine ⟨41827013407364932244796709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55769351209819909659728945 41827013407364932244796709)
  ·
    refine ⟨7842565013880924795899383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41827013407364932244796709 7842565013880924795899383)
    ·
      refine ⟨11763847520821387193849075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7842565013880924795899383 11763847520821387193849075)
      ·
        refine ⟨17645771281232080790773613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11763847520821387193849075 17645771281232080790773613)
        ·
          refine ⟨6617164230462030296540105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17645771281232080790773613 6617164230462030296540105)
          ·
            refine ⟨4962873172846522722405079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6617164230462030296540105 4962873172846522722405079)
            ·
              refine ⟨7444309759269784083607619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4962873172846522722405079 7444309759269784083607619)
              ·
                refine ⟨11166464638904676125411429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7444309759269784083607619 11166464638904676125411429)
                ·
                  refine ⟨2093712119794626773514643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11166464638904676125411429 2093712119794626773514643)
                  ·
                    refine ⟨3140568179691940160271965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2093712119794626773514643 3140568179691940160271965)
                    ·
                      refine ⟨1177713067384477560101987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3140568179691940160271965 1177713067384477560101987)
                      ·
                        rfl

theorem cell23_2293588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 1, 4, 1, 3].length) (baseStart_2293588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2293588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2293588 prefixEnd_2293588 := by exact prefixLift 2293588
  have htrace : WordTrace (prefixWord ++ tailWord_2293588) baseStart_2293588 baseEnd_2293588 := by
    simpa [prefixWord, tailWord_2293588, baseEnd_2293588] using wordTrace_append hprefix tailTrace_2293588
  have hstable : (prefixWord ++ tailWord_2293588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2293588).length < 2 ^ (prefixWord ++ tailWord_2293588).sum := by decide
  have hdescent : baseEnd_2293588 < baseStart_2293588 := by decide
  rcases family_descends (prefixWord ++ tailWord_2293588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2293664 : List Nat := [2, 1, 1, 4, 1, 1, 1, 1, 6, 5]
def baseStart_2293664 : Nat := 118140960795 + 2293664 * 2 ^ 59
def prefixEnd_2293664 : Nat := 4983230072969 + 3 ^ 40 * 2293664 * 2
def baseEnd_2293664 : Nat := 392584030638073087583879

theorem tailTrace_2293664 : CollatzResearch.WordTrace tailWord_2293664 prefixEnd_2293664 392584030638073087583879 := by
  unfold tailWord_2293664
  simp only [CollatzResearch.WordTrace]
  refine ⟨41828399381227264734680023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55771199174969686312906697 41828399381227264734680023)
  ·
    refine ⟨62742599071840897102020035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41828399381227264734680023 62742599071840897102020035)
    ·
      refine ⟨94113898607761345653030053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62742599071840897102020035 94113898607761345653030053)
      ·
        refine ⟨17646355988955252309943135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 94113898607761345653030053 17646355988955252309943135)
        ·
          refine ⟨26469533983432878464914703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17646355988955252309943135 26469533983432878464914703)
          ·
            refine ⟨39704300975149317697372055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26469533983432878464914703 39704300975149317697372055)
            ·
              refine ⟨59556451462723976546058083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39704300975149317697372055 59556451462723976546058083)
              ·
                refine ⟨89334677194085964819087125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59556451462723976546058083 89334677194085964819087125)
                ·
                  refine ⟨4187562993472779600894709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 89334677194085964819087125 4187562993472779600894709)
                  ·
                    refine ⟨392584030638073087583879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4187562993472779600894709 392584030638073087583879)
                    ·
                      rfl

theorem cell23_2293664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 6, 5].length) (baseStart_2293664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2293664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2293664 prefixEnd_2293664 := by exact prefixLift 2293664
  have htrace : WordTrace (prefixWord ++ tailWord_2293664) baseStart_2293664 baseEnd_2293664 := by
    simpa [prefixWord, tailWord_2293664, baseEnd_2293664] using wordTrace_append hprefix tailTrace_2293664
  have hstable : (prefixWord ++ tailWord_2293664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2293664).length < 2 ^ (prefixWord ++ tailWord_2293664).sum := by decide
  have hdescent : baseEnd_2293664 < baseStart_2293664 := by decide
  rcases family_descends (prefixWord ++ tailWord_2293664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2293681 : List Nat := [1, 2, 2, 4, 2, 1, 1, 3, 2, 5]
def baseStart_2293681 : Nat := 118140960795 + 2293681 * 2 ^ 59
def prefixEnd_2293681 : Nat := 4983230072969 + 3 ^ 40 * 2293681 * 2
def baseEnd_2293681 : Nat := 392586940361781898746353

theorem tailTrace_2293681 : CollatzResearch.WordTrace tailWord_2293681 prefixEnd_2293681 392586940361781898746353 := by
  unfold tailWord_2293681
  simp only [CollatzResearch.WordTrace]
  refine ⟨83657418803392941372728897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55771612535595294248485931 83657418803392941372728897)
  ·
    refine ⟨62743064102544706029546673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83657418803392941372728897 62743064102544706029546673)
    ·
      refine ⟨47057298076908529522160005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62743064102544706029546673 47057298076908529522160005)
      ·
        refine ⟨8823243389420349285405001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47057298076908529522160005 8823243389420349285405001)
        ·
          refine ⟨6617432542065261964053751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8823243389420349285405001 6617432542065261964053751)
          ·
            refine ⟨9926148813097892946080627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6617432542065261964053751 9926148813097892946080627)
            ·
              refine ⟨14889223219646839419120941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9926148813097892946080627 14889223219646839419120941)
              ·
                refine ⟨5583458707367564782170353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14889223219646839419120941 5583458707367564782170353)
                ·
                  refine ⟨4187594030525673586627765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5583458707367564782170353 4187594030525673586627765)
                  ·
                    refine ⟨392586940361781898746353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4187594030525673586627765 392586940361781898746353)
                    ·
                      rfl

theorem cell23_2293681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 3, 2, 5].length) (baseStart_2293681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2293681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2293681 prefixEnd_2293681 := by exact prefixLift 2293681
  have htrace : WordTrace (prefixWord ++ tailWord_2293681) baseStart_2293681 baseEnd_2293681 := by
    simpa [prefixWord, tailWord_2293681, baseEnd_2293681] using wordTrace_append hprefix tailTrace_2293681
  have hstable : (prefixWord ++ tailWord_2293681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2293681).length < 2 ^ (prefixWord ++ tailWord_2293681).sum := by decide
  have hdescent : baseEnd_2293681 < baseStart_2293681 := by decide
  rcases family_descends (prefixWord ++ tailWord_2293681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2293711 : List Nat := [1, 1, 2, 1, 1, 5, 2, 3, 3, 4]
def baseStart_2293711 : Nat := 118140960795 + 2293711 * 2 ^ 59
def prefixEnd_2293711 : Nat := 4983230072969 + 3 ^ 40 * 2293711 * 2
def baseEnd_2293711 : Nat := 392592075168326859621307

theorem tailTrace_2293711 : CollatzResearch.WordTrace tailWord_2293711 prefixEnd_2293711 392592075168326859621307 := by
  unfold tailWord_2293711
  simp only [CollatzResearch.WordTrace]
  refine ⟨83658512993284256496320987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55772341995522837664213991 83658512993284256496320987)
  ·
    refine ⟨125487769489926384744481481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83658512993284256496320987 125487769489926384744481481)
    ·
      refine ⟨94115827117444788558361111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125487769489926384744481481 94115827117444788558361111)
      ·
        refine ⟨141173740676167182837541667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94115827117444788558361111 141173740676167182837541667)
        ·
          refine ⟨211760611014250774256312501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141173740676167182837541667 211760611014250774256312501)
          ·
            refine ⟨19852557282586010086529297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 211760611014250774256312501 19852557282586010086529297)
            ·
              refine ⟨14889417961939507564896973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19852557282586010086529297 14889417961939507564896973)
              ·
                refine ⟨5583531735727315336836365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14889417961939507564896973 5583531735727315336836365)
                ·
                  refine ⟨2093824400897743251313637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5583531735727315336836365 2093824400897743251313637)
                  ·
                    refine ⟨392592075168326859621307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2093824400897743251313637 392592075168326859621307)
                    ·
                      rfl

theorem cell23_2293711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 3, 3, 4].length) (baseStart_2293711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2293711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2293711 prefixEnd_2293711 := by exact prefixLift 2293711
  have htrace : WordTrace (prefixWord ++ tailWord_2293711) baseStart_2293711 baseEnd_2293711 := by
    simpa [prefixWord, tailWord_2293711, baseEnd_2293711] using wordTrace_append hprefix tailTrace_2293711
  have hstable : (prefixWord ++ tailWord_2293711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2293711).length < 2 ^ (prefixWord ++ tailWord_2293711).sum := by decide
  have hdescent : baseEnd_2293711 < baseStart_2293711 := by decide
  rcases family_descends (prefixWord ++ tailWord_2293711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2293735 : List Nat := [1, 1, 5, 2, 3, 2, 1, 1, 2, 1, 4]
def baseStart_2293735 : Nat := 118140960795 + 2293735 * 2 ^ 59
def prefixEnd_2293735 : Nat := 4983230072969 + 3 ^ 40 * 2293735 * 2
def baseEnd_2293735 : Nat := 1177788549040688484963811

theorem tailTrace_2293735 : CollatzResearch.WordTrace tailWord_2293735 prefixEnd_2293735 1177788549040688484963811 := by
  unfold tailWord_2293735
  simp only [CollatzResearch.WordTrace]
  refine ⟨83659388345197308595194659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55772925563464872396796439 83659388345197308595194659)
  ·
    refine ⟨125489082517795962892791989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83659388345197308595194659 125489082517795962892791989)
    ·
      refine ⟨11764601486043371521199249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 125489082517795962892791989 11764601486043371521199249)
      ·
        refine ⟨8823451114532528640899437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11764601486043371521199249 8823451114532528640899437)
        ·
          refine ⟨3308794167949698240337289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8823451114532528640899437 3308794167949698240337289)
          ·
            refine ⟨2481595625962273680252967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3308794167949698240337289 2481595625962273680252967)
            ·
              refine ⟨3722393438943410520379451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2481595625962273680252967 3722393438943410520379451)
              ·
                refine ⟨5583590158415115780569177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3722393438943410520379451 5583590158415115780569177)
                ·
                  refine ⟨4187692618811336835426883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5583590158415115780569177 4187692618811336835426883)
                  ·
                    refine ⟨6281538928217005253140325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4187692618811336835426883 6281538928217005253140325)
                    ·
                      refine ⟨1177788549040688484963811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6281538928217005253140325 1177788549040688484963811)
                      ·
                        rfl

theorem cell23_2293735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 1, 1, 2, 1, 4].length) (baseStart_2293735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2293735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2293735 prefixEnd_2293735 := by exact prefixLift 2293735
  have htrace : WordTrace (prefixWord ++ tailWord_2293735) baseStart_2293735 baseEnd_2293735 := by
    simpa [prefixWord, tailWord_2293735, baseEnd_2293735] using wordTrace_append hprefix tailTrace_2293735
  have hstable : (prefixWord ++ tailWord_2293735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2293735).length < 2 ^ (prefixWord ++ tailWord_2293735).sum := by decide
  have hdescent : baseEnd_2293735 < baseStart_2293735 := by decide
  rcases family_descends (prefixWord ++ tailWord_2293735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2293758 : List Nat := [4, 2, 2, 2, 1, 2, 1, 1, 8]
def baseStart_2293758 : Nat := 118140960795 + 2293758 * 2 ^ 59
def prefixEnd_2293758 : Nat := 4983230072969 + 3 ^ 40 * 2293758 * 2
def baseEnd_2293758 : Nat := 130866706566193543886245

theorem tailTrace_2293758 : CollatzResearch.WordTrace tailWord_2293758 prefixEnd_2293758 130866706566193543886245 := by
  unfold tailWord_2293758
  simp only [CollatzResearch.WordTrace]
  refine ⟨10457528403014247940410241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55773484816075989015521285 10457528403014247940410241)
  ·
    refine ⟨7843146302260685955307681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10457528403014247940410241 7843146302260685955307681)
    ·
      refine ⟨5882359726695514466480761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7843146302260685955307681 5882359726695514466480761)
      ·
        refine ⟨4411769795021635849860571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5882359726695514466480761 4411769795021635849860571)
        ·
          refine ⟨6617654692532453774790857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4411769795021635849860571 6617654692532453774790857)
          ·
            refine ⟨4963241019399340331093143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6617654692532453774790857 4963241019399340331093143)
            ·
              refine ⟨7444861529099010496639715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4963241019399340331093143 7444861529099010496639715)
              ·
                refine ⟨11167292293648515744959573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7444861529099010496639715 11167292293648515744959573)
                ·
                  refine ⟨130866706566193543886245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11167292293648515744959573 130866706566193543886245)
                  ·
                    rfl

theorem cell23_2293758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 1, 8].length) (baseStart_2293758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2293758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2293758 prefixEnd_2293758 := by exact prefixLift 2293758
  have htrace : WordTrace (prefixWord ++ tailWord_2293758) baseStart_2293758 baseEnd_2293758 := by
    simpa [prefixWord, tailWord_2293758, baseEnd_2293758] using wordTrace_append hprefix tailTrace_2293758
  have hstable : (prefixWord ++ tailWord_2293758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2293758).length < 2 ^ (prefixWord ++ tailWord_2293758).sum := by decide
  have hdescent : baseEnd_2293758 < baseStart_2293758 := by decide
  rcases family_descends (prefixWord ++ tailWord_2293758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2293788 : List Nat := [2, 2, 3, 1, 3, 1, 1, 4, 1, 5]
def baseStart_2293788 : Nat := 118140960795 + 2293788 * 2 ^ 59
def prefixEnd_2293788 : Nat := 4983230072969 + 3 ^ 40 * 2293788 * 2
def baseEnd_2293788 : Nat := 392605254505125592533689

theorem tailTrace_2293788 : CollatzResearch.WordTrace tailWord_2293788 prefixEnd_2293788 392605254505125592533689 := by
  unfold tailWord_2293788
  simp only [CollatzResearch.WordTrace]
  refine ⟨41830660707002649323437009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55774214276003532431249345 41830660707002649323437009)
  ·
    refine ⟨31372995530251986992577757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41830660707002649323437009 31372995530251986992577757)
    ·
      refine ⟨11764873323844495122216659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31372995530251986992577757 11764873323844495122216659)
      ·
        refine ⟨17647309985766742683324989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11764873323844495122216659 17647309985766742683324989)
        ·
          refine ⟨6617741244662528506246871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17647309985766742683324989 6617741244662528506246871)
          ·
            refine ⟨9926611866993792759370307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6617741244662528506246871 9926611866993792759370307)
            ·
              refine ⟨14889917800490689139055461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9926611866993792759370307 14889917800490689139055461)
              ·
                refine ⟨2791859587592004213572899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14889917800490689139055461 2791859587592004213572899)
                ·
                  refine ⟨4187789381388006320359349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2791859587592004213572899 4187789381388006320359349)
                  ·
                    refine ⟨392605254505125592533689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4187789381388006320359349 392605254505125592533689)
                    ·
                      rfl

theorem cell23_2293788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 4, 1, 5].length) (baseStart_2293788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2293788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2293788 prefixEnd_2293788 := by exact prefixLift 2293788
  have htrace : WordTrace (prefixWord ++ tailWord_2293788) baseStart_2293788 baseEnd_2293788 := by
    simpa [prefixWord, tailWord_2293788, baseEnd_2293788] using wordTrace_append hprefix tailTrace_2293788
  have hstable : (prefixWord ++ tailWord_2293788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2293788).length < 2 ^ (prefixWord ++ tailWord_2293788).sum := by decide
  have hdescent : baseEnd_2293788 < baseStart_2293788 := by decide
  rcases family_descends (prefixWord ++ tailWord_2293788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2293808 : List Nat := [2, 1, 1, 1, 2, 5, 2, 3, 1, 1, 4]
def baseStart_2293808 : Nat := 118140960795 + 2293808 * 2 ^ 59
def prefixEnd_2293808 : Nat := 4983230072969 + 3 ^ 40 * 2293808 * 2
def baseEnd_2293808 : Nat := 1177826033128466699350975

theorem tailTrace_2293808 : CollatzResearch.WordTrace tailWord_2293808 prefixEnd_2293808 1177826033128466699350975 := by
  unfold tailWord_2293808
  simp only [CollatzResearch.WordTrace]
  refine ⟨41831025436966421031301039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55774700582621894708401385 41831025436966421031301039)
  ·
    refine ⟨62746538155449631546951559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41831025436966421031301039 62746538155449631546951559)
    ·
      refine ⟨94119807233174447320427339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62746538155449631546951559 94119807233174447320427339)
      ·
        refine ⟨141179710849761670980641009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94119807233174447320427339 141179710849761670980641009)
        ·
          refine ⟨105884783137321253235480757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 141179710849761670980641009 105884783137321253235480757)
          ·
            refine ⟨9926698419123867490826321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 105884783137321253235480757 9926698419123867490826321)
            ·
              refine ⟨7445023814342900618119741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9926698419123867490826321 7445023814342900618119741)
              ·
                refine ⟨2791883930378587731794903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7445023814342900618119741 2791883930378587731794903)
                ·
                  refine ⟨4187825895567881597692355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2791883930378587731794903 4187825895567881597692355)
                  ·
                    refine ⟨6281738843351822396538533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4187825895567881597692355 6281738843351822396538533)
                    ·
                      refine ⟨1177826033128466699350975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6281738843351822396538533 1177826033128466699350975)
                      ·
                        rfl

theorem cell23_2293808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 3, 1, 1, 4].length) (baseStart_2293808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2293808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2293808 prefixEnd_2293808 := by exact prefixLift 2293808
  have htrace : WordTrace (prefixWord ++ tailWord_2293808) baseStart_2293808 baseEnd_2293808 := by
    simpa [prefixWord, tailWord_2293808, baseEnd_2293808] using wordTrace_append hprefix tailTrace_2293808
  have hstable : (prefixWord ++ tailWord_2293808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2293808).length < 2 ^ (prefixWord ++ tailWord_2293808).sum := by decide
  have hdescent : baseEnd_2293808 < baseStart_2293808 := by decide
  rcases family_descends (prefixWord ++ tailWord_2293808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2293811 : List Nat := [1, 1, 1, 2, 4, 1, 3, 3, 1, 1, 5]
def baseStart_2293811 : Nat := 118140960795 + 2293811 * 2 ^ 59
def prefixEnd_2293811 : Nat := 4983230072969 + 3 ^ 40 * 2293811 * 2
def baseEnd_2293811 : Nat := 1177827573570430187613461

theorem tailTrace_2293811 : CollatzResearch.WordTrace tailWord_2293811 prefixEnd_2293811 1177827573570430187613461 := by
  unfold tailWord_2293811
  simp only [CollatzResearch.WordTrace]
  refine ⟨83662160292921973574961287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55774773528614649049974191 83662160292921973574961287)
  ·
    refine ⟨125493240439382960362441931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83662160292921973574961287 125493240439382960362441931)
    ·
      refine ⟨188239860659074440543662897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125493240439382960362441931 188239860659074440543662897)
      ·
        refine ⟨141179895494305830407747173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 188239860659074440543662897 141179895494305830407747173)
        ·
          refine ⟨26471230405182343201452595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 141179895494305830407747173 26471230405182343201452595)
          ·
            refine ⟨39706845607773514802178893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26471230405182343201452595 39706845607773514802178893)
            ·
              refine ⟨14890067102915068050817085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39706845607773514802178893 14890067102915068050817085)
              ·
                refine ⟨5583775163593150519056407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14890067102915068050817085 5583775163593150519056407)
                ·
                  refine ⟨8375662745389725778584611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5583775163593150519056407 8375662745389725778584611)
                  ·
                    refine ⟨12563494118084588667876917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8375662745389725778584611 12563494118084588667876917)
                    ·
                      refine ⟨1177827573570430187613461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12563494118084588667876917 1177827573570430187613461)
                      ·
                        rfl

theorem cell23_2293811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 3, 1, 1, 5].length) (baseStart_2293811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2293811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2293811 prefixEnd_2293811 := by exact prefixLift 2293811
  have htrace : WordTrace (prefixWord ++ tailWord_2293811) baseStart_2293811 baseEnd_2293811 := by
    simpa [prefixWord, tailWord_2293811, baseEnd_2293811] using wordTrace_append hprefix tailTrace_2293811
  have hstable : (prefixWord ++ tailWord_2293811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2293811).length < 2 ^ (prefixWord ++ tailWord_2293811).sum := by decide
  have hdescent : baseEnd_2293811 < baseStart_2293811 := by decide
  rcases family_descends (prefixWord ++ tailWord_2293811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2293818 : List Nat := [3, 1, 1, 1, 3, 1, 1, 6, 2, 4]
def baseStart_2293818 : Nat := 118140960795 + 2293818 * 2 ^ 59
def prefixEnd_2293818 : Nat := 4983230072969 + 3 ^ 40 * 2293818 * 2
def baseEnd_2293818 : Nat := 392610389311670553408643

theorem tailTrace_2293818 : CollatzResearch.WordTrace tailWord_2293818 prefixEnd_2293818 392610389311670553408643 := by
  unfold tailWord_2293818
  simp only [CollatzResearch.WordTrace]
  refine ⟨20915603900974153442616527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55774943735931075846977405 20915603900974153442616527)
  ·
    refine ⟨31373405851461230163924791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20915603900974153442616527 31373405851461230163924791)
    ·
      refine ⟨47060108777191845245887187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31373405851461230163924791 47060108777191845245887187)
      ·
        refine ⟨70590163165787767868830781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47060108777191845245887187 70590163165787767868830781)
        ·
          refine ⟨26471311187170412950811543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70590163165787767868830781 26471311187170412950811543)
          ·
            refine ⟨39706966780755619426217315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26471311187170412950811543 39706966780755619426217315)
            ·
              refine ⟨59560450171133429139325973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39706966780755619426217315 59560450171133429139325973)
              ·
                refine ⟨2791896101771879490905905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 59560450171133429139325973 2791896101771879490905905)
                ·
                  refine ⟨2093922076328909618179429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2791896101771879490905905 2093922076328909618179429)
                  ·
                    refine ⟨392610389311670553408643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2093922076328909618179429 392610389311670553408643)
                    ·
                      rfl

theorem cell23_2293818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 6, 2, 4].length) (baseStart_2293818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2293818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2293818 prefixEnd_2293818 := by exact prefixLift 2293818
  have htrace : WordTrace (prefixWord ++ tailWord_2293818) baseStart_2293818 baseEnd_2293818 := by
    simpa [prefixWord, tailWord_2293818, baseEnd_2293818] using wordTrace_append hprefix tailTrace_2293818
  have hstable : (prefixWord ++ tailWord_2293818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2293818).length < 2 ^ (prefixWord ++ tailWord_2293818).sum := by decide
  have hdescent : baseEnd_2293818 < baseStart_2293818 := by decide
  rcases family_descends (prefixWord ++ tailWord_2293818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2293821 : List Nat := [1, 4, 1, 3, 1, 1, 1, 1, 3, 1, 6]
def baseStart_2293821 : Nat := 118140960795 + 2293821 * 2 ^ 59
def prefixEnd_2293821 : Nat := 4983230072969 + 3 ^ 40 * 2293821 * 2
def baseEnd_2293821 : Nat := 1177832708376975148488415

theorem tailTrace_2293821 : CollatzResearch.WordTrace tailWord_2293821 prefixEnd_2293821 1177832708376975148488415 := by
  unfold tailWord_2293821
  simp only [CollatzResearch.WordTrace]
  refine ⟨83662525022885745282825317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55775016681923830188550211 83662525022885745282825317)
  ·
    refine ⟨15686723441791077240529747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83662525022885745282825317 15686723441791077240529747)
    ·
      refine ⟨23530085162686615860794621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15686723441791077240529747 23530085162686615860794621)
      ·
        refine ⟨8823781936007480947797983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23530085162686615860794621 8823781936007480947797983)
        ·
          refine ⟨13235672904011221421696975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8823781936007480947797983 13235672904011221421696975)
          ·
            refine ⟨19853509356016832132545463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13235672904011221421696975 19853509356016832132545463)
            ·
              refine ⟨29780264034025248198818195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19853509356016832132545463 29780264034025248198818195)
              ·
                refine ⟨44670396051037872298227293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29780264034025248198818195 44670396051037872298227293)
                ·
                  refine ⟨16751398519139202111835235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44670396051037872298227293 16751398519139202111835235)
                  ·
                    refine ⟨25127097778708803167752853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16751398519139202111835235 25127097778708803167752853)
                    ·
                      refine ⟨1177832708376975148488415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25127097778708803167752853 1177832708376975148488415)
                      ·
                        rfl

theorem cell23_2293821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_2293821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2293821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2293821 prefixEnd_2293821 := by exact prefixLift 2293821
  have htrace : WordTrace (prefixWord ++ tailWord_2293821) baseStart_2293821 baseEnd_2293821 := by
    simpa [prefixWord, tailWord_2293821, baseEnd_2293821] using wordTrace_append hprefix tailTrace_2293821
  have hstable : (prefixWord ++ tailWord_2293821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2293821).length < 2 ^ (prefixWord ++ tailWord_2293821).sum := by decide
  have hdescent : baseEnd_2293821 < baseStart_2293821 := by decide
  rcases family_descends (prefixWord ++ tailWord_2293821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2293831 : List Nat := [1, 1, 4, 1, 3, 1, 4, 8]
def baseStart_2293831 : Nat := 118140960795 + 2293831 * 2 ^ 59
def prefixEnd_2293831 : Nat := 4983230072969 + 3 ^ 40 * 2293831 * 2
def baseEnd_2293831 : Nat := 43623623821611855902347

theorem tailTrace_2293831 : CollatzResearch.WordTrace tailWord_2293831 prefixEnd_2293831 43623623821611855902347 := by
  unfold tailWord_2293831
  simp only [CollatzResearch.WordTrace]
  refine ⟨83662889752849516990689347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55775259835233011327126231 83662889752849516990689347)
  ·
    refine ⟨125494334629274275486034021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83662889752849516990689347 125494334629274275486034021)
    ·
      refine ⟨23530187742988926653631379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 125494334629274275486034021 23530187742988926653631379)
      ·
        refine ⟨35295281614483389980447069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23530187742988926653631379 35295281614483389980447069)
        ·
          refine ⟨13235730605431271242667651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35295281614483389980447069 13235730605431271242667651)
          ·
            refine ⟨19853595908146906864001477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13235730605431271242667651 19853595908146906864001477)
            ·
              refine ⟨3722549232777545037000277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19853595908146906864001477 3722549232777545037000277)
              ·
                refine ⟨43623623821611855902347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3722549232777545037000277 43623623821611855902347)
                ·
                  rfl

theorem cell23_2293831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 4, 8].length) (baseStart_2293831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2293831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2293831 prefixEnd_2293831 := by exact prefixLift 2293831
  have htrace : WordTrace (prefixWord ++ tailWord_2293831) baseStart_2293831 baseEnd_2293831 := by
    simpa [prefixWord, tailWord_2293831, baseEnd_2293831] using wordTrace_append hprefix tailTrace_2293831
  have hstable : (prefixWord ++ tailWord_2293831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2293831).length < 2 ^ (prefixWord ++ tailWord_2293831).sum := by decide
  have hdescent : baseEnd_2293831 < baseStart_2293831 := by decide
  rcases family_descends (prefixWord ++ tailWord_2293831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2293842 : List Nat := [3, 2, 2, 1, 4, 2, 1, 2, 1, 1, 4]
def baseStart_2293842 : Nat := 118140960795 + 2293842 * 2 ^ 59
def prefixEnd_2293842 : Nat := 4983230072969 + 3 ^ 40 * 2293842 * 2
def baseEnd_2293842 : Nat := 1177843491470719566325819

theorem tailTrace_2293842 : CollatzResearch.WordTrace tailWord_2293842 prefixEnd_2293842 1177843491470719566325819 := by
  unfold tailWord_2293842
  simp only [CollatzResearch.WordTrace]
  refine ⟨20915822738952416467334945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55775527303873110579559853 20915822738952416467334945)
  ·
    refine ⟨15686867054214312350501209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20915822738952416467334945 15686867054214312350501209)
    ·
      refine ⟨11765150290660734262875907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15686867054214312350501209 11765150290660734262875907)
      ·
        refine ⟨17647725435991101394313861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11765150290660734262875907 17647725435991101394313861)
        ·
          refine ⟨3308948519248331511433849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17647725435991101394313861 3308948519248331511433849)
          ·
            refine ⟨2481711389436248633575387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3308948519248331511433849 2481711389436248633575387)
            ·
              refine ⟨3722567084154372950363081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2481711389436248633575387 3722567084154372950363081)
              ·
                refine ⟨2791925313115779712772311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3722567084154372950363081 2791925313115779712772311)
                ·
                  refine ⟨4187887969673669569158467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2791925313115779712772311 4187887969673669569158467)
                  ·
                    refine ⟨6281831954510504353737701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4187887969673669569158467 6281831954510504353737701)
                    ·
                      refine ⟨1177843491470719566325819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6281831954510504353737701 1177843491470719566325819)
                      ·
                        rfl

theorem cell23_2293842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 1, 2, 1, 1, 4].length) (baseStart_2293842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2293842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2293842 prefixEnd_2293842 := by exact prefixLift 2293842
  have htrace : WordTrace (prefixWord ++ tailWord_2293842) baseStart_2293842 baseEnd_2293842 := by
    simpa [prefixWord, tailWord_2293842, baseEnd_2293842] using wordTrace_append hprefix tailTrace_2293842
  have hstable : (prefixWord ++ tailWord_2293842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2293842).length < 2 ^ (prefixWord ++ tailWord_2293842).sum := by decide
  have hdescent : baseEnd_2293842 < baseStart_2293842 := by decide
  rcases family_descends (prefixWord ++ tailWord_2293842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2293845 : List Nat := [1, 3, 2, 2, 1, 3, 3, 2, 1, 2, 3]
def baseStart_2293845 : Nat := 118140960795 + 2293845 * 2 ^ 59
def prefixEnd_2293845 : Nat := 4983230072969 + 3 ^ 40 * 2293845 * 2
def baseEnd_2293845 : Nat := 1177845031912683054588305

theorem tailTrace_2293845 : CollatzResearch.WordTrace tailWord_2293845 prefixEnd_2293845 1177845031912683054588305 := by
  unfold tailWord_2293845
  simp only [CollatzResearch.WordTrace]
  refine ⟨83663400374798797381698989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55775600249865864921132659 83663400374798797381698989)
  ·
    refine ⟨31373775140549549018137121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83663400374798797381698989 31373775140549549018137121)
    ·
      refine ⟨23530331355412161763602841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31373775140549549018137121 23530331355412161763602841)
      ·
        refine ⟨17647748516559121322702131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23530331355412161763602841 17647748516559121322702131)
        ·
          refine ⟨26471622774838681984053197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17647748516559121322702131 26471622774838681984053197)
          ·
            refine ⟨9926858540564505744019949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26471622774838681984053197 9926858540564505744019949)
            ·
              refine ⟨3722571952711689654007481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9926858540564505744019949 3722571952711689654007481)
              ·
                refine ⟨2791928964533767240505611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3722571952711689654007481 2791928964533767240505611)
                ·
                  refine ⟨4187893446800650860758417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2791928964533767240505611 4187893446800650860758417)
                  ·
                    refine ⟨3140920085100488145568813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4187893446800650860758417 3140920085100488145568813)
                    ·
                      refine ⟨1177845031912683054588305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3140920085100488145568813 1177845031912683054588305)
                      ·
                        rfl

theorem cell23_2293845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 3, 2, 1, 2, 3].length) (baseStart_2293845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2293845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2293845 prefixEnd_2293845 := by exact prefixLift 2293845
  have htrace : WordTrace (prefixWord ++ tailWord_2293845) baseStart_2293845 baseEnd_2293845 := by
    simpa [prefixWord, tailWord_2293845, baseEnd_2293845] using wordTrace_append hprefix tailTrace_2293845
  have hstable : (prefixWord ++ tailWord_2293845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2293845).length < 2 ^ (prefixWord ++ tailWord_2293845).sum := by decide
  have hdescent : baseEnd_2293845 < baseStart_2293845 := by decide
  rcases family_descends (prefixWord ++ tailWord_2293845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2293878 : List Nat := [5, 1, 1, 2, 1, 2, 1, 1, 2, 7]
def baseStart_2293878 : Nat := 118140960795 + 2293878 * 2 ^ 59
def prefixEnd_2293878 : Nat := 4983230072969 + 3 ^ 40 * 2293878 * 2
def baseEnd_2293878 : Nat := 392620658924760475158551

theorem tailTrace_2293878 : CollatzResearch.WordTrace tailWord_2293878 prefixEnd_2293878 392620658924760475158551 := by
  unfold tailWord_2293878
  simp only [CollatzResearch.WordTrace]
  refine ⟨5229037748979952751103143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 55776402655786162678433525 5229037748979952751103143)
  ·
    refine ⟨7843556623469929126654715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5229037748979952751103143 7843556623469929126654715)
    ·
      refine ⟨11765334935204893689982073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7843556623469929126654715 11765334935204893689982073)
      ·
        refine ⟨8824001201403670267486555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11765334935204893689982073 8824001201403670267486555)
        ·
          refine ⟨13236001802105505401229833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8824001201403670267486555 13236001802105505401229833)
          ·
            refine ⟨9927001351579129050922375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13236001802105505401229833 9927001351579129050922375)
            ·
              refine ⟨14890502027368693576383563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9927001351579129050922375 14890502027368693576383563)
              ·
                refine ⟨22335753041053040364575345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14890502027368693576383563 22335753041053040364575345)
                ·
                  refine ⟨16751814780789780273431509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22335753041053040364575345 16751814780789780273431509)
                  ·
                    refine ⟨392620658924760475158551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16751814780789780273431509 392620658924760475158551)
                    ·
                      rfl

theorem cell23_2293878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 1, 2, 7].length) (baseStart_2293878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2293878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2293878 prefixEnd_2293878 := by exact prefixLift 2293878
  have htrace : WordTrace (prefixWord ++ tailWord_2293878) baseStart_2293878 baseEnd_2293878 := by
    simpa [prefixWord, tailWord_2293878, baseEnd_2293878] using wordTrace_append hprefix tailTrace_2293878
  have hstable : (prefixWord ++ tailWord_2293878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2293878).length < 2 ^ (prefixWord ++ tailWord_2293878).sum := by decide
  have hdescent : baseEnd_2293878 < baseStart_2293878 := by decide
  rcases family_descends (prefixWord ++ tailWord_2293878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2293885 : List Nat := [1, 4, 1, 1, 3, 2, 1, 2, 3, 3, 2]
def baseStart_2293885 : Nat := 118140960795 + 2293885 * 2 ^ 59
def prefixEnd_2293885 : Nat := 4983230072969 + 3 ^ 40 * 2293885 * 2
def baseEnd_2293885 : Nat := 1177865571138862898088121

theorem tailTrace_2293885 : CollatzResearch.WordTrace tailWord_2293885 prefixEnd_2293885 1177865571138862898088121 := by
  unfold tailWord_2293885
  simp only [CollatzResearch.WordTrace]
  refine ⟨83664859294653884213155109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55776572863102589475436739 83664859294653884213155109)
  ·
    refine ⟨15687161117747603289966583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83664859294653884213155109 15687161117747603289966583)
    ·
      refine ⟨23530741676621404934949875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15687161117747603289966583 23530741676621404934949875)
      ·
        refine ⟨35296112514932107402424813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23530741676621404934949875 35296112514932107402424813)
        ·
          refine ⟨13236042193099540275909305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35296112514932107402424813 13236042193099540275909305)
          ·
            refine ⟨9927031644824655206931979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13236042193099540275909305 9927031644824655206931979)
            ·
              refine ⟨14890547467236982810397969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9927031644824655206931979 14890547467236982810397969)
              ·
                refine ⟨11167910600427737107798477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14890547467236982810397969 11167910600427737107798477)
                ·
                  refine ⟨4187966475160401415424429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11167910600427737107798477 4187966475160401415424429)
                  ·
                    refine ⟨1570487428185150530784161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4187966475160401415424429 1570487428185150530784161)
                    ·
                      refine ⟨1177865571138862898088121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1570487428185150530784161 1177865571138862898088121)
                      ·
                        rfl

theorem cell23_2293885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 2, 3, 3, 2].length) (baseStart_2293885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2293885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2293885 prefixEnd_2293885 := by exact prefixLift 2293885
  have htrace : WordTrace (prefixWord ++ tailWord_2293885) baseStart_2293885 baseEnd_2293885 := by
    simpa [prefixWord, tailWord_2293885, baseEnd_2293885] using wordTrace_append hprefix tailTrace_2293885
  have hstable : (prefixWord ++ tailWord_2293885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2293885).length < 2 ^ (prefixWord ++ tailWord_2293885).sum := by decide
  have hdescent : baseEnd_2293885 < baseStart_2293885 := by decide
  rcases family_descends (prefixWord ++ tailWord_2293885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2293891 : List Nat := [1, 1, 1, 3, 3, 3, 1, 1, 1, 8]
def baseStart_2293891 : Nat := 118140960795 + 2293891 * 2 ^ 59
def prefixEnd_2293891 : Nat := 4983230072969 + 3 ^ 40 * 2293891 * 2
def baseEnd_2293891 : Nat := 392622884007596624871031

theorem tailTrace_2293891 : CollatzResearch.WordTrace tailWord_2293891 prefixEnd_2293891 392622884007596624871031 := by
  unfold tailWord_2293891
  simp only [CollatzResearch.WordTrace]
  refine ⟨83665078132632147237873527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55776718755088098158582351 83665078132632147237873527)
  ·
    refine ⟨125497617198948220856810291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83665078132632147237873527 125497617198948220856810291)
    ·
      refine ⟨188246425798422331285215437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125497617198948220856810291 188246425798422331285215437)
      ·
        refine ⟨70592409674408374231955789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 188246425798422331285215437 70592409674408374231955789)
        ·
          refine ⟨26472153627903140336983421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70592409674408374231955789 26472153627903140336983421)
          ·
            refine ⟨9927057610463677626368783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26472153627903140336983421 9927057610463677626368783)
            ·
              refine ⟨14890586415695516439553175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9927057610463677626368783 14890586415695516439553175)
              ·
                refine ⟨22335879623543274659329763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14890586415695516439553175 22335879623543274659329763)
                ·
                  refine ⟨33503819435314911988994645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22335879623543274659329763 33503819435314911988994645)
                  ·
                    refine ⟨392622884007596624871031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 33503819435314911988994645 392622884007596624871031)
                    ·
                      rfl

theorem cell23_2293891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 1, 1, 8].length) (baseStart_2293891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2293891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2293891 prefixEnd_2293891 := by exact prefixLift 2293891
  have htrace : WordTrace (prefixWord ++ tailWord_2293891) baseStart_2293891 baseEnd_2293891 := by
    simpa [prefixWord, tailWord_2293891, baseEnd_2293891] using wordTrace_append hprefix tailTrace_2293891
  have hstable : (prefixWord ++ tailWord_2293891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2293891).length < 2 ^ (prefixWord ++ tailWord_2293891).sum := by decide
  have hdescent : baseEnd_2293891 < baseStart_2293891 := by decide
  rcases family_descends (prefixWord ++ tailWord_2293891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2293910 : List Nat := [5, 3, 2, 1, 1, 2, 2, 1, 1, 1, 4]
def baseStart_2293910 : Nat := 118140960795 + 2293910 * 2 ^ 59
def prefixEnd_2293910 : Nat := 4983230072969 + 3 ^ 40 * 2293910 * 2
def baseEnd_2293910 : Nat := 1177878408155225300275507

theorem tailTrace_2293910 : CollatzResearch.WordTrace tailWord_2293910 prefixEnd_2293910 1177878408155225300275507 := by
  unfold tailWord_2293910
  simp only [CollatzResearch.WordTrace]
  refine ⟨5229110694972707092675949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 55777180746375542321876789 5229110694972707092675949)
  ·
    refine ⟨1960916510614765159753481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5229110694972707092675949 1960916510614765159753481)
    ·
      refine ⟨1470687382961073869815111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1960916510614765159753481 1470687382961073869815111)
      ·
        refine ⟨2206031074441610804722667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1470687382961073869815111 2206031074441610804722667)
        ·
          refine ⟨3309046611662416207084001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2206031074441610804722667 3309046611662416207084001)
          ·
            refine ⟨2481784958746812155313001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3309046611662416207084001 2481784958746812155313001)
            ·
              refine ⟨1861338719060109116484751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2481784958746812155313001 1861338719060109116484751)
              ·
                refine ⟨2792008078590163674727127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1861338719060109116484751 2792008078590163674727127)
                ·
                  refine ⟨4188012117885245512090691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2792008078590163674727127 4188012117885245512090691)
                  ·
                    refine ⟨6282018176827868268136037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4188012117885245512090691 6282018176827868268136037)
                    ·
                      refine ⟨1177878408155225300275507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6282018176827868268136037 1177878408155225300275507)
                      ·
                        rfl

theorem cell23_2293910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_2293910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2293910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2293910 prefixEnd_2293910 := by exact prefixLift 2293910
  have htrace : WordTrace (prefixWord ++ tailWord_2293910) baseStart_2293910 baseEnd_2293910 := by
    simpa [prefixWord, tailWord_2293910, baseEnd_2293910] using wordTrace_append hprefix tailTrace_2293910
  have hstable : (prefixWord ++ tailWord_2293910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2293910).length < 2 ^ (prefixWord ++ tailWord_2293910).sum := by decide
  have hdescent : baseEnd_2293910 < baseStart_2293910 := by decide
  rcases family_descends (prefixWord ++ tailWord_2293910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2293919 : List Nat := [1, 1, 2, 6, 1, 1, 4, 1, 1, 3, 2]
def baseStart_2293919 : Nat := 118140960795 + 2293919 * 2 ^ 59
def prefixEnd_2293919 : Nat := 4983230072969 + 3 ^ 40 * 2293919 * 2
def baseEnd_2293919 : Nat := 1177883029481115765062965

theorem tailTrace_2293919 : CollatzResearch.WordTrace tailWord_2293919 prefixEnd_2293919 1177883029481115765062965 := by
  unfold tailWord_2293919
  simp only [CollatzResearch.WordTrace]
  refine ⟨83666099376530708019892811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55777399584353805346595207 83666099376530708019892811)
  ·
    refine ⟨125499149064796062029839217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83666099376530708019892811 125499149064796062029839217)
    ·
      refine ⟨94124361798597046522379413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125499149064796062029839217 94124361798597046522379413)
      ·
        refine ⟨4412079459309236555736535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 94124361798597046522379413 4412079459309236555736535)
        ·
          refine ⟨6618119188963854833604803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4412079459309236555736535 6618119188963854833604803)
          ·
            refine ⟨9927178783445782250407205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6618119188963854833604803 9927178783445782250407205)
            ·
              refine ⟨1861346021896084171951351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9927178783445782250407205 1861346021896084171951351)
              ·
                refine ⟨2792019032844126257927027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1861346021896084171951351 2792019032844126257927027)
                ·
                  refine ⟨4188028549266189386890541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2792019032844126257927027 4188028549266189386890541)
                  ·
                    refine ⟨1570510705974821020083953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4188028549266189386890541 1570510705974821020083953)
                    ·
                      refine ⟨1177883029481115765062965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1570510705974821020083953 1177883029481115765062965)
                      ·
                        rfl

theorem cell23_2293919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 4, 1, 1, 3, 2].length) (baseStart_2293919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2293919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2293919 prefixEnd_2293919 := by exact prefixLift 2293919
  have htrace : WordTrace (prefixWord ++ tailWord_2293919) baseStart_2293919 baseEnd_2293919 := by
    simpa [prefixWord, tailWord_2293919, baseEnd_2293919] using wordTrace_append hprefix tailTrace_2293919
  have hstable : (prefixWord ++ tailWord_2293919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2293919).length < 2 ^ (prefixWord ++ tailWord_2293919).sum := by decide
  have hdescent : baseEnd_2293919 < baseStart_2293919 := by decide
  rcases family_descends (prefixWord ++ tailWord_2293919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2293938 : List Nat := [3, 2, 1, 1, 1, 3, 4, 1, 7]
def baseStart_2293938 : Nat := 118140960795 + 2293938 * 2 ^ 59
def prefixEnd_2293938 : Nat := 4983230072969 + 3 ^ 40 * 2293938 * 2
def baseEnd_2293938 : Nat := 130876976179283465636153

theorem tailTrace_2293938 : CollatzResearch.WordTrace tailWord_2293938 prefixEnd_2293938 130876976179283465636153 := by
  unfold tailWord_2293938
  simp only [CollatzResearch.WordTrace]
  refine ⟨20916698090865468566208617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55777861575641249509889645 20916698090865468566208617)
  ·
    refine ⟨15687523568149101424656463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20916698090865468566208617 15687523568149101424656463)
    ·
      refine ⟨23531285352223652136984695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15687523568149101424656463 23531285352223652136984695)
      ·
        refine ⟨35296928028335478205477043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23531285352223652136984695 35296928028335478205477043)
        ·
          refine ⟨52945392042503217308215565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35296928028335478205477043 52945392042503217308215565)
          ·
            refine ⟨19854522015938706490580837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52945392042503217308215565 19854522015938706490580837)
            ·
              refine ⟨3722722877988507466983907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19854522015938706490580837 3722722877988507466983907)
              ·
                refine ⟨5584084316982761200475861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3722722877988507466983907 5584084316982761200475861)
                ·
                  refine ⟨130876976179283465636153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5584084316982761200475861 130876976179283465636153)
                  ·
                    rfl

theorem cell23_2293938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 4, 1, 7].length) (baseStart_2293938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2293938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2293938 prefixEnd_2293938 := by exact prefixLift 2293938
  have htrace : WordTrace (prefixWord ++ tailWord_2293938) baseStart_2293938 baseEnd_2293938 := by
    simpa [prefixWord, tailWord_2293938, baseEnd_2293938] using wordTrace_append hprefix tailTrace_2293938
  have hstable : (prefixWord ++ tailWord_2293938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2293938).length < 2 ^ (prefixWord ++ tailWord_2293938).sum := by decide
  have hdescent : baseEnd_2293938 < baseStart_2293938 := by decide
  rcases family_descends (prefixWord ++ tailWord_2293938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2293961 : List Nat := [1, 2, 1, 1, 2, 1, 1, 3, 3, 1, 7]
def baseStart_2293961 : Nat := 118140960795 + 2293961 * 2 ^ 59
def prefixEnd_2293961 : Nat := 4983230072969 + 3 ^ 40 * 2293961 * 2
def baseEnd_2293961 : Nat := 1177904595668604600737771

theorem tailTrace_2293961 : CollatzResearch.WordTrace tailWord_2293961 prefixEnd_2293961 1177904595668604600737771 := by
  unfold tailWord_2293961
  simp only [CollatzResearch.WordTrace]
  refine ⟨83667631242378549192921737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55778420828252366128614491 83667631242378549192921737)
  ·
    refine ⟨62750723431783911894691303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83667631242378549192921737 62750723431783911894691303)
    ·
      refine ⟨94126085147675867842036955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62750723431783911894691303 94126085147675867842036955)
      ·
        refine ⟨141189127721513801763055433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94126085147675867842036955 141189127721513801763055433)
        ·
          refine ⟨105891845791135351322291575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 141189127721513801763055433 105891845791135351322291575)
          ·
            refine ⟨158837768686703026983437363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105891845791135351322291575 158837768686703026983437363)
            ·
              refine ⟨238256653030054540475156045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 158837768686703026983437363 238256653030054540475156045)
              ·
                refine ⟨89346244886270452678183517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 238256653030054540475156045 89346244886270452678183517)
                ·
                  refine ⟨33504841832351419754318819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 89346244886270452678183517 33504841832351419754318819)
                  ·
                    refine ⟨50257262748527129631478229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33504841832351419754318819 50257262748527129631478229)
                    ·
                      refine ⟨1177904595668604600737771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 50257262748527129631478229 1177904595668604600737771)
                      ·
                        rfl

theorem cell23_2293961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 3, 1, 7].length) (baseStart_2293961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2293961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2293961 prefixEnd_2293961 := by exact prefixLift 2293961
  have htrace : WordTrace (prefixWord ++ tailWord_2293961) baseStart_2293961 baseEnd_2293961 := by
    simpa [prefixWord, tailWord_2293961, baseEnd_2293961] using wordTrace_append hprefix tailTrace_2293961
  have hstable : (prefixWord ++ tailWord_2293961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2293961).length < 2 ^ (prefixWord ++ tailWord_2293961).sum := by decide
  have hdescent : baseEnd_2293961 < baseStart_2293961 := by decide
  rcases family_descends (prefixWord ++ tailWord_2293961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2294008 : List Nat := [2, 1, 2, 1, 1, 2, 1, 3, 3, 4, 3]
def baseStart_2294008 : Nat := 118140960795 + 2294008 * 2 ^ 59
def prefixEnd_2294008 : Nat := 4983230072969 + 3 ^ 40 * 2294008 * 2
def baseEnd_2294008 : Nat := 1177928729259365916850055

theorem tailTrace_2294008 : CollatzResearch.WordTrace tailWord_2294008 prefixEnd_2294008 1177928729259365916850055 := by
  unfold tailWord_2294008
  simp only [CollatzResearch.WordTrace]
  refine ⟨41834672736604138109941339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55779563648805517479921785 41834672736604138109941339)
  ·
    refine ⟨62752009104906207164912009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41834672736604138109941339 62752009104906207164912009)
    ·
      refine ⟨47064006828679655373684007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62752009104906207164912009 47064006828679655373684007)
      ·
        refine ⟨70596010243019483060526011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47064006828679655373684007 70596010243019483060526011)
        ·
          refine ⟨105894015364529224590789017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70596010243019483060526011 105894015364529224590789017)
          ·
            refine ⟨79420511523396918443091763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105894015364529224590789017 79420511523396918443091763)
            ·
              refine ⟨119130767285095377664637645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79420511523396918443091763 119130767285095377664637645)
              ·
                refine ⟨44674037731910766624239117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 119130767285095377664637645 44674037731910766624239117)
                ·
                  refine ⟨16752764149466537484089669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44674037731910766624239117 16752764149466537484089669)
                  ·
                    refine ⟨3141143278024975778266813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16752764149466537484089669 3141143278024975778266813)
                    ·
                      refine ⟨1177928729259365916850055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3141143278024975778266813 1177928729259365916850055)
                      ·
                        rfl

theorem cell23_2294008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 3, 4, 3].length) (baseStart_2294008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2294008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2294008 prefixEnd_2294008 := by exact prefixLift 2294008
  have htrace : WordTrace (prefixWord ++ tailWord_2294008) baseStart_2294008 baseEnd_2294008 := by
    simpa [prefixWord, tailWord_2294008, baseEnd_2294008] using wordTrace_append hprefix tailTrace_2294008
  have hstable : (prefixWord ++ tailWord_2294008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2294008).length < 2 ^ (prefixWord ++ tailWord_2294008).sum := by decide
  have hdescent : baseEnd_2294008 < baseStart_2294008 := by decide
  rcases family_descends (prefixWord ++ tailWord_2294008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2294025 : List Nat := [1, 2, 1, 1, 3, 4, 1, 3, 2, 2, 3]
def baseStart_2294025 : Nat := 118140960795 + 2294025 * 2 ^ 59
def prefixEnd_2294025 : Nat := 4983230072969 + 3 ^ 40 * 2294025 * 2
def baseEnd_2294025 : Nat := 1177937458430492350337477

theorem tailTrace_2294025 : CollatzResearch.WordTrace tailWord_2294025 prefixEnd_2294025 1177937458430492350337477 := by
  unfold tailWord_2294025
  simp only [CollatzResearch.WordTrace]
  refine ⟨83669965514146688123251529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55779977009431125415501019 83669965514146688123251529)
  ·
    refine ⟨62752474135610016092438647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83669965514146688123251529 62752474135610016092438647)
    ·
      refine ⟨94128711203415024138657971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62752474135610016092438647 94128711203415024138657971)
      ·
        refine ⟨141193066805122536207986957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94128711203415024138657971 141193066805122536207986957)
        ·
          refine ⟨52947400051920951077995109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 141193066805122536207986957 52947400051920951077995109)
          ·
            refine ⟨9927637509735178327124083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52947400051920951077995109 9927637509735178327124083)
            ·
              refine ⟨14891456264602767490686125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9927637509735178327124083 14891456264602767490686125)
              ·
                refine ⟨5584296099226037809007297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14891456264602767490686125 5584296099226037809007297)
                ·
                  refine ⟨4188222074419528356755473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5584296099226037809007297 4188222074419528356755473)
                  ·
                    refine ⟨3141166555814646267566605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4188222074419528356755473 3141166555814646267566605)
                    ·
                      refine ⟨1177937458430492350337477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3141166555814646267566605 1177937458430492350337477)
                      ·
                        rfl

theorem cell23_2294025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 3, 2, 2, 3].length) (baseStart_2294025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2294025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2294025 prefixEnd_2294025 := by exact prefixLift 2294025
  have htrace : WordTrace (prefixWord ++ tailWord_2294025) baseStart_2294025 baseEnd_2294025 := by
    simpa [prefixWord, tailWord_2294025, baseEnd_2294025] using wordTrace_append hprefix tailTrace_2294025
  have hstable : (prefixWord ++ tailWord_2294025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2294025).length < 2 ^ (prefixWord ++ tailWord_2294025).sum := by decide
  have hdescent : baseEnd_2294025 < baseStart_2294025 := by decide
  rcases family_descends (prefixWord ++ tailWord_2294025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2294049 : List Nat := [1, 2, 3, 2, 1, 1, 6, 2, 1, 4]
def baseStart_2294049 : Nat := 118140960795 + 2294049 * 2 ^ 59
def prefixEnd_2294049 : Nat := 4983230072969 + 3 ^ 40 * 2294049 * 2
def baseEnd_2294049 : Nat := 392649927322066752145789

theorem tailTrace_2294049 : CollatzResearch.WordTrace tailWord_2294049 prefixEnd_2294049 392649927322066752145789 := by
  unfold tailWord_2294049
  simp only [CollatzResearch.WordTrace]
  refine ⟨83670840866059740222125201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55780560577373160148083467 83670840866059740222125201)
  ·
    refine ⟨62753130649544805166593901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83670840866059740222125201 62753130649544805166593901)
    ·
      refine ⟨23532423993579301937472713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62753130649544805166593901 23532423993579301937472713)
      ·
        refine ⟨17649317995184476453104535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23532423993579301937472713 17649317995184476453104535)
        ·
          refine ⟨26473976992776714679656803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17649317995184476453104535 26473976992776714679656803)
          ·
            refine ⟨39710965489165072019485205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26473976992776714679656803 39710965489165072019485205)
            ·
              refine ⟨1861451507304612750913369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 39710965489165072019485205 1861451507304612750913369)
              ·
                refine ⟨1396088630478459563185027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1861451507304612750913369 1396088630478459563185027)
                ·
                  refine ⟨2094132945717689344777541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1396088630478459563185027 2094132945717689344777541)
                  ·
                    refine ⟨392649927322066752145789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2094132945717689344777541 392649927322066752145789)
                    ·
                      rfl

theorem cell23_2294049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 6, 2, 1, 4].length) (baseStart_2294049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2294049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2294049 prefixEnd_2294049 := by exact prefixLift 2294049
  have htrace : WordTrace (prefixWord ++ tailWord_2294049) baseStart_2294049 baseEnd_2294049 := by
    simpa [prefixWord, tailWord_2294049, baseEnd_2294049] using wordTrace_append hprefix tailTrace_2294049
  have hstable : (prefixWord ++ tailWord_2294049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2294049).length < 2 ^ (prefixWord ++ tailWord_2294049).sum := by decide
  have hdescent : baseEnd_2294049 < baseStart_2294049 := by decide
  rcases family_descends (prefixWord ++ tailWord_2294049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2294115 : List Nat := [1, 1, 1, 5, 2, 1, 3, 2, 1, 1, 5]
def baseStart_2294115 : Nat := 118140960795 + 2294115 * 2 ^ 59
def prefixEnd_2294115 : Nat := 4983230072969 + 3 ^ 40 * 2294115 * 2
def baseEnd_2294115 : Nat := 1177983671689396998212063

theorem tailTrace_2294115 : CollatzResearch.WordTrace tailWord_2294115 prefixEnd_2294115 1177983671689396998212063 := by
  unfold tailWord_2294115
  simp only [CollatzResearch.WordTrace]
  refine ⟨83673248083820633494027799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55782165389213755662685199 83673248083820633494027799)
  ·
    refine ⟨125509872125730950241041699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83673248083820633494027799 125509872125730950241041699)
    ·
      refine ⟨188264808188596425361562549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125509872125730950241041699 188264808188596425361562549)
      ·
        refine ⟨17649825767680914877646489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 188264808188596425361562549 17649825767680914877646489)
        ·
          refine ⟨13237369325760686158234867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17649825767680914877646489 13237369325760686158234867)
          ·
            refine ⟨19856053988641029237352301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13237369325760686158234867 19856053988641029237352301)
            ·
              refine ⟨7446020245740385964007113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19856053988641029237352301 7446020245740385964007113)
              ·
                refine ⟨5584515184305289473005335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7446020245740385964007113 5584515184305289473005335)
                ·
                  refine ⟨8376772776457934209508003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5584515184305289473005335 8376772776457934209508003)
                  ·
                    refine ⟨12565159164686901314262005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8376772776457934209508003 12565159164686901314262005)
                    ·
                      refine ⟨1177983671689396998212063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12565159164686901314262005 1177983671689396998212063)
                      ·
                        rfl

theorem cell23_2294115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 2, 1, 1, 5].length) (baseStart_2294115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2294115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2294115 prefixEnd_2294115 := by exact prefixLift 2294115
  have htrace : WordTrace (prefixWord ++ tailWord_2294115) baseStart_2294115 baseEnd_2294115 := by
    simpa [prefixWord, tailWord_2294115, baseEnd_2294115] using wordTrace_append hprefix tailTrace_2294115
  have hstable : (prefixWord ++ tailWord_2294115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2294115).length < 2 ^ (prefixWord ++ tailWord_2294115).sum := by decide
  have hdescent : baseEnd_2294115 < baseStart_2294115 := by decide
  rcases family_descends (prefixWord ++ tailWord_2294115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2294122 : List Nat := [3, 1, 3, 3, 1, 1, 3, 1, 1, 6]
def baseStart_2294122 : Nat := 118140960795 + 2294122 * 2 ^ 59
def prefixEnd_2294122 : Nat := 4983230072969 + 3 ^ 40 * 2294122 * 2
def baseEnd_2294122 : Nat := 392662422017992823608177

theorem tailTrace_2294122 : CollatzResearch.WordTrace tailWord_2294122 prefixEnd_2294122 392662422017992823608177 := by
  unfold tailWord_2294122
  simp only [CollatzResearch.WordTrace]
  refine ⟨20918375848698818422383155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55782335596530182459688413 20918375848698818422383155)
  ·
    refine ⟨31377563773048227633574733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20918375848698818422383155 31377563773048227633574733)
    ·
      refine ⟨11766586414893085362590525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31377563773048227633574733 11766586414893085362590525)
      ·
        refine ⟨4412469905584907010971447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11766586414893085362590525 4412469905584907010971447)
        ·
          refine ⟨6618704858377360516457171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4412469905584907010971447 6618704858377360516457171)
          ·
            refine ⟨9928057287566040774685757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6618704858377360516457171 9928057287566040774685757)
            ·
              refine ⟨3723021482837265290507159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9928057287566040774685757 3723021482837265290507159)
              ·
                refine ⟨5584532224255897935760739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3723021482837265290507159 5584532224255897935760739)
                ·
                  refine ⟨8376798336383846903641109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5584532224255897935760739 8376798336383846903641109)
                  ·
                    refine ⟨392662422017992823608177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8376798336383846903641109 392662422017992823608177)
                    ·
                      rfl

theorem cell23_2294122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 3, 1, 1, 6].length) (baseStart_2294122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2294122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2294122 prefixEnd_2294122 := by exact prefixLift 2294122
  have htrace : WordTrace (prefixWord ++ tailWord_2294122) baseStart_2294122 baseEnd_2294122 := by
    simpa [prefixWord, tailWord_2294122, baseEnd_2294122] using wordTrace_append hprefix tailTrace_2294122
  have hstable : (prefixWord ++ tailWord_2294122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2294122).length < 2 ^ (prefixWord ++ tailWord_2294122).sum := by decide
  have hdescent : baseEnd_2294122 < baseStart_2294122 := by decide
  rcases family_descends (prefixWord ++ tailWord_2294122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2294125 : List Nat := [1, 5, 1, 1, 1, 2, 3, 1, 1, 1, 6]
def baseStart_2294125 : Nat := 118140960795 + 2294125 * 2 ^ 59
def prefixEnd_2294125 : Nat := 4983230072969 + 3 ^ 40 * 2294125 * 2
def baseEnd_2294125 : Nat := 1177988806495941959087017

theorem tailTrace_2294125 : CollatzResearch.WordTrace tailWord_2294125 prefixEnd_2294125 1177988806495941959087017 := by
  unfold tailWord_2294125
  simp only [CollatzResearch.WordTrace]
  refine ⟨83673612813784405201891829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55782408542522936801261219 83673612813784405201891829)
  ·
    refine ⟨7844401201292287987677359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 83673612813784405201891829 7844401201292287987677359)
    ·
      refine ⟨11766601801938431981516039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7844401201292287987677359 11766601801938431981516039)
      ·
        refine ⟨17649902702907647972274059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11766601801938431981516039 17649902702907647972274059)
        ·
          refine ⟨26474854054361471958411089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17649902702907647972274059 26474854054361471958411089)
          ·
            refine ⟨19856140540771103968808317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26474854054361471958411089 19856140540771103968808317)
            ·
              refine ⟨7446052702789163988303119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19856140540771103968808317 7446052702789163988303119)
              ·
                refine ⟨11169079054183745982454679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7446052702789163988303119 11169079054183745982454679)
                ·
                  refine ⟨16753618581275618973682019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11169079054183745982454679 16753618581275618973682019)
                  ·
                    refine ⟨25130427871913428460523029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16753618581275618973682019 25130427871913428460523029)
                    ·
                      refine ⟨1177988806495941959087017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25130427871913428460523029 1177988806495941959087017)
                      ·
                        rfl

theorem cell23_2294125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 1, 1, 1, 6].length) (baseStart_2294125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2294125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2294125 prefixEnd_2294125 := by exact prefixLift 2294125
  have htrace : WordTrace (prefixWord ++ tailWord_2294125) baseStart_2294125 baseEnd_2294125 := by
    simpa [prefixWord, tailWord_2294125, baseEnd_2294125] using wordTrace_append hprefix tailTrace_2294125
  have hstable : (prefixWord ++ tailWord_2294125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2294125).length < 2 ^ (prefixWord ++ tailWord_2294125).sum := by decide
  have hdescent : baseEnd_2294125 < baseStart_2294125 := by decide
  rcases family_descends (prefixWord ++ tailWord_2294125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2294173 : List Nat := [1, 4, 2, 1, 5, 1, 2, 1, 2, 4]
def baseStart_2294173 : Nat := 118140960795 + 2294173 * 2 ^ 59
def prefixEnd_2294173 : Nat := 4983230072969 + 3 ^ 40 * 2294173 * 2
def baseEnd_2294173 : Nat := 392671151189119257095599

theorem tailTrace_2294173 : CollatzResearch.WordTrace tailWord_2294173 prefixEnd_2294173 392671151189119257095599 := by
  unfold tailWord_2294173
  simp only [CollatzResearch.WordTrace]
  refine ⟨83675363517610509399639173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55783575678407006266426115 83675363517610509399639173)
  ·
    refine ⟨15689130659551970512432345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83675363517610509399639173 15689130659551970512432345)
    ·
      refine ⟨11766847994663977884324259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15689130659551970512432345 11766847994663977884324259)
      ·
        refine ⟨17650271991995966826486389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11766847994663977884324259 17650271991995966826486389)
        ·
          refine ⟨1654712999249621889983099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17650271991995966826486389 1654712999249621889983099)
          ·
            refine ⟨2482069498874432834974649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1654712999249621889983099 2482069498874432834974649)
            ·
              refine ⟨1861552124155824626230987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2482069498874432834974649 1861552124155824626230987)
              ·
                refine ⟨2792328186233736939346481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1861552124155824626230987 2792328186233736939346481)
                ·
                  refine ⟨2094246139675302704509861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2792328186233736939346481 2094246139675302704509861)
                  ·
                    refine ⟨392671151189119257095599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2094246139675302704509861 392671151189119257095599)
                    ·
                      rfl

theorem cell23_2294173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 2, 1, 2, 4].length) (baseStart_2294173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2294173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2294173 prefixEnd_2294173 := by exact prefixLift 2294173
  have htrace : WordTrace (prefixWord ++ tailWord_2294173) baseStart_2294173 baseEnd_2294173 := by
    simpa [prefixWord, tailWord_2294173, baseEnd_2294173] using wordTrace_append hprefix tailTrace_2294173
  have hstable : (prefixWord ++ tailWord_2294173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2294173).length < 2 ^ (prefixWord ++ tailWord_2294173).sum := by decide
  have hdescent : baseEnd_2294173 < baseStart_2294173 := by decide
  rcases family_descends (prefixWord ++ tailWord_2294173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2294179 : List Nat := [1, 1, 1, 4, 1, 5, 1, 3, 2, 1, 3]
def baseStart_2294179 : Nat := 118140960795 + 2294179 * 2 ^ 59
def prefixEnd_2294179 : Nat := 4983230072969 + 3 ^ 40 * 2294179 * 2
def baseEnd_2294179 : Nat := 1178016534451284747811769

theorem tailTrace_2294179 : CollatzResearch.WordTrace tailWord_2294179 prefixEnd_2294179 1178016534451284747811769 := by
  unfold tailWord_2294179
  simp only [CollatzResearch.WordTrace]
  refine ⟨83675582355588772424357591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55783721570392514949571727 83675582355588772424357591)
  ·
    refine ⟨125513373533383158636536387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83675582355588772424357591 125513373533383158636536387)
    ·
      refine ⟨188270060300074737954804581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125513373533383158636536387 188270060300074737954804581)
      ·
        refine ⟨35300636306264013366525859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 188270060300074737954804581 35300636306264013366525859)
        ·
          refine ⟨52950954459396020049788789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35300636306264013366525859 52950954459396020049788789)
          ·
            refine ⟨4964151980568376879667699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 52950954459396020049788789 4964151980568376879667699)
            ·
              refine ⟨7446227970852565319501549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4964151980568376879667699 7446227970852565319501549)
              ·
                refine ⟨2792335489069711994813081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7446227970852565319501549 2792335489069711994813081)
                ·
                  refine ⟨2094251616802283996109811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2792335489069711994813081 2094251616802283996109811)
                  ·
                    refine ⟨3141377425203425994164717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2094251616802283996109811 3141377425203425994164717)
                    ·
                      refine ⟨1178016534451284747811769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3141377425203425994164717 1178016534451284747811769)
                      ·
                        rfl

theorem cell23_2294179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 3, 2, 1, 3].length) (baseStart_2294179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2294179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2294179 prefixEnd_2294179 := by exact prefixLift 2294179
  have htrace : WordTrace (prefixWord ++ tailWord_2294179) baseStart_2294179 baseEnd_2294179 := by
    simpa [prefixWord, tailWord_2294179, baseEnd_2294179] using wordTrace_append hprefix tailTrace_2294179
  have hstable : (prefixWord ++ tailWord_2294179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2294179).length < 2 ^ (prefixWord ++ tailWord_2294179).sum := by decide
  have hdescent : baseEnd_2294179 < baseStart_2294179 := by decide
  rcases family_descends (prefixWord ++ tailWord_2294179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2294265 : List Nat := [1, 2, 1, 3, 1, 2, 2, 1, 3, 2, 5]
def baseStart_2294265 : Nat := 118140960795 + 2294265 * 2 ^ 59
def prefixEnd_2294265 : Nat := 4983230072969 + 3 ^ 40 * 2294265 * 2
def baseEnd_2294265 : Nat := 1178060693787571411336373

theorem tailTrace_2294265 : CollatzResearch.WordTrace tailWord_2294265 prefixEnd_2294265 1178060693787571411336373 := by
  unfold tailWord_2294265
  simp only [CollatzResearch.WordTrace]
  refine ⟨83678719033277209111988249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55785812688851472741325499 83678719033277209111988249)
  ·
    refine ⟨62759039274957906833991187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83678719033277209111988249 62759039274957906833991187)
    ·
      refine ⟨94138558912436860250986781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62759039274957906833991187 94138558912436860250986781)
      ·
        refine ⟨35301959592163822594120043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94138558912436860250986781 35301959592163822594120043)
        ·
          refine ⟨52952939388245733891180065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35301959592163822594120043 52952939388245733891180065)
          ·
            refine ⟨39714704541184300418385049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52952939388245733891180065 39714704541184300418385049)
            ·
              refine ⟨29786028405888225313788787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39714704541184300418385049 29786028405888225313788787)
              ·
                refine ⟨44679042608832337970683181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29786028405888225313788787 44679042608832337970683181)
                ·
                  refine ⟨16754640978312126739006193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44679042608832337970683181 16754640978312126739006193)
                  ·
                    refine ⟨12565980733734095054254645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16754640978312126739006193 12565980733734095054254645)
                    ·
                      refine ⟨1178060693787571411336373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12565980733734095054254645 1178060693787571411336373)
                      ·
                        rfl

theorem cell23_2294265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 1, 3, 2, 5].length) (baseStart_2294265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2294265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2294265 prefixEnd_2294265 := by exact prefixLift 2294265
  have htrace : WordTrace (prefixWord ++ tailWord_2294265) baseStart_2294265 baseEnd_2294265 := by
    simpa [prefixWord, tailWord_2294265, baseEnd_2294265] using wordTrace_append hprefix tailTrace_2294265
  have hstable : (prefixWord ++ tailWord_2294265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2294265).length < 2 ^ (prefixWord ++ tailWord_2294265).sum := by decide
  have hdescent : baseEnd_2294265 < baseStart_2294265 := by decide
  rcases family_descends (prefixWord ++ tailWord_2294265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2294326 : List Nat := [5, 1, 2, 1, 2, 2, 1, 2, 2, 1, 4]
def baseStart_2294326 : Nat := 118140960795 + 2294326 * 2 ^ 59
def prefixEnd_2294326 : Nat := 4983230072969 + 3 ^ 40 * 2294326 * 2
def baseEnd_2294326 : Nat := 1178092016107495672673593

theorem tailTrace_2294326 : CollatzResearch.WordTrace tailWord_2294326 prefixEnd_2294326 1178092016107495672673593 := by
  unfold tailWord_2294326
  simp only [CollatzResearch.WordTrace]
  refine ⟨5230058992878513533122427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 55787295924037477686639221 5230058992878513533122427)
  ·
    refine ⟨7845088489317770299683641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5230058992878513533122427 7845088489317770299683641)
    ·
      refine ⟨5883816366988327724762731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7845088489317770299683641 5883816366988327724762731)
      ·
        refine ⟨8825724550482491587144097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5883816366988327724762731 8825724550482491587144097)
        ·
          refine ⟨6619293412861868690358073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8825724550482491587144097 6619293412861868690358073)
          ·
            refine ⟨4964470059646401517768555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6619293412861868690358073 4964470059646401517768555)
            ·
              refine ⟨7446705089469602276652833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4964470059646401517768555 7446705089469602276652833)
              ·
                refine ⟨5585028817102201707489625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7446705089469602276652833 5585028817102201707489625)
                ·
                  refine ⟨4188771612826651280617219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5585028817102201707489625 4188771612826651280617219)
                  ·
                    refine ⟨6283157419239976920925829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4188771612826651280617219 6283157419239976920925829)
                    ·
                      refine ⟨1178092016107495672673593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6283157419239976920925829 1178092016107495672673593)
                      ·
                        rfl

theorem cell23_2294326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_2294326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2294326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2294326 prefixEnd_2294326 := by exact prefixLift 2294326
  have htrace : WordTrace (prefixWord ++ tailWord_2294326) baseStart_2294326 baseEnd_2294326 := by
    simpa [prefixWord, tailWord_2294326, baseEnd_2294326] using wordTrace_append hprefix tailTrace_2294326
  have hstable : (prefixWord ++ tailWord_2294326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2294326).length < 2 ^ (prefixWord ++ tailWord_2294326).sum := by decide
  have hdescent : baseEnd_2294326 < baseStart_2294326 := by decide
  rcases family_descends (prefixWord ++ tailWord_2294326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2294329 : List Nat := [1, 2, 1, 5, 1, 1, 3, 2, 2, 2, 3]
def baseStart_2294329 : Nat := 118140960795 + 2294329 * 2 ^ 59
def prefixEnd_2294329 : Nat := 4983230072969 + 3 ^ 40 * 2294329 * 2
def baseEnd_2294329 : Nat := 1178093556549459160936079

theorem tailTrace_2294329 : CollatzResearch.WordTrace tailWord_2294329 prefixEnd_2294329 1178093556549459160936079 := by
  unfold tailWord_2294329
  simp only [CollatzResearch.WordTrace]
  refine ⟨83681053305045348042318041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55787368870030232028212027 83681053305045348042318041)
  ·
    refine ⟨62760789978784011031738531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83681053305045348042318041 62760789978784011031738531)
    ·
      refine ⟨94141184968176016547607797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62760789978784011031738531 94141184968176016547607797)
      ·
        refine ⟨8825736090766501551338231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 94141184968176016547607797 8825736090766501551338231)
        ·
          refine ⟨13238604136149752327007347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8825736090766501551338231 13238604136149752327007347)
          ·
            refine ⟨19857906204224628490511021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13238604136149752327007347 19857906204224628490511021)
            ·
              refine ⟨7446714826584235683941633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19857906204224628490511021 7446714826584235683941633)
              ·
                refine ⟨5585036119938176762956225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7446714826584235683941633 5585036119938176762956225)
                ·
                  refine ⟨4188777089953632572217169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5585036119938176762956225 4188777089953632572217169)
                  ·
                    refine ⟨3141582817465224429162877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4188777089953632572217169 3141582817465224429162877)
                    ·
                      refine ⟨1178093556549459160936079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3141582817465224429162877 1178093556549459160936079)
                      ·
                        rfl

theorem cell23_2294329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 2, 2, 2, 3].length) (baseStart_2294329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2294329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2294329 prefixEnd_2294329 := by exact prefixLift 2294329
  have htrace : WordTrace (prefixWord ++ tailWord_2294329) baseStart_2294329 baseEnd_2294329 := by
    simpa [prefixWord, tailWord_2294329, baseEnd_2294329] using wordTrace_append hprefix tailTrace_2294329
  have hstable : (prefixWord ++ tailWord_2294329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2294329).length < 2 ^ (prefixWord ++ tailWord_2294329).sum := by decide
  have hdescent : baseEnd_2294329 < baseStart_2294329 := by decide
  rcases family_descends (prefixWord ++ tailWord_2294329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2294332 : List Nat := [2, 2, 2, 2, 3, 1, 2, 1, 8]
def baseStart_2294332 : Nat := 118140960795 + 2294332 * 2 ^ 59
def prefixEnd_2294332 : Nat := 4983230072969 + 3 ^ 40 * 2294332 * 2
def baseEnd_2294332 : Nat := 130899455221269183244285

theorem tailTrace_2294332 : CollatzResearch.WordTrace tailWord_2294332 prefixEnd_2294332 130899455221269183244285 := by
  unfold tailWord_2294332
  simp only [CollatzResearch.WordTrace]
  refine ⟨41840581362017239777338625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55787441816022986369784833 41840581362017239777338625)
  ·
    refine ⟨31380436021512929833003969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41840581362017239777338625 31380436021512929833003969)
    ·
      refine ⟨23535327016134697374752977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31380436021512929833003969 23535327016134697374752977)
      ·
        refine ⟨17651495262101023031064733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23535327016134697374752977 17651495262101023031064733)
        ·
          refine ⟨6619310723287883636649275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17651495262101023031064733 6619310723287883636649275)
          ·
            refine ⟨9928966084931825454973913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6619310723287883636649275 9928966084931825454973913)
            ·
              refine ⟨7446724563698869091230435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9928966084931825454973913 7446724563698869091230435)
              ·
                refine ⟨11170086845548303636845653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7446724563698869091230435 11170086845548303636845653)
                ·
                  refine ⟨130899455221269183244285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11170086845548303636845653 130899455221269183244285)
                  ·
                    rfl

theorem cell23_2294332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 1, 8].length) (baseStart_2294332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2294332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2294332 prefixEnd_2294332 := by exact prefixLift 2294332
  have htrace : WordTrace (prefixWord ++ tailWord_2294332) baseStart_2294332 baseEnd_2294332 := by
    simpa [prefixWord, tailWord_2294332, baseEnd_2294332] using wordTrace_append hprefix tailTrace_2294332
  have hstable : (prefixWord ++ tailWord_2294332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2294332).length < 2 ^ (prefixWord ++ tailWord_2294332).sum := by decide
  have hdescent : baseEnd_2294332 < baseStart_2294332 := by decide
  rcases family_descends (prefixWord ++ tailWord_2294332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2294345 : List Nat := [1, 2, 1, 1, 2, 2, 1, 1, 1, 11]
def baseStart_2294345 : Nat := 118140960795 + 2294345 * 2 ^ 59
def prefixEnd_2294345 : Nat := 4983230072969 + 3 ^ 40 * 2294345 * 2
def baseEnd_2294345 : Nat := 392700590746643699445335

theorem tailTrace_2294345 : CollatzResearch.WordTrace tailWord_2294345 prefixEnd_2294345 392700590746643699445335 := by
  unfold tailWord_2294345
  simp only [CollatzResearch.WordTrace]
  refine ⟨83681636872987382774900489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55787757915324921849933659 83681636872987382774900489)
  ·
    refine ⟨62761227654740537081175367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83681636872987382774900489 62761227654740537081175367)
    ·
      refine ⟨94141841482110805621763051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62761227654740537081175367 94141841482110805621763051)
      ·
        refine ⟨141212762223166208432644577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94141841482110805621763051 141212762223166208432644577)
        ·
          refine ⟨105909571667374656324483433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 141212762223166208432644577 105909571667374656324483433)
          ·
            refine ⟨79432178750530992243362575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105909571667374656324483433 79432178750530992243362575)
            ·
              refine ⟨119148268125796488365043863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79432178750530992243362575 119148268125796488365043863)
              ·
                refine ⟨178722402188694732547565795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 119148268125796488365043863 178722402188694732547565795)
                ·
                  refine ⟨268083603283042098821348693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 178722402188694732547565795 268083603283042098821348693)
                  ·
                    refine ⟨392700590746643699445335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 268083603283042098821348693 392700590746643699445335)
                    ·
                      rfl

theorem cell23_2294345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 11].length) (baseStart_2294345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2294345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2294345 prefixEnd_2294345 := by exact prefixLift 2294345
  have htrace : WordTrace (prefixWord ++ tailWord_2294345) baseStart_2294345 baseEnd_2294345 := by
    simpa [prefixWord, tailWord_2294345, baseEnd_2294345] using wordTrace_append hprefix tailTrace_2294345
  have hstable : (prefixWord ++ tailWord_2294345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2294345).length < 2 ^ (prefixWord ++ tailWord_2294345).sum := by decide
  have hdescent : baseEnd_2294345 < baseStart_2294345 := by decide
  rcases family_descends (prefixWord ++ tailWord_2294345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2294359 : List Nat := [1, 1, 3, 2, 2, 2, 2, 1, 5, 1, 3]
def baseStart_2294359 : Nat := 118140960795 + 2294359 * 2 ^ 59
def prefixEnd_2294359 : Nat := 4983230072969 + 3 ^ 40 * 2294359 * 2
def baseEnd_2294359 : Nat := 1178108960969094043560941

theorem tailTrace_2294359 : CollatzResearch.WordTrace tailWord_2294359 prefixEnd_2294359 1178108960969094043560941 := by
  unfold tailWord_2294359
  simp only [CollatzResearch.WordTrace]
  refine ⟨83682147494936663165910131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55788098329957775443940087 83682147494936663165910131)
  ·
    refine ⟨125523221242404994748865197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83682147494936663165910131 125523221242404994748865197)
    ·
      refine ⟨47071207965901873030824449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 125523221242404994748865197 47071207965901873030824449)
      ·
        refine ⟨35303405974426404773118337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47071207965901873030824449 35303405974426404773118337)
        ·
          refine ⟨26477554480819803579838753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35303405974426404773118337 26477554480819803579838753)
          ·
            refine ⟨19858165860614852684879065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26477554480819803579838753 19858165860614852684879065)
            ·
              refine ⟨14893624395461139513659299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19858165860614852684879065 14893624395461139513659299)
              ·
                refine ⟨22340436593191709270488949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14893624395461139513659299 22340436593191709270488949)
                ·
                  refine ⟨2094415930611722744108339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22340436593191709270488949 2094415930611722744108339)
                  ·
                    refine ⟨3141623895917584116162509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2094415930611722744108339 3141623895917584116162509)
                    ·
                      refine ⟨1178108960969094043560941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3141623895917584116162509 1178108960969094043560941)
                      ·
                        rfl

theorem cell23_2294359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 1, 5, 1, 3].length) (baseStart_2294359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2294359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2294359 prefixEnd_2294359 := by exact prefixLift 2294359
  have htrace : WordTrace (prefixWord ++ tailWord_2294359) baseStart_2294359 baseEnd_2294359 := by
    simpa [prefixWord, tailWord_2294359, baseEnd_2294359] using wordTrace_append hprefix tailTrace_2294359
  have hstable : (prefixWord ++ tailWord_2294359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2294359).length < 2 ^ (prefixWord ++ tailWord_2294359).sum := by decide
  have hdescent : baseEnd_2294359 < baseStart_2294359 := by decide
  rcases family_descends (prefixWord ++ tailWord_2294359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2294393 : List Nat := [1, 2, 1, 3, 3, 3, 1, 4, 1, 1, 3]
def baseStart_2294393 : Nat := 118140960795 + 2294393 * 2 ^ 59
def prefixEnd_2294393 : Nat := 4983230072969 + 3 ^ 40 * 2294393 * 2
def baseEnd_2294393 : Nat := 1178126419311346910535785

theorem tailTrace_2294393 : CollatzResearch.WordTrace tailWord_2294393 prefixEnd_2294393 1178126419311346910535785 := by
  unfold tailWord_2294393
  simp only [CollatzResearch.WordTrace]
  refine ⟨83683387576813486972647833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55788925051208991315098555 83683387576813486972647833)
  ·
    refine ⟨62762540682610115229485875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83683387576813486972647833 62762540682610115229485875)
    ·
      refine ⟨94143811023915172844228813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62762540682610115229485875 94143811023915172844228813)
      ·
        refine ⟨35303929133968189816585805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94143811023915172844228813 35303929133968189816585805)
        ·
          refine ⟨13238973425238071181219677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35303929133968189816585805 13238973425238071181219677)
          ·
            refine ⟨4964615034464276692957379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13238973425238071181219677 4964615034464276692957379)
            ·
              refine ⟨7446922551696415039436069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4964615034464276692957379 7446922551696415039436069)
              ·
                refine ⟨1396297978443077819894263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7446922551696415039436069 1396297978443077819894263)
                ·
                  refine ⟨2094446967664616729841395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1396297978443077819894263 2094446967664616729841395)
                  ·
                    refine ⟨3141670451496925094762093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2094446967664616729841395 3141670451496925094762093)
                    ·
                      refine ⟨1178126419311346910535785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3141670451496925094762093 1178126419311346910535785)
                      ·
                        rfl

theorem cell23_2294393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 4, 1, 1, 3].length) (baseStart_2294393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2294393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2294393 prefixEnd_2294393 := by exact prefixLift 2294393
  have htrace : WordTrace (prefixWord ++ tailWord_2294393) baseStart_2294393 baseEnd_2294393 := by
    simpa [prefixWord, tailWord_2294393, baseEnd_2294393] using wordTrace_append hprefix tailTrace_2294393
  have hstable : (prefixWord ++ tailWord_2294393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2294393).length < 2 ^ (prefixWord ++ tailWord_2294393).sum := by decide
  have hdescent : baseEnd_2294393 < baseStart_2294393 := by decide
  rcases family_descends (prefixWord ++ tailWord_2294393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2294420 : List Nat := [2, 4, 2, 2, 1, 3, 1, 1, 2, 3, 2]
def baseStart_2294420 : Nat := 118140960795 + 2294420 * 2 ^ 59
def prefixEnd_2294420 : Nat := 4983230072969 + 3 ^ 40 * 2294420 * 2
def baseEnd_2294420 : Nat := 1178140283289018304898161

theorem tailTrace_2294420 : CollatzResearch.WordTrace tailWord_2294420 prefixEnd_2294420 1178140283289018304898161 := by
  unfold tailWord_2294420
  simp only [CollatzResearch.WordTrace]
  refine ⟨41842186173857835291940357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55789581565143780389253809 41842186173857835291940357)
  ·
    refine ⟨7845409907598344117238817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41842186173857835291940357 7845409907598344117238817)
    ·
      refine ⟨5884057430698758087929113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7845409907598344117238817 5884057430698758087929113)
      ·
        refine ⟨4413043073024068565946835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5884057430698758087929113 4413043073024068565946835)
        ·
          refine ⟨6619564609536102848920253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4413043073024068565946835 6619564609536102848920253)
          ·
            refine ⟨2482336728576038568345095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6619564609536102848920253 2482336728576038568345095)
            ·
              refine ⟨3723505092864057852517643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2482336728576038568345095 3723505092864057852517643)
              ·
                refine ⟨5585257639296086778776465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3723505092864057852517643 5585257639296086778776465)
                ·
                  refine ⟨4188943229472065084082349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5585257639296086778776465 4188943229472065084082349)
                  ·
                    refine ⟨1570853711052024406530881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4188943229472065084082349 1570853711052024406530881)
                    ·
                      refine ⟨1178140283289018304898161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1570853711052024406530881 1178140283289018304898161)
                      ·
                        rfl

theorem cell23_2294420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 1, 1, 2, 3, 2].length) (baseStart_2294420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2294420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2294420 prefixEnd_2294420 := by exact prefixLift 2294420
  have htrace : WordTrace (prefixWord ++ tailWord_2294420) baseStart_2294420 baseEnd_2294420 := by
    simpa [prefixWord, tailWord_2294420, baseEnd_2294420] using wordTrace_append hprefix tailTrace_2294420
  have hstable : (prefixWord ++ tailWord_2294420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2294420).length < 2 ^ (prefixWord ++ tailWord_2294420).sum := by decide
  have hdescent : baseEnd_2294420 < baseStart_2294420 := by decide
  rcases family_descends (prefixWord ++ tailWord_2294420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2294429 : List Nat := [1, 4, 2, 1, 1, 1, 4, 2, 1, 2, 4]
def baseStart_2294429 : Nat := 118140960795 + 2294429 * 2 ^ 59
def prefixEnd_2294429 : Nat := 4983230072969 + 3 ^ 40 * 2294429 * 2
def baseEnd_2294429 : Nat := 1178144904614908769685619

theorem tailTrace_2294429 : CollatzResearch.WordTrace tailWord_2294429 prefixEnd_2294429 1178144904614908769685619 := by
  unfold tailWord_2294429
  simp only [CollatzResearch.WordTrace]
  refine ⟨83684700604683065120958341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55789800403122043413972227 83684700604683065120958341)
  ·
    refine ⟨15690881363378074710179689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83684700604683065120958341 15690881363378074710179689)
    ·
      refine ⟨11768161022533556032634767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15690881363378074710179689 11768161022533556032634767)
      ·
        refine ⟨17652241533800334048952151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11768161022533556032634767 17652241533800334048952151)
        ·
          refine ⟨26478362300700501073428227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17652241533800334048952151 26478362300700501073428227)
          ·
            refine ⟨39717543451050751610142341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26478362300700501073428227 39717543451050751610142341)
            ·
              refine ⟨7447039397072015926901689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39717543451050751610142341 7447039397072015926901689)
              ·
                refine ⟨5585279547804011945176267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7447039397072015926901689 5585279547804011945176267)
                ·
                  refine ⟨8377919321706017917764401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5585279547804011945176267 8377919321706017917764401)
                  ·
                    refine ⟨6283439491279513438323301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8377919321706017917764401 6283439491279513438323301)
                    ·
                      refine ⟨1178144904614908769685619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6283439491279513438323301 1178144904614908769685619)
                      ·
                        rfl

theorem cell23_2294429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 2, 1, 2, 4].length) (baseStart_2294429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2294429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2294429 prefixEnd_2294429 := by exact prefixLift 2294429
  have htrace : WordTrace (prefixWord ++ tailWord_2294429) baseStart_2294429 baseEnd_2294429 := by
    simpa [prefixWord, tailWord_2294429, baseEnd_2294429] using wordTrace_append hprefix tailTrace_2294429
  have hstable : (prefixWord ++ tailWord_2294429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2294429).length < 2 ^ (prefixWord ++ tailWord_2294429).sum := by decide
  have hdescent : baseEnd_2294429 < baseStart_2294429 := by decide
  rcases family_descends (prefixWord ++ tailWord_2294429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2294436 : List Nat := [2, 3, 1, 2, 2, 1, 3, 3, 1, 2, 3]
def baseStart_2294436 : Nat := 118140960795 + 2294436 * 2 ^ 59
def prefixEnd_2294436 : Nat := 4983230072969 + 3 ^ 40 * 2294436 * 2
def baseEnd_2294436 : Nat := 1178148498979490242298087

theorem tailTrace_2294436 : CollatzResearch.WordTrace tailWord_2294436 prefixEnd_2294436 1178148498979490242298087 := by
  unfold tailWord_2294436
  simp only [CollatzResearch.WordTrace]
  refine ⟨41842477957828852658231581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55789970610438470210975441 41842477957828852658231581)
  ·
    refine ⟨15690929234185819746836843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41842477957828852658231581 15690929234185819746836843)
    ·
      refine ⟨23536393851278729620255265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15690929234185819746836843 23536393851278729620255265)
      ·
        refine ⟨17652295388459047215191449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23536393851278729620255265 17652295388459047215191449)
        ·
          refine ⟨13239221541344285411393587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17652295388459047215191449 13239221541344285411393587)
          ·
            refine ⟨19858832312016428117090381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13239221541344285411393587 19858832312016428117090381)
            ·
              refine ⟨7447062117006160543908893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19858832312016428117090381 7447062117006160543908893)
              ·
                refine ⟨2792648293877310203965835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7447062117006160543908893 2792648293877310203965835)
                ·
                  refine ⟨4188972440815965305948753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2792648293877310203965835 4188972440815965305948753)
                  ·
                    refine ⟨3141729330611973979461565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4188972440815965305948753 3141729330611973979461565)
                    ·
                      refine ⟨1178148498979490242298087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3141729330611973979461565 1178148498979490242298087)
                      ·
                        rfl

theorem cell23_2294436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 3, 1, 2, 3].length) (baseStart_2294436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2294436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2294436 prefixEnd_2294436 := by exact prefixLift 2294436
  have htrace : WordTrace (prefixWord ++ tailWord_2294436) baseStart_2294436 baseEnd_2294436 := by
    simpa [prefixWord, tailWord_2294436, baseEnd_2294436] using wordTrace_append hprefix tailTrace_2294436
  have hstable : (prefixWord ++ tailWord_2294436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2294436).length < 2 ^ (prefixWord ++ tailWord_2294436).sum := by decide
  have hdescent : baseEnd_2294436 < baseStart_2294436 := by decide
  rcases family_descends (prefixWord ++ tailWord_2294436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2294484 : List Nat := [2, 4, 1, 3, 2, 2, 1, 3, 1, 2, 2]
def baseStart_2294484 : Nat := 118140960795 + 2294484 * 2 ^ 59
def prefixEnd_2294484 : Nat := 4983230072969 + 3 ^ 40 * 2294484 * 2
def baseEnd_2294484 : Nat := 1178173146050906054497867

theorem tailTrace_2294484 : CollatzResearch.WordTrace tailWord_2294484 prefixEnd_2294484 1178173146050906054497867 := by
  unfold tailWord_2294484
  simp only [CollatzResearch.WordTrace]
  refine ⟨41843353309741904757105253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55791137746322539676140337 41843353309741904757105253)
  ·
    refine ⟨7845628745576607141957235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41843353309741904757105253 7845628745576607141957235)
    ·
      refine ⟨11768443118364910712935853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7845628745576607141957235 11768443118364910712935853)
      ·
        refine ⟨4413166169386841517350945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11768443118364910712935853 4413166169386841517350945)
        ·
          refine ⟨3309874627040131138013209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4413166169386841517350945 3309874627040131138013209)
          ·
            refine ⟨2482405970280098353509907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3309874627040131138013209 2482405970280098353509907)
            ·
              refine ⟨3723608955420147530264861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2482405970280098353509907 3723608955420147530264861)
              ·
                refine ⟨1396353358282555323849323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3723608955420147530264861 1396353358282555323849323)
                ·
                  refine ⟨2094530037423832985773985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1396353358282555323849323 2094530037423832985773985)
                  ·
                    refine ⟨1570897528067874739330489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2094530037423832985773985 1570897528067874739330489)
                    ·
                      refine ⟨1178173146050906054497867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1570897528067874739330489 1178173146050906054497867)
                      ·
                        rfl

theorem cell23_2294484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 1, 3, 1, 2, 2].length) (baseStart_2294484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2294484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2294484 prefixEnd_2294484 := by exact prefixLift 2294484
  have htrace : WordTrace (prefixWord ++ tailWord_2294484) baseStart_2294484 baseEnd_2294484 := by
    simpa [prefixWord, tailWord_2294484, baseEnd_2294484] using wordTrace_append hprefix tailTrace_2294484
  have hstable : (prefixWord ++ tailWord_2294484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2294484).length < 2 ^ (prefixWord ++ tailWord_2294484).sum := by decide
  have hdescent : baseEnd_2294484 < baseStart_2294484 := by decide
  rcases family_descends (prefixWord ++ tailWord_2294484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2294509 : List Nat := [1, 5, 1, 2, 1, 1, 1, 2, 1, 3, 5]
def baseStart_2294509 : Nat := 118140960795 + 2294509 * 2 ^ 59
def prefixEnd_2294509 : Nat := 4983230072969 + 3 ^ 40 * 2294509 * 2
def baseEnd_2294509 : Nat := 1178185983067268456685251

theorem tailTrace_2294509 : CollatzResearch.WordTrace tailWord_2294509 prefixEnd_2294509 1178185983067268456685251 := by
  unfold tailWord_2294509
  simp only [CollatzResearch.WordTrace]
  refine ⟨83687618444393238783870581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55791745629595492522580387 83687618444393238783870581)
  ·
    refine ⟨7845714229161866135987867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 83687618444393238783870581 7845714229161866135987867)
    ·
      refine ⟨11768571343742799203981801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7845714229161866135987867 11768571343742799203981801)
      ·
        refine ⟨8826428507807099402986351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11768571343742799203981801 8826428507807099402986351)
        ·
          refine ⟨13239642761710649104479527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8826428507807099402986351 13239642761710649104479527)
          ·
            refine ⟨19859464142565973656719291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13239642761710649104479527 19859464142565973656719291)
            ·
              refine ⟨29789196213848960485078937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19859464142565973656719291 29789196213848960485078937)
              ·
                refine ⟨22341897160386720363809203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29789196213848960485078937 22341897160386720363809203)
                ·
                  refine ⟨33512845740580080545713805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22341897160386720363809203 33512845740580080545713805)
                  ·
                    refine ⟨12567317152717530204642677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33512845740580080545713805 12567317152717530204642677)
                    ·
                      refine ⟨1178185983067268456685251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12567317152717530204642677 1178185983067268456685251)
                      ·
                        rfl

theorem cell23_2294509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_2294509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2294509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2294509 prefixEnd_2294509 := by exact prefixLift 2294509
  have htrace : WordTrace (prefixWord ++ tailWord_2294509) baseStart_2294509 baseEnd_2294509 := by
    simpa [prefixWord, tailWord_2294509, baseEnd_2294509] using wordTrace_append hprefix tailTrace_2294509
  have hstable : (prefixWord ++ tailWord_2294509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2294509).length < 2 ^ (prefixWord ++ tailWord_2294509).sum := by decide
  have hdescent : baseEnd_2294509 < baseStart_2294509 := by decide
  rcases family_descends (prefixWord ++ tailWord_2294509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2294526 : List Nat := [4, 2, 2, 1, 2, 1, 1, 2, 2, 1, 5]
def baseStart_2294526 : Nat := 118140960795 + 2294526 * 2 ^ 59
def prefixEnd_2294526 : Nat := 4983230072969 + 3 ^ 40 * 2294526 * 2
def baseEnd_2294526 : Nat := 1178194712238394890172673

theorem tailTrace_2294526 : CollatzResearch.WordTrace tailWord_2294526 prefixEnd_2294526 1178194712238394890172673 := by
  unfold tailWord_2294526
  simp only [CollatzResearch.WordTrace]
  refine ⟨10461029810666456335904929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55792158990221100458159621 10461029810666456335904929)
  ·
    refine ⟨7845772357999842251928697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10461029810666456335904929 7845772357999842251928697)
    ·
      refine ⟨5884329268499881688946523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7845772357999842251928697 5884329268499881688946523)
      ·
        refine ⟨8826493902749822533419785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5884329268499881688946523 8826493902749822533419785)
        ·
          refine ⟨6619870427062366900064839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8826493902749822533419785 6619870427062366900064839)
          ·
            refine ⟨9929805640593550350097259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6619870427062366900064839 9929805640593550350097259)
            ·
              refine ⟨14894708460890325525145889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9929805640593550350097259 14894708460890325525145889)
              ·
                refine ⟨11171031345667744143859417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14894708460890325525145889 11171031345667744143859417)
                ·
                  refine ⟨8378273509250808107894563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11171031345667744143859417 8378273509250808107894563)
                  ·
                    refine ⟨12567410263876212161841845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8378273509250808107894563 12567410263876212161841845)
                    ·
                      refine ⟨1178194712238394890172673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12567410263876212161841845 1178194712238394890172673)
                      ·
                        rfl

theorem cell23_2294526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_2294526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2294526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2294526 prefixEnd_2294526 := by exact prefixLift 2294526
  have htrace : WordTrace (prefixWord ++ tailWord_2294526) baseStart_2294526 baseEnd_2294526 := by
    simpa [prefixWord, tailWord_2294526, baseEnd_2294526] using wordTrace_append hprefix tailTrace_2294526
  have hstable : (prefixWord ++ tailWord_2294526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2294526).length < 2 ^ (prefixWord ++ tailWord_2294526).sum := by decide
  have hdescent : baseEnd_2294526 < baseStart_2294526 := by decide
  rcases family_descends (prefixWord ++ tailWord_2294526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2294539 : List Nat := [1, 1, 1, 1, 5, 1, 1, 2, 4, 3, 3]
def baseStart_2294539 : Nat := 118140960795 + 2294539 * 2 ^ 59
def prefixEnd_2294539 : Nat := 4983230072969 + 3 ^ 40 * 2294539 * 2
def baseEnd_2294539 : Nat := 1178201387486903339310113

theorem tailTrace_2294539 : CollatzResearch.WordTrace tailWord_2294539 prefixEnd_2294539 1178201387486903339310113 := by
  unfold tailWord_2294539
  simp only [CollatzResearch.WordTrace]
  refine ⟨83688712634284553907462671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55792475089523035938308447 83688712634284553907462671)
  ·
    refine ⟨125533068951426830861194007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83688712634284553907462671 125533068951426830861194007)
    ·
      refine ⟨188299603427140246291791011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125533068951426830861194007 188299603427140246291791011)
      ·
        refine ⟨282449405140710369437686517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188299603427140246291791011 282449405140710369437686517)
        ·
          refine ⟨26479631731941597134783111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 282449405140710369437686517 26479631731941597134783111)
          ·
            refine ⟨39719447597912395702174667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26479631731941597134783111 39719447597912395702174667)
            ·
              refine ⟨59579171396868593553262001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39719447597912395702174667 59579171396868593553262001)
              ·
                refine ⟨44684378547651445164946501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59579171396868593553262001 44684378547651445164946501)
                ·
                  refine ⟨8378320977684645968427469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44684378547651445164946501 8378320977684645968427469)
                  ·
                    refine ⟨3141870366631742238160301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8378320977684645968427469 3141870366631742238160301)
                    ·
                      refine ⟨1178201387486903339310113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3141870366631742238160301 1178201387486903339310113)
                      ·
                        rfl

theorem cell23_2294539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 2, 4, 3, 3].length) (baseStart_2294539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2294539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2294539 prefixEnd_2294539 := by exact prefixLift 2294539
  have htrace : WordTrace (prefixWord ++ tailWord_2294539) baseStart_2294539 baseEnd_2294539 := by
    simpa [prefixWord, tailWord_2294539, baseEnd_2294539] using wordTrace_append hprefix tailTrace_2294539
  have hstable : (prefixWord ++ tailWord_2294539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2294539).length < 2 ^ (prefixWord ++ tailWord_2294539).sum := by decide
  have hdescent : baseEnd_2294539 < baseStart_2294539 := by decide
  rcases family_descends (prefixWord ++ tailWord_2294539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2294593 : List Nat := [1, 2, 5, 3, 1, 1, 1, 1, 1, 7]
def baseStart_2294593 : Nat := 118140960795 + 2294593 * 2 ^ 59
def prefixEnd_2294593 : Nat := 4983230072969 + 3 ^ 40 * 2294593 * 2
def baseEnd_2294593 : Nat := 392743038480748709344955

theorem tailTrace_2294593 : CollatzResearch.WordTrace tailWord_2294593 prefixEnd_2294593 392743038480748709344955 := by
  unfold tailWord_2294593
  simp only [CollatzResearch.WordTrace]
  refine ⟨83690682176088921129928433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55793788117392614086618955 83690682176088921129928433)
  ·
    refine ⟨62768011632066690847446325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83690682176088921129928433 62768011632066690847446325)
    ·
      refine ⟨5884501090506252266948093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 62768011632066690847446325 5884501090506252266948093)
      ·
        refine ⟨2206687908939844600105535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5884501090506252266948093 2206687908939844600105535)
        ·
          refine ⟨3310031863409766900158303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2206687908939844600105535 3310031863409766900158303)
          ·
            refine ⟨4965047795114650350237455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3310031863409766900158303 4965047795114650350237455)
            ·
              refine ⟨7447571692671975525356183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4965047795114650350237455 7447571692671975525356183)
              ·
                refine ⟨11171357539007963288034275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7447571692671975525356183 11171357539007963288034275)
                ·
                  refine ⟨16757036308511944932051413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11171357539007963288034275 16757036308511944932051413)
                  ·
                    refine ⟨392743038480748709344955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16757036308511944932051413 392743038480748709344955)
                    ·
                      rfl

theorem cell23_2294593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 1, 1, 7].length) (baseStart_2294593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2294593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2294593 prefixEnd_2294593 := by exact prefixLift 2294593
  have htrace : WordTrace (prefixWord ++ tailWord_2294593) baseStart_2294593 baseEnd_2294593 := by
    simpa [prefixWord, tailWord_2294593, baseEnd_2294593] using wordTrace_append hprefix tailTrace_2294593
  have hstable : (prefixWord ++ tailWord_2294593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2294593).length < 2 ^ (prefixWord ++ tailWord_2294593).sum := by decide
  have hdescent : baseEnd_2294593 < baseStart_2294593 := by decide
  rcases family_descends (prefixWord ++ tailWord_2294593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2294616 : List Nat := [2, 1, 2, 2, 1, 1, 1, 6, 2, 2, 3]
def baseStart_2294616 : Nat := 118140960795 + 2294616 * 2 ^ 59
def prefixEnd_2294616 : Nat := 4983230072969 + 3 ^ 40 * 2294616 * 2
def baseEnd_2294616 : Nat := 1178240925497299538047259

theorem tailTrace_2294616 : CollatzResearch.WordTrace tailWord_2294616 prefixEnd_2294616 1178240925497299538047259 := by
  unfold tailWord_2294616
  simp only [CollatzResearch.WordTrace]
  refine ⟨41845760527502798029007851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55794347370003730705343801 41845760527502798029007851)
  ·
    refine ⟨62768640791254197043511777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41845760527502798029007851 62768640791254197043511777)
    ·
      refine ⟨47076480593440647782633833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62768640791254197043511777 47076480593440647782633833)
      ·
        refine ⟨35307360445080485836975375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47076480593440647782633833 35307360445080485836975375)
        ·
          refine ⟨52961040667620728755463063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35307360445080485836975375 52961040667620728755463063)
          ·
            refine ⟨79441561001431093133194595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52961040667620728755463063 79441561001431093133194595)
            ·
              refine ⟨119162341502146639699791893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79441561001431093133194595 119162341502146639699791893)
              ·
                refine ⟨5585734757913123735927745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 119162341502146639699791893 5585734757913123735927745)
                ·
                  refine ⟨4189301068434842801945809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5585734757913123735927745 4189301068434842801945809)
                  ·
                    refine ⟨3141975801326132101459357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4189301068434842801945809 3141975801326132101459357)
                    ·
                      refine ⟨1178240925497299538047259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3141975801326132101459357 1178240925497299538047259)
                      ·
                        rfl

theorem cell23_2294616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 6, 2, 2, 3].length) (baseStart_2294616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2294616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2294616 prefixEnd_2294616 := by exact prefixLift 2294616
  have htrace : WordTrace (prefixWord ++ tailWord_2294616) baseStart_2294616 baseEnd_2294616 := by
    simpa [prefixWord, tailWord_2294616, baseEnd_2294616] using wordTrace_append hprefix tailTrace_2294616
  have hstable : (prefixWord ++ tailWord_2294616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2294616).length < 2 ^ (prefixWord ++ tailWord_2294616).sum := by decide
  have hdescent : baseEnd_2294616 < baseStart_2294616 := by decide
  rcases family_descends (prefixWord ++ tailWord_2294616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2294623 : List Nat := [1, 1, 2, 3, 1, 3, 1, 6, 1, 4]
def baseStart_2294623 : Nat := 118140960795 + 2294623 * 2 ^ 59
def prefixEnd_2294623 : Nat := 4983230072969 + 3 ^ 40 * 2294623 * 2
def baseEnd_2294623 : Nat := 392748173287293670219909

theorem tailTrace_2294623 : CollatzResearch.WordTrace tailWord_2294623 prefixEnd_2294623 392748173287293670219909 := by
  unfold tailWord_2294623
  simp only [CollatzResearch.WordTrace]
  refine ⟨83691776365980236253520523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55794517577320157502347015 83691776365980236253520523)
  ·
    refine ⟨125537664548970354380280785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83691776365980236253520523 125537664548970354380280785)
    ·
      refine ⟨94153248411727765785210589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125537664548970354380280785 94153248411727765785210589)
      ·
        refine ⟨35307468154397912169453971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94153248411727765785210589 35307468154397912169453971)
        ·
          refine ⟨52961202231596868254180957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35307468154397912169453971 52961202231596868254180957)
          ·
            refine ⟨19860450836848825595317859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52961202231596868254180957 19860450836848825595317859)
            ·
              refine ⟨29790676255273238392976789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19860450836848825595317859 29790676255273238392976789)
              ·
                refine ⟨1396437949465933049670787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 29790676255273238392976789 1396437949465933049670787)
                ·
                  refine ⟨2094656924198899574506181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1396437949465933049670787 2094656924198899574506181)
                  ·
                    refine ⟨392748173287293670219909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2094656924198899574506181 392748173287293670219909)
                    ·
                      rfl

theorem cell23_2294623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 6, 1, 4].length) (baseStart_2294623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2294623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2294623 prefixEnd_2294623 := by exact prefixLift 2294623
  have htrace : WordTrace (prefixWord ++ tailWord_2294623) baseStart_2294623 baseEnd_2294623 := by
    simpa [prefixWord, tailWord_2294623, baseEnd_2294623] using wordTrace_append hprefix tailTrace_2294623
  have hstable : (prefixWord ++ tailWord_2294623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2294623).length < 2 ^ (prefixWord ++ tailWord_2294623).sum := by decide
  have hdescent : baseEnd_2294623 < baseStart_2294623 := by decide
  rcases family_descends (prefixWord ++ tailWord_2294623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2294674 : List Nat := [3, 2, 3, 2, 2, 1, 3, 2, 1, 4]
def baseStart_2294674 : Nat := 118140960795 + 2294674 * 2 ^ 59
def prefixEnd_2294674 : Nat := 4983230072969 + 3 ^ 40 * 2294674 * 2
def baseEnd_2294674 : Nat := 392756902458420103707331

theorem tailTrace_2294674 : CollatzResearch.WordTrace tailWord_2294674 prefixEnd_2294674 392756902458420103707331 := by
  unfold tailWord_2294674
  simp only [CollatzResearch.WordTrace]
  refine ⟨20923409122198867990906769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55795757659196981309084717 20923409122198867990906769)
  ·
    refine ⟨15692556841649150993180077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20923409122198867990906769 15692556841649150993180077)
    ·
      refine ⟨5884708815618431622442529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15692556841649150993180077 5884708815618431622442529)
      ·
        refine ⟨4413531611713823716831897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5884708815618431622442529 4413531611713823716831897)
        ·
          refine ⟨3310148708785367787623923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4413531611713823716831897 3310148708785367787623923)
          ·
            refine ⟨4965223063178051681435885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3310148708785367787623923 4965223063178051681435885)
            ·
              refine ⟨1861958648691769380538457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4965223063178051681435885 1861958648691769380538457)
              ·
                refine ⟨1396468986518827035403843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1861958648691769380538457 1396468986518827035403843)
                ·
                  refine ⟨2094703479778240553105765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1396468986518827035403843 2094703479778240553105765)
                  ·
                    refine ⟨392756902458420103707331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2094703479778240553105765 392756902458420103707331)
                    ·
                      rfl

theorem cell23_2294674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 3, 2, 1, 4].length) (baseStart_2294674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2294674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2294674 prefixEnd_2294674 := by exact prefixLift 2294674
  have htrace : WordTrace (prefixWord ++ tailWord_2294674) baseStart_2294674 baseEnd_2294674 := by
    simpa [prefixWord, tailWord_2294674, baseEnd_2294674] using wordTrace_append hprefix tailTrace_2294674
  have hstable : (prefixWord ++ tailWord_2294674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2294674).length < 2 ^ (prefixWord ++ tailWord_2294674).sum := by decide
  have hdescent : baseEnd_2294674 < baseStart_2294674 := by decide
  rcases family_descends (prefixWord ++ tailWord_2294674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2294720 : List Nat := [2, 1, 1, 2, 3, 4, 3, 1, 1, 1, 4]
def baseStart_2294720 : Nat := 118140960795 + 2294720 * 2 ^ 59
def prefixEnd_2294720 : Nat := 4983230072969 + 3 ^ 40 * 2294720 * 2
def baseEnd_2294720 : Nat := 1178294327485367131146781

theorem tailTrace_2294720 : CollatzResearch.WordTrace tailWord_2294720 prefixEnd_2294720 1178294327485367131146781 := by
  unfold tailWord_2294720
  simp only [CollatzResearch.WordTrace]
  refine ⟨41847657123314410909900807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55796876164419214546534409 41847657123314410909900807)
  ·
    refine ⟨62771485684971616364851211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41847657123314410909900807 62771485684971616364851211)
    ·
      refine ⟨94157228527457424547276817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62771485684971616364851211 94157228527457424547276817)
      ·
        refine ⟨70617921395593068410457613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94157228527457424547276817 70617921395593068410457613)
        ·
          refine ⟨26481720523347400653921605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70617921395593068410457613 26481720523347400653921605)
          ·
            refine ⟨4965322598127637622610301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26481720523347400653921605 4965322598127637622610301)
            ·
              refine ⟨1861995974297864108478863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4965322598127637622610301 1861995974297864108478863)
              ·
                refine ⟨2792993961446796162718295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1861995974297864108478863 2792993961446796162718295)
                ·
                  refine ⟨4189490942170194244077443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2792993961446796162718295 4189490942170194244077443)
                  ·
                    refine ⟨6284236413255291366116165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4189490942170194244077443 6284236413255291366116165)
                    ·
                      refine ⟨1178294327485367131146781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6284236413255291366116165 1178294327485367131146781)
                      ·
                        rfl

theorem cell23_2294720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 3, 1, 1, 1, 4].length) (baseStart_2294720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2294720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2294720 prefixEnd_2294720 := by exact prefixLift 2294720
  have htrace : WordTrace (prefixWord ++ tailWord_2294720) baseStart_2294720 baseEnd_2294720 := by
    simpa [prefixWord, tailWord_2294720, baseEnd_2294720] using wordTrace_append hprefix tailTrace_2294720
  have hstable : (prefixWord ++ tailWord_2294720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2294720).length < 2 ^ (prefixWord ++ tailWord_2294720).sum := by decide
  have hdescent : baseEnd_2294720 < baseStart_2294720 := by decide
  rcases family_descends (prefixWord ++ tailWord_2294720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2294736 : List Nat := [2, 1, 1, 1, 1, 2, 3, 1, 5, 3, 3]
def baseStart_2294736 : Nat := 118140960795 + 2294736 * 2 ^ 59
def prefixEnd_2294736 : Nat := 4983230072969 + 3 ^ 40 * 2294736 * 2
def baseEnd_2294736 : Nat := 1178302543175839068546707

theorem tailTrace_2294736 : CollatzResearch.WordTrace tailWord_2294736 prefixEnd_2294736 1178302543175839068546707 := by
  unfold tailWord_2294736
  simp only [CollatzResearch.WordTrace]
  refine ⟨41847948907285428276192031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55797265209713904368256041 41847948907285428276192031)
  ·
    refine ⟨62771923360928142414288047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41847948907285428276192031 62771923360928142414288047)
    ·
      refine ⟨94157885041392213621432071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62771923360928142414288047 94157885041392213621432071)
      ·
        refine ⟨141236827562088320432148107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94157885041392213621432071 141236827562088320432148107)
        ·
          refine ⟨211855241343132480648222161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141236827562088320432148107 211855241343132480648222161)
          ·
            refine ⟨158891431007349360486166621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 211855241343132480648222161 158891431007349360486166621)
            ·
              refine ⟨59584286627756010182312483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 158891431007349360486166621 59584286627756010182312483)
              ·
                refine ⟨89376429941634015273468725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59584286627756010182312483 89376429941634015273468725)
                ·
                  refine ⟨8379040307028188931887693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 89376429941634015273468725 8379040307028188931887693)
                  ·
                    refine ⟨3142140115135570849457885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8379040307028188931887693 3142140115135570849457885)
                    ·
                      refine ⟨1178302543175839068546707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3142140115135570849457885 1178302543175839068546707)
                      ·
                        rfl

theorem cell23_2294736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 5, 3, 3].length) (baseStart_2294736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2294736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2294736 prefixEnd_2294736 := by exact prefixLift 2294736
  have htrace : WordTrace (prefixWord ++ tailWord_2294736) baseStart_2294736 baseEnd_2294736 := by
    simpa [prefixWord, tailWord_2294736, baseEnd_2294736] using wordTrace_append hprefix tailTrace_2294736
  have hstable : (prefixWord ++ tailWord_2294736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2294736).length < 2 ^ (prefixWord ++ tailWord_2294736).sum := by decide
  have hdescent : baseEnd_2294736 < baseStart_2294736 := by decide
  rcases family_descends (prefixWord ++ tailWord_2294736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2294737 : List Nat := [1, 2, 2, 1, 2, 1, 5, 4, 1, 2, 2]
def baseStart_2294737 : Nat := 118140960795 + 2294737 * 2 ^ 59
def prefixEnd_2294737 : Nat := 4983230072969 + 3 ^ 40 * 2294737 * 2
def baseEnd_2294737 : Nat := 1178303056656493564634203

theorem tailTrace_2294737 : CollatzResearch.WordTrace tailWord_2294737 prefixEnd_2294737 1178303056656493564634203 := by
  unfold tailWord_2294737
  simp only [CollatzResearch.WordTrace]
  refine ⟨83695934287567233723170465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55797289525044822482113643 83695934287567233723170465)
  ·
    refine ⟨62771950715675425292377849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83695934287567233723170465 62771950715675425292377849)
    ·
      refine ⟨47078963036756568969283387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62771950715675425292377849 47078963036756568969283387)
      ·
        refine ⟨70618444555134853453925081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47078963036756568969283387 70618444555134853453925081)
        ·
          refine ⟨52963833416351140090443811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70618444555134853453925081 52963833416351140090443811)
          ·
            refine ⟨79445750124526710135665717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52963833416351140090443811 79445750124526710135665717)
            ·
              refine ⟨7448039074174379075218661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 79445750124526710135665717 7448039074174379075218661)
              ·
                refine ⟨1396507326407696076603499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7448039074174379075218661 1396507326407696076603499)
                ·
                  refine ⟨2094760989611544114905249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1396507326407696076603499 2094760989611544114905249)
                  ·
                    refine ⟨1571070742208658086178937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2094760989611544114905249 1571070742208658086178937)
                    ·
                      refine ⟨1178303056656493564634203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1571070742208658086178937 1178303056656493564634203)
                      ·
                        rfl

theorem cell23_2294737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 4, 1, 2, 2].length) (baseStart_2294737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2294737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2294737 prefixEnd_2294737 := by exact prefixLift 2294737
  have htrace : WordTrace (prefixWord ++ tailWord_2294737) baseStart_2294737 baseEnd_2294737 := by
    simpa [prefixWord, tailWord_2294737, baseEnd_2294737] using wordTrace_append hprefix tailTrace_2294737
  have hstable : (prefixWord ++ tailWord_2294737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2294737).length < 2 ^ (prefixWord ++ tailWord_2294737).sum := by decide
  have hdescent : baseEnd_2294737 < baseStart_2294737 := by decide
  rcases family_descends (prefixWord ++ tailWord_2294737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2294753 : List Nat := [1, 2, 3, 1, 2, 1, 1, 2, 6, 1, 3]
def baseStart_2294753 : Nat := 118140960795 + 2294753 * 2 ^ 59
def prefixEnd_2294753 : Nat := 4983230072969 + 3 ^ 40 * 2294753 * 2
def baseEnd_2294753 : Nat := 1178311272346965502034129

theorem tailTrace_2294753 : CollatzResearch.WordTrace tailWord_2294753 prefixEnd_2294753 1178311272346965502034129 := by
  unfold tailWord_2294753
  simp only [CollatzResearch.WordTrace]
  refine ⟨83696517855509268455752913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55797678570339512303835275 83696517855509268455752913)
  ·
    refine ⟨62772388391631951341814685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83696517855509268455752913 62772388391631951341814685)
    ·
      refine ⟨23539645646861981753180507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62772388391631951341814685 23539645646861981753180507)
      ·
        refine ⟨35309468470292972629770761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23539645646861981753180507 35309468470292972629770761)
        ·
          refine ⟨26482101352719729472328071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35309468470292972629770761 26482101352719729472328071)
          ·
            refine ⟨39723152029079594208492107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26482101352719729472328071 39723152029079594208492107)
            ·
              refine ⟨59584728043619391312738161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39723152029079594208492107 59584728043619391312738161)
              ·
                refine ⟨44688546032714543484553621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59584728043619391312738161 44688546032714543484553621)
                ·
                  refine ⟨2094775595283494225838451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 44688546032714543484553621 2094775595283494225838451)
                  ·
                    refine ⟨3142163392925241338757677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2094775595283494225838451 3142163392925241338757677)
                    ·
                      refine ⟨1178311272346965502034129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3142163392925241338757677 1178311272346965502034129)
                      ·
                        rfl

theorem cell23_2294753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 2, 6, 1, 3].length) (baseStart_2294753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2294753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2294753 prefixEnd_2294753 := by exact prefixLift 2294753
  have htrace : WordTrace (prefixWord ++ tailWord_2294753) baseStart_2294753 baseEnd_2294753 := by
    simpa [prefixWord, tailWord_2294753, baseEnd_2294753] using wordTrace_append hprefix tailTrace_2294753
  have hstable : (prefixWord ++ tailWord_2294753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2294753).length < 2 ^ (prefixWord ++ tailWord_2294753).sum := by decide
  have hdescent : baseEnd_2294753 < baseStart_2294753 := by decide
  rcases family_descends (prefixWord ++ tailWord_2294753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2294754 : List Nat := [3, 3, 3, 1, 1, 2, 1, 2, 3, 2, 2]
def baseStart_2294754 : Nat := 118140960795 + 2294754 * 2 ^ 59
def prefixEnd_2294754 : Nat := 4983230072969 + 3 ^ 40 * 2294754 * 2
def baseEnd_2294754 : Nat := 1178311785827619998121625

theorem tailTrace_2294754 : CollatzResearch.WordTrace tailWord_2294754 prefixEnd_2294754 1178311785827619998121625 := by
  unfold tailWord_2294754
  simp only [CollatzResearch.WordTrace]
  refine ⟨20924138582126411406634829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55797702885670430417692877 20924138582126411406634829)
  ·
    refine ⟨7846551968297404277488061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20924138582126411406634829 7846551968297404277488061)
    ·
      refine ⟨2942456988111526604058023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7846551968297404277488061 2942456988111526604058023)
      ·
        refine ⟨4413685482167289906087035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2942456988111526604058023 4413685482167289906087035)
        ·
          refine ⟨6620528223250934859130553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4413685482167289906087035 6620528223250934859130553)
          ·
            refine ⟨4965396167438201144347915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6620528223250934859130553 4965396167438201144347915)
            ·
              refine ⟨7448094251157301716521873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4965396167438201144347915 7448094251157301716521873)
              ·
                refine ⟨5586070688367976287391405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7448094251157301716521873 5586070688367976287391405)
                ·
                  refine ⟨2094776508137991107771777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5586070688367976287391405 2094776508137991107771777)
                  ·
                    refine ⟨1571082381103493330828833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2094776508137991107771777 1571082381103493330828833)
                    ·
                      refine ⟨1178311785827619998121625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1571082381103493330828833 1178311785827619998121625)
                      ·
                        rfl

theorem cell23_2294754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 2, 3, 2, 2].length) (baseStart_2294754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2294754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2294754 prefixEnd_2294754 := by exact prefixLift 2294754
  have htrace : WordTrace (prefixWord ++ tailWord_2294754) baseStart_2294754 baseEnd_2294754 := by
    simpa [prefixWord, tailWord_2294754, baseEnd_2294754] using wordTrace_append hprefix tailTrace_2294754
  have hstable : (prefixWord ++ tailWord_2294754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2294754).length < 2 ^ (prefixWord ++ tailWord_2294754).sum := by decide
  have hdescent : baseEnd_2294754 < baseStart_2294754 := by decide
  rcases family_descends (prefixWord ++ tailWord_2294754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2294774 : List Nat := [5, 1, 1, 1, 3, 3, 2, 1, 1, 2, 3]
def baseStart_2294774 : Nat := 118140960795 + 2294774 * 2 ^ 59
def prefixEnd_2294774 : Nat := 4983230072969 + 3 ^ 40 * 2294774 * 2
def baseEnd_2294774 : Nat := 1178322055440709919871533

theorem tailTrace_2294774 : CollatzResearch.WordTrace tailWord_2294774 prefixEnd_2294774 1178322055440709919871533 := by
  unfold tailWord_2294774
  simp only [CollatzResearch.WordTrace]
  refine ⟨5231080236777074315141711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 55798189192288792694844917 5231080236777074315141711)
  ·
    refine ⟨7846620355165611472712567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5231080236777074315141711 7846620355165611472712567)
    ·
      refine ⟨11769930532748417209068851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7846620355165611472712567 11769930532748417209068851)
      ·
        refine ⟨17654895799122625813603277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11769930532748417209068851 17654895799122625813603277)
        ·
          refine ⟨6620585924670984680101229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17654895799122625813603277 6620585924670984680101229)
          ·
            refine ⟨2482719721751619255037961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6620585924670984680101229 2482719721751619255037961)
            ·
              refine ⟨1862039791313714441278471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2482719721751619255037961 1862039791313714441278471)
              ·
                refine ⟨2793059686970571661917707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1862039791313714441278471 2793059686970571661917707)
                ·
                  refine ⟨4189589530455857492876561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2793059686970571661917707 4189589530455857492876561)
                  ·
                    refine ⟨3142192147841893119657421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4189589530455857492876561 3142192147841893119657421)
                    ·
                      refine ⟨1178322055440709919871533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3142192147841893119657421 1178322055440709919871533)
                      ·
                        rfl

theorem cell23_2294774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 2, 1, 1, 2, 3].length) (baseStart_2294774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2294774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2294774 prefixEnd_2294774 := by exact prefixLift 2294774
  have htrace : WordTrace (prefixWord ++ tailWord_2294774) baseStart_2294774 baseEnd_2294774 := by
    simpa [prefixWord, tailWord_2294774, baseEnd_2294774] using wordTrace_append hprefix tailTrace_2294774
  have hstable : (prefixWord ++ tailWord_2294774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2294774).length < 2 ^ (prefixWord ++ tailWord_2294774).sum := by decide
  have hdescent : baseEnd_2294774 < baseStart_2294774 := by decide
  rcases family_descends (prefixWord ++ tailWord_2294774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2294793 : List Nat := [1, 2, 1, 1, 3, 1, 1, 4, 3, 4, 2]
def baseStart_2294793 : Nat := 118140960795 + 2294793 * 2 ^ 59
def prefixEnd_2294793 : Nat := 4983230072969 + 3 ^ 40 * 2294793 * 2
def baseEnd_2294793 : Nat := 1178331811573145345533945

theorem tailTrace_2294793 : CollatzResearch.WordTrace tailWord_2294793 prefixEnd_2294793 1178331811573145345533945 := by
  unfold tailWord_2294793
  simp only [CollatzResearch.WordTrace]
  refine ⟨83697976775364355287209033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55798651183576236858139355 83697976775364355287209033)
  ·
    refine ⟨62773482581523266465406775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83697976775364355287209033 62773482581523266465406775)
    ·
      refine ⟨94160223872284899698110163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62773482581523266465406775 94160223872284899698110163)
      ·
        refine ⟨141240335808427349547165245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94160223872284899698110163 141240335808427349547165245)
        ·
          refine ⟨52965125928160256080186967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 141240335808427349547165245 52965125928160256080186967)
          ·
            refine ⟨79447688892240384120280451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52965125928160256080186967 79447688892240384120280451)
            ·
              refine ⟨119171533338360576180420677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79447688892240384120280451 119171533338360576180420677)
              ·
                refine ⟨22344662500942608033828877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 119171533338360576180420677 22344662500942608033828877)
                ·
                  refine ⟨8379248437853478012685829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22344662500942608033828877 8379248437853478012685829)
                  ·
                    refine ⟨1571109082097527127378593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8379248437853478012685829 1571109082097527127378593)
                    ·
                      refine ⟨1178331811573145345533945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1571109082097527127378593 1178331811573145345533945)
                      ·
                        rfl

theorem cell23_2294793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 4, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 4, 3, 4, 2].length) (baseStart_2294793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2294793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2294793 prefixEnd_2294793 := by exact prefixLift 2294793
  have htrace : WordTrace (prefixWord ++ tailWord_2294793) baseStart_2294793 baseEnd_2294793 := by
    simpa [prefixWord, tailWord_2294793, baseEnd_2294793] using wordTrace_append hprefix tailTrace_2294793
  have hstable : (prefixWord ++ tailWord_2294793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2294793).length < 2 ^ (prefixWord ++ tailWord_2294793).sum := by decide
  have hdescent : baseEnd_2294793 < baseStart_2294793 := by decide
  rcases family_descends (prefixWord ++ tailWord_2294793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2294861 : List Nat := [1, 6, 1, 1, 1, 2, 4, 1, 2, 2, 2]
def baseStart_2294861 : Nat := 118140960795 + 2294861 * 2 ^ 59
def prefixEnd_2294861 : Nat := 4983230072969 + 3 ^ 40 * 2294861 * 2
def baseEnd_2294861 : Nat := 1178366728257651079483633

theorem tailTrace_2294861 : CollatzResearch.WordTrace tailWord_2294861 prefixEnd_2294861 1178366728257651079483633 := by
  unfold tailWord_2294861
  simp only [CollatzResearch.WordTrace]
  refine ⟨83700456939118002900684437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55800304626078668600456291 83700456939118002900684437)
  ·
    refine ⟨3923458919021156385969583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 83700456939118002900684437 3923458919021156385969583)
    ·
      refine ⟨5885188378531734578954375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3923458919021156385969583 5885188378531734578954375)
      ·
        refine ⟨8827782567797601868431563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5885188378531734578954375 8827782567797601868431563)
        ·
          refine ⟨13241673851696402802647345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8827782567797601868431563 13241673851696402802647345)
          ·
            refine ⟨9931255388772302101985509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13241673851696402802647345 9931255388772302101985509)
            ·
              refine ⟨1862110385394806644122283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9931255388772302101985509 1862110385394806644122283)
              ·
                refine ⟨2793165578092209966183425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1862110385394806644122283 2793165578092209966183425)
                ·
                  refine ⟨2094874183569157474637569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2793165578092209966183425 2094874183569157474637569)
                  ·
                    refine ⟨1571155637676868105978177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2094874183569157474637569 1571155637676868105978177)
                    ·
                      refine ⟨1178366728257651079483633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1571155637676868105978177 1178366728257651079483633)
                      ·
                        rfl

theorem cell23_2294861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 4, 1, 2, 2, 2].length) (baseStart_2294861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2294861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2294861 prefixEnd_2294861 := by exact prefixLift 2294861
  have htrace : WordTrace (prefixWord ++ tailWord_2294861) baseStart_2294861 baseEnd_2294861 := by
    simpa [prefixWord, tailWord_2294861, baseEnd_2294861] using wordTrace_append hprefix tailTrace_2294861
  have hstable : (prefixWord ++ tailWord_2294861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2294861).length < 2 ^ (prefixWord ++ tailWord_2294861).sum := by decide
  have hdescent : baseEnd_2294861 < baseStart_2294861 := by decide
  rcases family_descends (prefixWord ++ tailWord_2294861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2294901 : List Nat := [1, 3, 4, 3, 1, 2, 2, 2, 5]
def baseStart_2294901 : Nat := 118140960795 + 2294901 * 2 ^ 59
def prefixEnd_2294901 : Nat := 4983230072969 + 3 ^ 40 * 2294901 * 2
def baseEnd_2294901 : Nat := 130931918609314546998161

theorem tailTrace_2294901 : CollatzResearch.WordTrace tailWord_2294901 prefixEnd_2294901 130931918609314546998161 := by
  unfold tailWord_2294901
  simp only [CollatzResearch.WordTrace]
  refine ⟨83701915858973089732140557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55801277239315393154760371 83701915858973089732140557)
  ·
    refine ⟨31388218447114908649552709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83701915858973089732140557 31388218447114908649552709)
    ·
      refine ⟨5885290958834045371791133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31388218447114908649552709 5885290958834045371791133)
      ·
        refine ⟨2206984109562767014421675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5885290958834045371791133 2206984109562767014421675)
        ·
          refine ⟨3310476164344150521632513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2206984109562767014421675 3310476164344150521632513)
          ·
            refine ⟨2482857123258112891224385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3310476164344150521632513 2482857123258112891224385)
            ·
              refine ⟨1862142842443584668418289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2482857123258112891224385 1862142842443584668418289)
              ·
                refine ⟨1396607131832688501313717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1862142842443584668418289 1396607131832688501313717)
                ·
                  refine ⟨130931918609314546998161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1396607131832688501313717 130931918609314546998161)
                  ·
                    rfl

theorem cell23_2294901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 2, 2, 5].length) (baseStart_2294901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2294901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2294901 prefixEnd_2294901 := by exact prefixLift 2294901
  have htrace : WordTrace (prefixWord ++ tailWord_2294901) baseStart_2294901 baseEnd_2294901 := by
    simpa [prefixWord, tailWord_2294901, baseEnd_2294901] using wordTrace_append hprefix tailTrace_2294901
  have hstable : (prefixWord ++ tailWord_2294901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2294901).length < 2 ^ (prefixWord ++ tailWord_2294901).sum := by decide
  have hdescent : baseEnd_2294901 < baseStart_2294901 := by decide
  rcases family_descends (prefixWord ++ tailWord_2294901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2294917 : List Nat := [1, 3, 1, 1, 6, 1, 1, 1, 2, 4, 2]
def baseStart_2294917 : Nat := 118140960795 + 2294917 * 2 ^ 59
def prefixEnd_2294917 : Nat := 4983230072969 + 3 ^ 40 * 2294917 * 2
def baseEnd_2294917 : Nat := 1178395483174302860383375

theorem tailTrace_2294917 : CollatzResearch.WordTrace tailWord_2294917 prefixEnd_2294917 1178395483174302860383375 := by
  unfold tailWord_2294917
  simp only [CollatzResearch.WordTrace]
  refine ⟨83702499426915124464723005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55801666284610082976482003 83702499426915124464723005)
  ·
    refine ⟨31388437285093171674271127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83702499426915124464723005 31388437285093171674271127)
    ·
      refine ⟨47082655927639757511406691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31388437285093171674271127 47082655927639757511406691)
      ·
        refine ⟨70623983891459636267110037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47082655927639757511406691 70623983891459636267110037)
        ·
          refine ⟨3310499244912170450020783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 70623983891459636267110037 3310499244912170450020783)
          ·
            refine ⟨4965748867368255675031175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3310499244912170450020783 4965748867368255675031175)
            ·
              refine ⟨7448623301052383512546763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4965748867368255675031175 7448623301052383512546763)
              ·
                refine ⟨11172934951578575268820145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7448623301052383512546763 11172934951578575268820145)
                ·
                  refine ⟨8379701213683931451615109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11172934951578575268820145 8379701213683931451615109)
                  ·
                    refine ⟨1571193977565737147177833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8379701213683931451615109 1571193977565737147177833)
                    ·
                      refine ⟨1178395483174302860383375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1571193977565737147177833 1178395483174302860383375)
                      ·
                        rfl

theorem cell23_2294917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 1, 2, 4, 2].length) (baseStart_2294917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2294917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2294917 prefixEnd_2294917 := by exact prefixLift 2294917
  have htrace : WordTrace (prefixWord ++ tailWord_2294917) baseStart_2294917 baseEnd_2294917 := by
    simpa [prefixWord, tailWord_2294917, baseEnd_2294917] using wordTrace_append hprefix tailTrace_2294917
  have hstable : (prefixWord ++ tailWord_2294917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2294917).length < 2 ^ (prefixWord ++ tailWord_2294917).sum := by decide
  have hdescent : baseEnd_2294917 < baseStart_2294917 := by decide
  rcases family_descends (prefixWord ++ tailWord_2294917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2294933 : List Nat := [1, 3, 2, 1, 1, 1, 2, 1, 1, 7, 3]
def baseStart_2294933 : Nat := 118140960795 + 2294933 * 2 ^ 59
def prefixEnd_2294933 : Nat := 4983230072969 + 3 ^ 40 * 2294933 * 2
def baseEnd_2294933 : Nat := 1178403698864774797783301

theorem tailTrace_2294933 : CollatzResearch.WordTrace tailWord_2294933 prefixEnd_2294933 1178403698864774797783301 := by
  unfold tailWord_2294933
  simp only [CollatzResearch.WordTrace]
  refine ⟨83703082994857159197305453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55802055329904772798203635 83703082994857159197305453)
  ·
    refine ⟨31388656123071434698989545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83703082994857159197305453 31388656123071434698989545)
    ·
      refine ⟨23541492092303576024242159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31388656123071434698989545 23541492092303576024242159)
      ·
        refine ⟨35312238138455364036363239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23541492092303576024242159 35312238138455364036363239)
        ·
          refine ⟨52968357207683046054544859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35312238138455364036363239 52968357207683046054544859)
          ·
            refine ⟨79452535811524569081817289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52968357207683046054544859 79452535811524569081817289)
            ·
              refine ⟨59589401858643426811362967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79452535811524569081817289 59589401858643426811362967)
              ·
                refine ⟨89384102787965140217044451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59589401858643426811362967 89384102787965140217044451)
                ·
                  refine ⟨134076154181947710325566677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 89384102787965140217044451 134076154181947710325566677)
                  ·
                    refine ⟨3142409863639399460755469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 134076154181947710325566677 3142409863639399460755469)
                    ·
                      refine ⟨1178403698864774797783301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3142409863639399460755469 1178403698864774797783301)
                      ·
                        rfl

theorem cell23_2294933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 7, 3].length) (baseStart_2294933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2294933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2294933 prefixEnd_2294933 := by exact prefixLift 2294933
  have htrace : WordTrace (prefixWord ++ tailWord_2294933) baseStart_2294933 baseEnd_2294933 := by
    simpa [prefixWord, tailWord_2294933, baseEnd_2294933] using wordTrace_append hprefix tailTrace_2294933
  have hstable : (prefixWord ++ tailWord_2294933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2294933).length < 2 ^ (prefixWord ++ tailWord_2294933).sum := by decide
  have hdescent : baseEnd_2294933 < baseStart_2294933 := by decide
  rcases family_descends (prefixWord ++ tailWord_2294933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2294967 : List Nat := [1, 1, 3, 1, 4, 1, 4, 1, 3, 1, 3]
def baseStart_2294967 : Nat := 118140960795 + 2294967 * 2 ^ 59
def prefixEnd_2294967 : Nat := 4983230072969 + 3 ^ 40 * 2294967 * 2
def baseEnd_2294967 : Nat := 1178421157207027664758145

theorem tailTrace_2294967 : CollatzResearch.WordTrace tailWord_2294967 prefixEnd_2294967 1178421157207027664758145 := by
  unfold tailWord_2294967
  simp only [CollatzResearch.WordTrace]
  refine ⟨83704323076733983004043155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55802882051155988669362103 83704323076733983004043155)
  ·
    refine ⟨125556484615100974506064733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83704323076733983004043155 125556484615100974506064733)
    ·
      refine ⟨47083681730662865439774275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 125556484615100974506064733 47083681730662865439774275)
      ·
        refine ⟨70625522595994298159661413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47083681730662865439774275 70625522595994298159661413)
        ·
          refine ⟨13242285486748930904936515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 70625522595994298159661413 13242285486748930904936515)
          ·
            refine ⟨19863428230123396357404773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13242285486748930904936515 19863428230123396357404773)
            ·
              refine ⟨3724392793148136817013395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19863428230123396357404773 3724392793148136817013395)
              ·
                refine ⟨5586589189722205225520093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3724392793148136817013395 5586589189722205225520093)
                ·
                  refine ⟨2094970946145826959570035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5586589189722205225520093 2094970946145826959570035)
                  ·
                    refine ⟨3142456419218740439355053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2094970946145826959570035 3142456419218740439355053)
                    ·
                      refine ⟨1178421157207027664758145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3142456419218740439355053 1178421157207027664758145)
                      ·
                        rfl

theorem cell23_2294967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 4, 1, 3, 1, 3].length) (baseStart_2294967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2294967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2294967 prefixEnd_2294967 := by exact prefixLift 2294967
  have htrace : WordTrace (prefixWord ++ tailWord_2294967) baseStart_2294967 baseEnd_2294967 := by
    simpa [prefixWord, tailWord_2294967, baseEnd_2294967] using wordTrace_append hprefix tailTrace_2294967
  have hstable : (prefixWord ++ tailWord_2294967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2294967).length < 2 ^ (prefixWord ++ tailWord_2294967).sum := by decide
  have hdescent : baseEnd_2294967 < baseStart_2294967 := by decide
  rcases family_descends (prefixWord ++ tailWord_2294967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2294993 : List Nat := [1, 2, 2, 1, 2, 2, 1, 1, 5, 1, 5]
def baseStart_2294993 : Nat := 118140960795 + 2294993 * 2 ^ 59
def prefixEnd_2294993 : Nat := 4983230072969 + 3 ^ 40 * 2294993 * 2
def baseEnd_2294993 : Nat := 1178434507704044563033025

theorem tailTrace_2294993 : CollatzResearch.WordTrace tailWord_2294993 prefixEnd_2294993 1178434507704044563033025 := by
  unfold tailWord_2294993
  simp only [CollatzResearch.WordTrace]
  refine ⟨83705271374639789444489633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55803514249759859629659755 83705271374639789444489633)
  ·
    refine ⟨62778953530979842083367225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83705271374639789444489633 62778953530979842083367225)
    ·
      refine ⟨47084215148234881562525419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62778953530979842083367225 47084215148234881562525419)
      ·
        refine ⟨70626322722352322343788129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47084215148234881562525419 70626322722352322343788129)
        ·
          refine ⟨52969742041764241757841097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70626322722352322343788129 52969742041764241757841097)
          ·
            refine ⟨39727306531323181318380823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52969742041764241757841097 39727306531323181318380823)
            ·
              refine ⟨59590959796984771977571235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39727306531323181318380823 59590959796984771977571235)
              ·
                refine ⟨89386439695477157966356853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59590959796984771977571235 89386439695477157966356853)
                ·
                  refine ⟨8379978721450983559345955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 89386439695477157966356853 8379978721450983559345955)
                  ·
                    refine ⟨12569968082176475339018933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8379978721450983559345955 12569968082176475339018933)
                    ·
                      refine ⟨1178434507704044563033025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12569968082176475339018933 1178434507704044563033025)
                      ·
                        rfl

theorem cell23_2294993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 5, 1, 5].length) (baseStart_2294993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2294993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2294993 prefixEnd_2294993 := by exact prefixLift 2294993
  have htrace : WordTrace (prefixWord ++ tailWord_2294993) baseStart_2294993 baseEnd_2294993 := by
    simpa [prefixWord, tailWord_2294993, baseEnd_2294993] using wordTrace_append hprefix tailTrace_2294993
  have hstable : (prefixWord ++ tailWord_2294993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2294993).length < 2 ^ (prefixWord ++ tailWord_2294993).sum := by decide
  have hdescent : baseEnd_2294993 < baseStart_2294993 := by decide
  rcases family_descends (prefixWord ++ tailWord_2294993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2295007 : List Nat := [1, 1, 2, 3, 2, 1, 2, 2, 5, 2, 2]
def baseStart_2295007 : Nat := 118140960795 + 2295007 * 2 ^ 59
def prefixEnd_2295007 : Nat := 4983230072969 + 3 ^ 40 * 2295007 * 2
def baseEnd_2295007 : Nat := 1178441696433207508257961

theorem tailTrace_2295007 : CollatzResearch.WordTrace tailWord_2295007 prefixEnd_2295007 1178441696433207508257961 := by
  unfold tailWord_2295007
  simp only [CollatzResearch.WordTrace]
  refine ⟨83705781996589069835499275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55803854664392713223666183 83705781996589069835499275)
  ·
    refine ⟨125558672994883604753248913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83705781996589069835499275 125558672994883604753248913)
    ·
      refine ⟨94169004746162703564936685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125558672994883604753248913 94169004746162703564936685)
      ·
        refine ⟨35313376779811013836851257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94169004746162703564936685 35313376779811013836851257)
        ·
          refine ⟨26485032584858260377638443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35313376779811013836851257 26485032584858260377638443)
          ·
            refine ⟨39727548877287390566457665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26485032584858260377638443 39727548877287390566457665)
            ·
              refine ⟨29795661657965542924843249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39727548877287390566457665 29795661657965542924843249)
              ·
                refine ⟨22346746243474157193632437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29795661657965542924843249 22346746243474157193632437)
                ·
                  refine ⟨2095007460325702236903041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22346746243474157193632437 2095007460325702236903041)
                  ·
                    refine ⟨1571255595244276677677281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2095007460325702236903041 1571255595244276677677281)
                    ·
                      refine ⟨1178441696433207508257961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1571255595244276677677281 1178441696433207508257961)
                      ·
                        rfl

theorem cell23_2295007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 2, 5, 2, 2].length) (baseStart_2295007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2295007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2295007 prefixEnd_2295007 := by exact prefixLift 2295007
  have htrace : WordTrace (prefixWord ++ tailWord_2295007) baseStart_2295007 baseEnd_2295007 := by
    simpa [prefixWord, tailWord_2295007, baseEnd_2295007] using wordTrace_append hprefix tailTrace_2295007
  have hstable : (prefixWord ++ tailWord_2295007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2295007).length < 2 ^ (prefixWord ++ tailWord_2295007).sum := by decide
  have hdescent : baseEnd_2295007 < baseStart_2295007 := by decide
  rcases family_descends (prefixWord ++ tailWord_2295007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2295033 : List Nat := [1, 2, 1, 3, 1, 1, 3, 1, 2, 2, 6]
def baseStart_2295033 : Nat := 118140960795 + 2295033 * 2 ^ 59
def prefixEnd_2295033 : Nat := 4983230072969 + 3 ^ 40 * 2295033 * 2
def baseEnd_2295033 : Nat := 1178455046930224406532841

theorem tailTrace_2295033 : CollatzResearch.WordTrace tailWord_2295033 prefixEnd_2295033 1178455046930224406532841 := by
  unfold tailWord_2295033
  simp only [CollatzResearch.WordTrace]
  refine ⟨83706730294494876275945753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55804486862996584183963835 83706730294494876275945753)
  ·
    refine ⟨62780047720871157206959315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83706730294494876275945753 62780047720871157206959315)
    ·
      refine ⟨94170071581306735810438973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62780047720871157206959315 94170071581306735810438973)
      ·
        refine ⟨35313776842990025928914615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94170071581306735810438973 35313776842990025928914615)
        ·
          refine ⟨52970665264485038893371923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35313776842990025928914615 52970665264485038893371923)
          ·
            refine ⟨79455997896727558340057885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52970665264485038893371923 79455997896727558340057885)
            ·
              refine ⟨29795999211272834377521707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79455997896727558340057885 29795999211272834377521707)
              ·
                refine ⟨44693998816909251566282561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29795999211272834377521707 44693998816909251566282561)
                ·
                  refine ⟨33520499112681938674711921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44693998816909251566282561 33520499112681938674711921)
                  ·
                    refine ⟨25140374334511454006033941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33520499112681938674711921 25140374334511454006033941)
                    ·
                      refine ⟨1178455046930224406532841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25140374334511454006033941 1178455046930224406532841)
                      ·
                        rfl

theorem cell23_2295033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 1, 2, 2, 6].length) (baseStart_2295033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2295033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2295033 prefixEnd_2295033 := by exact prefixLift 2295033
  have htrace : WordTrace (prefixWord ++ tailWord_2295033) baseStart_2295033 baseEnd_2295033 := by
    simpa [prefixWord, tailWord_2295033, baseEnd_2295033] using wordTrace_append hprefix tailTrace_2295033
  have hstable : (prefixWord ++ tailWord_2295033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2295033).length < 2 ^ (prefixWord ++ tailWord_2295033).sum := by decide
  have hdescent : baseEnd_2295033 < baseStart_2295033 := by decide
  rcases family_descends (prefixWord ++ tailWord_2295033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2295040 : List Nat := [2, 1, 1, 2, 1, 1, 3, 5, 1, 3, 3]
def baseStart_2295040 : Nat := 118140960795 + 2295040 * 2 ^ 59
def prefixEnd_2295040 : Nat := 4983230072969 + 3 ^ 40 * 2295040 * 2
def baseEnd_2295040 : Nat := 1178458641294805879145309

theorem tailTrace_2295040 : CollatzResearch.WordTrace tailWord_2295040 prefixEnd_2295040 1178458641294805879145309 := by
  unfold tailWord_2295040
  simp only [CollatzResearch.WordTrace]
  refine ⟨41853492802734758235725287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55804657070313010980967049 41853492802734758235725287)
  ·
    refine ⟨62780239204102137353587931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41853492802734758235725287 62780239204102137353587931)
    ·
      refine ⟨94170358806153206030381897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62780239204102137353587931 94170358806153206030381897)
      ·
        refine ⟨70627769104614904522786423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94170358806153206030381897 70627769104614904522786423)
        ·
          refine ⟨105941653656922356784179635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70627769104614904522786423 105941653656922356784179635)
          ·
            refine ⟨158912480485383535176269453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105941653656922356784179635 158912480485383535176269453)
            ·
              refine ⟨59592180182018825691101045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 158912480485383535176269453 59592180182018825691101045)
              ·
                refine ⟨5586766892064264908540723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 59592180182018825691101045 5586766892064264908540723)
                ·
                  refine ⟨8380150338096397362811085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5586766892064264908540723 8380150338096397362811085)
                  ·
                    refine ⟨3142556376786149011054157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8380150338096397362811085 3142556376786149011054157)
                    ·
                      refine ⟨1178458641294805879145309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3142556376786149011054157 1178458641294805879145309)
                      ·
                        rfl

theorem cell23_2295040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 5, 1, 3, 3].length) (baseStart_2295040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2295040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2295040 prefixEnd_2295040 := by exact prefixLift 2295040
  have htrace : WordTrace (prefixWord ++ tailWord_2295040) baseStart_2295040 baseEnd_2295040 := by
    simpa [prefixWord, tailWord_2295040, baseEnd_2295040] using wordTrace_append hprefix tailTrace_2295040
  have hstable : (prefixWord ++ tailWord_2295040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2295040).length < 2 ^ (prefixWord ++ tailWord_2295040).sum := by decide
  have hdescent : baseEnd_2295040 < baseStart_2295040 := by decide
  rcases family_descends (prefixWord ++ tailWord_2295040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2295044 : List Nat := [2, 3, 2, 2, 2, 1, 3, 2, 1, 2, 3]
def baseStart_2295044 : Nat := 118140960795 + 2295044 * 2 ^ 59
def prefixEnd_2295044 : Nat := 4983230072969 + 3 ^ 40 * 2295044 * 2
def baseEnd_2295044 : Nat := 1178460695217423863495291

theorem tailTrace_2295044 : CollatzResearch.WordTrace tailWord_2295044 prefixEnd_2295044 1178460695217423863495291 := by
  unfold tailWord_2295044
  simp only [CollatzResearch.WordTrace]
  refine ⟨41853565748727512577298093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55804754331636683436397457 41853565748727512577298093)
  ·
    refine ⟨15695087155772817216486785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41853565748727512577298093 15695087155772817216486785)
    ·
      refine ⟨11771315366829612912365089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15695087155772817216486785 11771315366829612912365089)
      ·
        refine ⟨8828486525122209684273817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11771315366829612912365089 8828486525122209684273817)
        ·
          refine ⟨6621364893841657263205363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8828486525122209684273817 6621364893841657263205363)
          ·
            refine ⟨9932047340762485894808045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6621364893841657263205363 9932047340762485894808045)
            ·
              refine ⟨3724517752785932210553017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9932047340762485894808045 3724517752785932210553017)
              ·
                refine ⟨2793388314589449157914763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3724517752785932210553017 2793388314589449157914763)
                ·
                  refine ⟨4190082471884173736872145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2793388314589449157914763 4190082471884173736872145)
                  ·
                    refine ⟨3142561853913130302654109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4190082471884173736872145 3142561853913130302654109)
                    ·
                      refine ⟨1178460695217423863495291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3142561853913130302654109 1178460695217423863495291)
                      ·
                        rfl

theorem cell23_2295044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 3, 2, 1, 2, 3].length) (baseStart_2295044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2295044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2295044 prefixEnd_2295044 := by exact prefixLift 2295044
  have htrace : WordTrace (prefixWord ++ tailWord_2295044) baseStart_2295044 baseEnd_2295044 := by
    simpa [prefixWord, tailWord_2295044, baseEnd_2295044] using wordTrace_append hprefix tailTrace_2295044
  have hstable : (prefixWord ++ tailWord_2295044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2295044).length < 2 ^ (prefixWord ++ tailWord_2295044).sum := by decide
  have hdescent : baseEnd_2295044 < baseStart_2295044 := by decide
  rcases family_descends (prefixWord ++ tailWord_2295044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2295058 : List Nat := [3, 2, 4, 2, 1, 1, 3, 1, 1, 1, 4]
def baseStart_2295058 : Nat := 118140960795 + 2295058 * 2 ^ 59
def prefixEnd_2295058 : Nat := 4983230072969 + 3 ^ 40 * 2295058 * 2
def baseEnd_2295058 : Nat := 1178467883946586808720227

theorem tailTrace_2295058 : CollatzResearch.WordTrace tailWord_2295058 prefixEnd_2295058 1178467883946586808720227 := by
  unfold tailWord_2295058
  simp only [CollatzResearch.WordTrace]
  refine ⟨20926910529851076386401457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55805094746269537030403885 20926910529851076386401457)
  ·
    refine ⟨15695182897388307289801093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20926910529851076386401457 15695182897388307289801093)
    ·
      refine ⟨2942846793260307616837705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15695182897388307289801093 2942846793260307616837705)
      ·
        refine ⟨2207135094945230712628279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2942846793260307616837705 2207135094945230712628279)
        ·
          refine ⟨3310702642417846068942419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2207135094945230712628279 3310702642417846068942419)
          ·
            refine ⟨4966053963626769103413629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3310702642417846068942419 4966053963626769103413629)
            ·
              refine ⟨1862270236360038413780111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4966053963626769103413629 1862270236360038413780111)
              ·
                refine ⟨2793405354540057620670167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1862270236360038413780111 2793405354540057620670167)
                ·
                  refine ⟨4190108031810086431005251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2793405354540057620670167 4190108031810086431005251)
                  ·
                    refine ⟨6285162047715129646507877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4190108031810086431005251 6285162047715129646507877)
                    ·
                      refine ⟨1178467883946586808720227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6285162047715129646507877 1178467883946586808720227)
                      ·
                        rfl

theorem cell23_2295058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_2295058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2295058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2295058 prefixEnd_2295058 := by exact prefixLift 2295058
  have htrace : WordTrace (prefixWord ++ tailWord_2295058) baseStart_2295058 baseEnd_2295058 := by
    simpa [prefixWord, tailWord_2295058, baseEnd_2295058] using wordTrace_append hprefix tailTrace_2295058
  have hstable : (prefixWord ++ tailWord_2295058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2295058).length < 2 ^ (prefixWord ++ tailWord_2295058).sum := by decide
  have hdescent : baseEnd_2295058 < baseStart_2295058 := by decide
  rcases family_descends (prefixWord ++ tailWord_2295058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2295090 : List Nat := [3, 2, 1, 1, 4, 1, 1, 1, 1, 8]
def baseStart_2295090 : Nat := 118140960795 + 2295090 * 2 ^ 59
def prefixEnd_2295090 : Nat := 4983230072969 + 3 ^ 40 * 2295090 * 2
def baseEnd_2295090 : Nat := 392828105109176894506693

theorem tailTrace_2295090 : CollatzResearch.WordTrace tailWord_2295090 prefixEnd_2295090 392828105109176894506693 := by
  unfold tailWord_2295090
  simp only [CollatzResearch.WordTrace]
  refine ⟨20927202313822093752692681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55805872836858916673847149 20927202313822093752692681)
  ·
    refine ⟨15695401735366570314519511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20927202313822093752692681 15695401735366570314519511)
    ·
      refine ⟨23543102603049855471779267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15695401735366570314519511 23543102603049855471779267)
      ·
        refine ⟨35314653904574783207668901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23543102603049855471779267 35314653904574783207668901)
        ·
          refine ⟨6621497607107771851437919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35314653904574783207668901 6621497607107771851437919)
          ·
            refine ⟨9932246410661657777156879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6621497607107771851437919 9932246410661657777156879)
            ·
              refine ⟨14898369615992486665735319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9932246410661657777156879 14898369615992486665735319)
              ·
                refine ⟨22347554423988729998602979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14898369615992486665735319 22347554423988729998602979)
                ·
                  refine ⟨33521331635983094997904469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22347554423988729998602979 33521331635983094997904469)
                  ·
                    refine ⟨392828105109176894506693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 33521331635983094997904469 392828105109176894506693)
                    ·
                      rfl

theorem cell23_2295090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 1, 1, 8].length) (baseStart_2295090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2295090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2295090 prefixEnd_2295090 := by exact prefixLift 2295090
  have htrace : WordTrace (prefixWord ++ tailWord_2295090) baseStart_2295090 baseEnd_2295090 := by
    simpa [prefixWord, tailWord_2295090, baseEnd_2295090] using wordTrace_append hprefix tailTrace_2295090
  have hstable : (prefixWord ++ tailWord_2295090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2295090).length < 2 ^ (prefixWord ++ tailWord_2295090).sum := by decide
  have hdescent : baseEnd_2295090 < baseStart_2295090 := by decide
  rcases family_descends (prefixWord ++ tailWord_2295090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2295148 : List Nat := [2, 2, 1, 1, 5, 2, 3, 1, 2, 2, 2]
def baseStart_2295148 : Nat := 118140960795 + 2295148 * 2 ^ 59
def prefixEnd_2295148 : Nat := 4983230072969 + 3 ^ 40 * 2295148 * 2
def baseEnd_2295148 : Nat := 1178514097205491456594813

theorem tailTrace_2295148 : CollatzResearch.WordTrace tailWord_2295148 prefixEnd_2295148 1178514097205491456594813 := by
  unfold tailWord_2295148
  simp only [CollatzResearch.WordTrace]
  refine ⟨41855462344539125458191049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55807283126052167277588065 41855462344539125458191049)
  ·
    refine ⟨31391596758404344093643287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41855462344539125458191049 31391596758404344093643287)
    ·
      refine ⟨47087395137606516140464931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31391596758404344093643287 47087395137606516140464931)
      ·
        refine ⟨70631092706409774210697397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47087395137606516140464931 70631092706409774210697397)
        ·
          refine ⟨6621664941225916332252881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 70631092706409774210697397 6621664941225916332252881)
          ·
            refine ⟨4966248705919437249189661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6621664941225916332252881 4966248705919437249189661)
            ·
              refine ⟨1862343264719788968446123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4966248705919437249189661 1862343264719788968446123)
              ·
                refine ⟨2793514897079683452669185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1862343264719788968446123 2793514897079683452669185)
                ·
                  refine ⟨2095136172809762589501889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2793514897079683452669185 2095136172809762589501889)
                  ·
                    refine ⟨1571352129607321942126417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2095136172809762589501889 1571352129607321942126417)
                    ·
                      refine ⟨1178514097205491456594813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1571352129607321942126417 1178514097205491456594813)
                      ·
                        rfl

theorem cell23_2295148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 2, 2].length) (baseStart_2295148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2295148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2295148 prefixEnd_2295148 := by exact prefixLift 2295148
  have htrace : WordTrace (prefixWord ++ tailWord_2295148) baseStart_2295148 baseEnd_2295148 := by
    simpa [prefixWord, tailWord_2295148, baseEnd_2295148] using wordTrace_append hprefix tailTrace_2295148
  have hstable : (prefixWord ++ tailWord_2295148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2295148).length < 2 ^ (prefixWord ++ tailWord_2295148).sum := by decide
  have hdescent : baseEnd_2295148 < baseStart_2295148 := by decide
  rcases family_descends (prefixWord ++ tailWord_2295148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2295244 : List Nat := [2, 2, 1, 4, 2, 2, 2, 2, 6]
def baseStart_2295244 : Nat := 118140960795 + 2295244 * 2 ^ 59
def prefixEnd_2295244 : Nat := 4983230072969 + 3 ^ 40 * 2295244 * 2
def baseEnd_2295244 : Nat := 130951487927591453443819

theorem tailTrace_2295244 : CollatzResearch.WordTrace tailWord_2295244 prefixEnd_2295244 130951487927591453443819 := by
  unfold tailWord_2295244
  simp only [CollatzResearch.WordTrace]
  refine ⟨41857213048365229655938393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55809617397820306207917857 41857213048365229655938393)
  ·
    refine ⟨31392909786273922241953795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41857213048365229655938393 31392909786273922241953795)
    ·
      refine ⟨47089364679410883362930693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31392909786273922241953795 47089364679410883362930693)
      ·
        refine ⟨8829255877389540630549505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47089364679410883362930693 8829255877389540630549505)
        ·
          refine ⟨6621941908042155472912129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8829255877389540630549505 6621941908042155472912129)
          ·
            refine ⟨4966456431031616604684097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6621941908042155472912129 4966456431031616604684097)
            ·
              refine ⟨3724842323273712453513073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4966456431031616604684097 3724842323273712453513073)
              ·
                refine ⟨2793631742455284340134805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3724842323273712453513073 2793631742455284340134805)
                ·
                  refine ⟨130951487927591453443819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2793631742455284340134805 130951487927591453443819)
                  ·
                    rfl

theorem cell23_2295244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 2, 2, 6].length) (baseStart_2295244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2295244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2295244 prefixEnd_2295244 := by exact prefixLift 2295244
  have htrace : WordTrace (prefixWord ++ tailWord_2295244) baseStart_2295244 baseEnd_2295244 := by
    simpa [prefixWord, tailWord_2295244, baseEnd_2295244] using wordTrace_append hprefix tailTrace_2295244
  have hstable : (prefixWord ++ tailWord_2295244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2295244).length < 2 ^ (prefixWord ++ tailWord_2295244).sum := by decide
  have hdescent : baseEnd_2295244 < baseStart_2295244 := by decide
  rcases family_descends (prefixWord ++ tailWord_2295244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2295257 : List Nat := [1, 2, 1, 2, 4, 2, 1, 2, 3, 5]
def baseStart_2295257 : Nat := 118140960795 + 2295257 * 2 ^ 59
def prefixEnd_2295257 : Nat := 4983230072969 + 3 ^ 40 * 2295257 * 2
def baseEnd_2295257 : Nat := 392856688865610510043937

theorem tailTrace_2295257 : CollatzResearch.WordTrace tailWord_2295257 prefixEnd_2295257 392856688865610510043937 := by
  unfold tailWord_2295257
  simp only [CollatzResearch.WordTrace]
  refine ⟨83714900245683362532100025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55809933497122241688066683 83714900245683362532100025)
  ·
    refine ⟨62786175184262521899075019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83714900245683362532100025 62786175184262521899075019)
    ·
      refine ⟨94179262776393782848612529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62786175184262521899075019 94179262776393782848612529)
      ·
        refine ⟨70634447082295337136459397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94179262776393782848612529 70634447082295337136459397)
        ·
          refine ⟨13243958827930375713086137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 70634447082295337136459397 13243958827930375713086137)
          ·
            refine ⟨9932969120947781784814603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13243958827930375713086137 9932969120947781784814603)
            ·
              refine ⟨14899453681421672677221905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9932969120947781784814603 14899453681421672677221905)
              ·
                refine ⟨11174590261066254507916429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14899453681421672677221905 11174590261066254507916429)
                ·
                  refine ⟨4190471347899845440468661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11174590261066254507916429 4190471347899845440468661)
                  ·
                    refine ⟨392856688865610510043937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4190471347899845440468661 392856688865610510043937)
                    ·
                      rfl

theorem cell23_2295257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 2, 3, 5].length) (baseStart_2295257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2295257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2295257 prefixEnd_2295257 := by exact prefixLift 2295257
  have htrace : WordTrace (prefixWord ++ tailWord_2295257) baseStart_2295257 baseEnd_2295257 := by
    simpa [prefixWord, tailWord_2295257, baseEnd_2295257] using wordTrace_append hprefix tailTrace_2295257
  have hstable : (prefixWord ++ tailWord_2295257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2295257).length < 2 ^ (prefixWord ++ tailWord_2295257).sum := by decide
  have hdescent : baseEnd_2295257 < baseStart_2295257 := by decide
  rcases family_descends (prefixWord ++ tailWord_2295257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2295271 : List Nat := [1, 1, 5, 2, 1, 3, 1, 2, 3, 1, 3]
def baseStart_2295271 : Nat := 118140960795 + 2295271 * 2 ^ 59
def prefixEnd_2295271 : Nat := 4983230072969 + 3 ^ 40 * 2295271 * 2
def baseEnd_2295271 : Nat := 1178577255325994475356747

theorem tailTrace_2295271 : CollatzResearch.WordTrace tailWord_2295271 prefixEnd_2295271 1178577255325994475356747 := by
  unfold tailWord_2295271
  simp only [CollatzResearch.WordTrace]
  refine ⟨83715410867632642923109667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55810273911755095282073111 83715410867632642923109667)
  ·
    refine ⟨125573116301448964384664501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83715410867632642923109667 125573116301448964384664501)
    ·
      refine ⟨11772479653260840411062297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 125573116301448964384664501 11772479653260840411062297)
      ·
        refine ⟨8829359739945630308296723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11772479653260840411062297 8829359739945630308296723)
        ·
          refine ⟨13244039609918445462445085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8829359739945630308296723 13244039609918445462445085)
          ·
            refine ⟨4966514853719417048416907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13244039609918445462445085 4966514853719417048416907)
            ·
              refine ⟨7449772280579125572625361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4966514853719417048416907 7449772280579125572625361)
              ·
                refine ⟨5587329210434344179469021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7449772280579125572625361 5587329210434344179469021)
                ·
                  refine ⟨2095248453912879067300883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5587329210434344179469021 2095248453912879067300883)
                  ·
                    refine ⟨3142872680869318600951325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2095248453912879067300883 3142872680869318600951325)
                    ·
                      refine ⟨1178577255325994475356747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3142872680869318600951325 1178577255325994475356747)
                      ·
                        rfl

theorem cell23_2295271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 2, 3, 1, 3].length) (baseStart_2295271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2295271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2295271 prefixEnd_2295271 := by exact prefixLift 2295271
  have htrace : WordTrace (prefixWord ++ tailWord_2295271) baseStart_2295271 baseEnd_2295271 := by
    simpa [prefixWord, tailWord_2295271, baseEnd_2295271] using wordTrace_append hprefix tailTrace_2295271
  have hstable : (prefixWord ++ tailWord_2295271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2295271).length < 2 ^ (prefixWord ++ tailWord_2295271).sum := by decide
  have hdescent : baseEnd_2295271 < baseStart_2295271 := by decide
  rcases family_descends (prefixWord ++ tailWord_2295271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2295281 : List Nat := [1, 2, 2, 2, 3, 2, 3, 1, 2, 3, 2]
def baseStart_2295281 : Nat := 118140960795 + 2295281 * 2 ^ 59
def prefixEnd_2295281 : Nat := 4983230072969 + 3 ^ 40 * 2295281 * 2
def baseEnd_2295281 : Nat := 1178582390132539436231701

theorem tailTrace_2295281 : CollatzResearch.WordTrace tailWord_2295281 prefixEnd_2295281 1178582390132539436231701 := by
  unfold tailWord_2295281
  simp only [CollatzResearch.WordTrace]
  refine ⟨83715775597596414630973697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55810517065064276420649131 83715775597596414630973697)
  ·
    refine ⟨62786831698197310973230273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83715775597596414630973697 62786831698197310973230273)
    ·
      refine ⟨47090123773647983229922705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62786831698197310973230273 47090123773647983229922705)
      ·
        refine ⟨35317592830235987422442029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47090123773647983229922705 35317592830235987422442029)
        ·
          refine ⟨13244097311338495283415761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35317592830235987422442029 13244097311338495283415761)
          ·
            refine ⟨9933072983503871462561821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13244097311338495283415761 9933072983503871462561821)
            ·
              refine ⟨3724902368813951798460683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9933072983503871462561821 3724902368813951798460683)
              ·
                refine ⟨5587353553220927697691025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3724902368813951798460683 5587353553220927697691025)
                ·
                  refine ⟨4190515164915695773268269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5587353553220927697691025 4190515164915695773268269)
                  ·
                    refine ⟨1571443186843385914975601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4190515164915695773268269 1571443186843385914975601)
                    ·
                      refine ⟨1178582390132539436231701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1571443186843385914975601 1178582390132539436231701)
                      ·
                        rfl

theorem cell23_2295281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 3, 1, 2, 3, 2].length) (baseStart_2295281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2295281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2295281 prefixEnd_2295281 := by exact prefixLift 2295281
  have htrace : WordTrace (prefixWord ++ tailWord_2295281) baseStart_2295281 baseEnd_2295281 := by
    simpa [prefixWord, tailWord_2295281, baseEnd_2295281] using wordTrace_append hprefix tailTrace_2295281
  have hstable : (prefixWord ++ tailWord_2295281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2295281).length < 2 ^ (prefixWord ++ tailWord_2295281).sum := by decide
  have hdescent : baseEnd_2295281 < baseStart_2295281 := by decide
  rcases family_descends (prefixWord ++ tailWord_2295281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2295288 : List Nat := [2, 1, 2, 1, 1, 6, 2, 3, 1, 1, 3]
def baseStart_2295288 : Nat := 118140960795 + 2295288 * 2 ^ 59
def prefixEnd_2295288 : Nat := 4983230072969 + 3 ^ 40 * 2295288 * 2
def baseEnd_2295288 : Nat := 1178585984497120908844169

theorem tailTrace_2295288 : CollatzResearch.WordTrace tailWord_2295288 prefixEnd_2295288 1178585984497120908844169 := by
  unfold tailWord_2295288
  simp only [CollatzResearch.WordTrace]
  refine ⟨41858015454285527413239259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55810687272380703217652345 41858015454285527413239259)
  ·
    refine ⟨62787023181428291119858889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41858015454285527413239259 62787023181428291119858889)
    ·
      refine ⟨47090267386071218339894167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62787023181428291119858889 47090267386071218339894167)
      ·
        refine ⟨70635401079106827509841251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47090267386071218339894167 70635401079106827509841251)
        ·
          refine ⟨105953101618660241264761877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70635401079106827509841251 105953101618660241264761877)
          ·
            refine ⟨4966551638374698809285713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 105953101618660241264761877 4966551638374698809285713)
            ·
              refine ⟨3724913728781024106964285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4966551638374698809285713 3724913728781024106964285)
              ·
                refine ⟨1396842648292884040111607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3724913728781024106964285 1396842648292884040111607)
                ·
                  refine ⟨2095263972439326060167411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1396842648292884040111607 2095263972439326060167411)
                  ·
                    refine ⟨3142895958658989090251117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2095263972439326060167411 3142895958658989090251117)
                    ·
                      refine ⟨1178585984497120908844169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3142895958658989090251117 1178585984497120908844169)
                      ·
                        rfl

theorem cell23_2295288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 2, 3, 1, 1, 3].length) (baseStart_2295288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2295288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2295288 prefixEnd_2295288 := by exact prefixLift 2295288
  have htrace : WordTrace (prefixWord ++ tailWord_2295288) baseStart_2295288 baseEnd_2295288 := by
    simpa [prefixWord, tailWord_2295288, baseEnd_2295288] using wordTrace_append hprefix tailTrace_2295288
  have hstable : (prefixWord ++ tailWord_2295288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2295288).length < 2 ^ (prefixWord ++ tailWord_2295288).sum := by decide
  have hdescent : baseEnd_2295288 < baseStart_2295288 := by decide
  rcases family_descends (prefixWord ++ tailWord_2295288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2295328 : List Nat := [2, 1, 1, 6, 1, 1, 2, 2, 3, 2, 2]
def baseStart_2295328 : Nat := 118140960795 + 2295328 * 2 ^ 59
def prefixEnd_2295328 : Nat := 4983230072969 + 3 ^ 40 * 2295328 * 2
def baseEnd_2295328 : Nat := 1178606523723300752343985

theorem tailTrace_2295328 : CollatzResearch.WordTrace tailWord_2295328 prefixEnd_2295328 1178606523723300752343985 := by
  unfold tailWord_2295328
  simp only [CollatzResearch.WordTrace]
  refine ⟨41858744914213070828967319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55811659885617427771956425 41858744914213070828967319)
  ·
    refine ⟨62788117371319606243450979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41858744914213070828967319 62788117371319606243450979)
    ·
      refine ⟨94182176056979409365176469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62788117371319606243450979 94182176056979409365176469)
      ·
        refine ⟨4414789502670909813992647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 94182176056979409365176469 4414789502670909813992647)
        ·
          refine ⟨6622184254006364720988971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4414789502670909813992647 6622184254006364720988971)
          ·
            refine ⟨9933276381009547081483457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6622184254006364720988971 9933276381009547081483457)
            ·
              refine ⟨7449957285757160311112593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9933276381009547081483457 7449957285757160311112593)
              ·
                refine ⟨5587467964317870233334445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7449957285757160311112593 5587467964317870233334445)
                ·
                  refine ⟨2095300486619201337500417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5587467964317870233334445 2095300486619201337500417)
                  ·
                    refine ⟨1571475364964401003125313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2095300486619201337500417 1571475364964401003125313)
                    ·
                      refine ⟨1178606523723300752343985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1571475364964401003125313 1178606523723300752343985)
                      ·
                        rfl

theorem cell23_2295328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 2, 3, 2, 2].length) (baseStart_2295328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2295328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2295328 prefixEnd_2295328 := by exact prefixLift 2295328
  have htrace : WordTrace (prefixWord ++ tailWord_2295328) baseStart_2295328 baseEnd_2295328 := by
    simpa [prefixWord, tailWord_2295328, baseEnd_2295328] using wordTrace_append hprefix tailTrace_2295328
  have hstable : (prefixWord ++ tailWord_2295328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2295328).length < 2 ^ (prefixWord ++ tailWord_2295328).sum := by decide
  have hdescent : baseEnd_2295328 < baseStart_2295328 := by decide
  rcases family_descends (prefixWord ++ tailWord_2295328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2295361 : List Nat := [1, 2, 5, 1, 1, 1, 1, 3, 4, 1, 3]
def baseStart_2295361 : Nat := 118140960795 + 2295361 * 2 ^ 59
def prefixEnd_2295361 : Nat := 4983230072969 + 3 ^ 40 * 2295361 * 2
def baseEnd_2295361 : Nat := 1178623468584899123231333

theorem tailTrace_2295361 : CollatzResearch.WordTrace tailWord_2295361 prefixEnd_2295361 1178623468584899123231333 := by
  unfold tailWord_2295361
  simp only [CollatzResearch.WordTrace]
  refine ⟨83718693437306588293885937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55812462291537725529257291 83718693437306588293885937)
  ·
    refine ⟨62789020077979941220414453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83718693437306588293885937 62789020077979941220414453)
    ·
      refine ⟨5886470632310619489413855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 62789020077979941220414453 5886470632310619489413855)
      ·
        refine ⟨8829705948465929234120783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5886470632310619489413855 8829705948465929234120783)
        ·
          refine ⟨13244558922698893851181175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8829705948465929234120783 13244558922698893851181175)
          ·
            refine ⟨19866838384048340776771763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13244558922698893851181175 19866838384048340776771763)
            ·
              refine ⟨29800257576072511165157645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19866838384048340776771763 29800257576072511165157645)
              ·
                refine ⟨11175096591027191686934117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29800257576072511165157645 11175096591027191686934117)
                ·
                  refine ⟨2095330610817598441300147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11175096591027191686934117 2095330610817598441300147)
                  ·
                    refine ⟨3142995916226397661950221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2095330610817598441300147 3142995916226397661950221)
                    ·
                      refine ⟨1178623468584899123231333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3142995916226397661950221 1178623468584899123231333)
                      ·
                        rfl

theorem cell23_2295361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 3, 4, 1, 3].length) (baseStart_2295361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2295361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2295361 prefixEnd_2295361 := by exact prefixLift 2295361
  have htrace : WordTrace (prefixWord ++ tailWord_2295361) baseStart_2295361 baseEnd_2295361 := by
    simpa [prefixWord, tailWord_2295361, baseEnd_2295361] using wordTrace_append hprefix tailTrace_2295361
  have hstable : (prefixWord ++ tailWord_2295361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2295361).length < 2 ^ (prefixWord ++ tailWord_2295361).sum := by decide
  have hdescent : baseEnd_2295361 < baseStart_2295361 := by decide
  rcases family_descends (prefixWord ++ tailWord_2295361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2295377 : List Nat := [1, 2, 2, 1, 3, 2, 2, 1, 1, 8]
def baseStart_2295377 : Nat := 118140960795 + 2295377 * 2 ^ 59
def prefixEnd_2295377 : Nat := 4983230072969 + 3 ^ 40 * 2295377 * 2
def baseEnd_2295377 : Nat := 392877228091790353543753

theorem tailTrace_2295377 : CollatzResearch.WordTrace tailWord_2295377 prefixEnd_2295377 392877228091790353543753 := by
  unfold tailWord_2295377
  simp only [CollatzResearch.WordTrace]
  refine ⟨83719277005248623026468385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55812851336832415350978923 83719277005248623026468385)
  ·
    refine ⟨62789457753936467269851289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83719277005248623026468385 62789457753936467269851289)
    ·
      refine ⟨47092093315452350452388467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62789457753936467269851289 47092093315452350452388467)
      ·
        refine ⟨70638139973178525678582701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47092093315452350452388467 70638139973178525678582701)
        ·
          refine ⟨26489302489941947129468513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70638139973178525678582701 26489302489941947129468513)
          ·
            refine ⟨19866976867456460347101385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26489302489941947129468513 19866976867456460347101385)
            ·
              refine ⟨14900232650592345260326039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19866976867456460347101385 14900232650592345260326039)
              ·
                refine ⟨22350348975888517890489059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14900232650592345260326039 22350348975888517890489059)
                ·
                  refine ⟨33525523463832776835733589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22350348975888517890489059 33525523463832776835733589)
                  ·
                    refine ⟨392877228091790353543753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 33525523463832776835733589 392877228091790353543753)
                    ·
                      rfl

theorem cell23_2295377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 1, 1, 8].length) (baseStart_2295377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2295377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2295377 prefixEnd_2295377 := by exact prefixLift 2295377
  have htrace : WordTrace (prefixWord ++ tailWord_2295377) baseStart_2295377 baseEnd_2295377 := by
    simpa [prefixWord, tailWord_2295377, baseEnd_2295377] using wordTrace_append hprefix tailTrace_2295377
  have hstable : (prefixWord ++ tailWord_2295377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2295377).length < 2 ^ (prefixWord ++ tailWord_2295377).sum := by decide
  have hdescent : baseEnd_2295377 < baseStart_2295377 := by decide
  rcases family_descends (prefixWord ++ tailWord_2295377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2295378 : List Nat := [3, 2, 2, 1, 2, 3, 1, 3, 2, 1, 3]
def baseStart_2295378 : Nat := 118140960795 + 2295378 * 2 ^ 59
def prefixEnd_2295378 : Nat := 4983230072969 + 3 ^ 40 * 2295378 * 2
def baseEnd_2295378 : Nat := 1178632197756025556718755

theorem tailTrace_2295378 : CollatzResearch.WordTrace tailWord_2295378 prefixEnd_2295378 1178632197756025556718755 := by
  unfold tailWord_2295378
  simp only [CollatzResearch.WordTrace]
  refine ⟨20929828369561250049313697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55812875652163333464836525 20929828369561250049313697)
  ·
    refine ⟨15697371277170937536985273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20929828369561250049313697 15697371277170937536985273)
    ·
      refine ⟨11773028457878203152738955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15697371277170937536985273 11773028457878203152738955)
      ·
        refine ⟨17659542686817304729108433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11773028457878203152738955 17659542686817304729108433)
        ·
          refine ⟨13244657015112978546831325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17659542686817304729108433 13244657015112978546831325)
          ·
            refine ⟨4966746380667366955061747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13244657015112978546831325 4966746380667366955061747)
            ·
              refine ⟨7450119571001050432592621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4966746380667366955061747 7450119571001050432592621)
              ·
                refine ⟨2793794839125393912222233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7450119571001050432592621 2793794839125393912222233)
                ·
                  refine ⟨2095346129344045434166675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2793794839125393912222233 2095346129344045434166675)
                  ·
                    refine ⟨3143019194016068151250013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2095346129344045434166675 3143019194016068151250013)
                    ·
                      refine ⟨1178632197756025556718755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3143019194016068151250013 1178632197756025556718755)
                      ·
                        rfl

theorem cell23_2295378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 3, 2, 1, 3].length) (baseStart_2295378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2295378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2295378 prefixEnd_2295378 := by exact prefixLift 2295378
  have htrace : WordTrace (prefixWord ++ tailWord_2295378) baseStart_2295378 baseEnd_2295378 := by
    simpa [prefixWord, tailWord_2295378, baseEnd_2295378] using wordTrace_append hprefix tailTrace_2295378
  have hstable : (prefixWord ++ tailWord_2295378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2295378).length < 2 ^ (prefixWord ++ tailWord_2295378).sum := by decide
  have hdescent : baseEnd_2295378 < baseStart_2295378 := by decide
  rcases family_descends (prefixWord ++ tailWord_2295378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2295388 : List Nat := [2, 2, 4, 1, 2, 2, 1, 1, 3, 3, 2]
def baseStart_2295388 : Nat := 118140960795 + 2295388 * 2 ^ 59
def prefixEnd_2295388 : Nat := 4983230072969 + 3 ^ 40 * 2295388 * 2
def baseEnd_2295388 : Nat := 1178637332562570517593709

theorem tailTrace_2295388 : CollatzResearch.WordTrace tailWord_2295388 prefixEnd_2295388 1178637332562570517593709 := by
  unfold tailWord_2295388
  simp only [CollatzResearch.WordTrace]
  refine ⟨41859839104104385952559409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55813118805472514603412545 41859839104104385952559409)
  ·
    refine ⟨31394879328078289464419557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41859839104104385952559409 31394879328078289464419557)
    ·
      refine ⟨5886539874014679274578667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31394879328078289464419557 5886539874014679274578667)
      ·
        refine ⟨8829809811022018911868001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5886539874014679274578667 8829809811022018911868001)
        ·
          refine ⟨6622357358266514183901001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8829809811022018911868001 6622357358266514183901001)
          ·
            refine ⟨4966768018699885637925751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6622357358266514183901001 4966768018699885637925751)
            ·
              refine ⟨7450152028049828456888627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4966768018699885637925751 7450152028049828456888627)
              ·
                refine ⟨11175228042074742685332941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7450152028049828456888627 11175228042074742685332941)
                ·
                  refine ⟨4190710515778028506999853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11175228042074742685332941 4190710515778028506999853)
                  ·
                    refine ⟨1571516443416760690124945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4190710515778028506999853 1571516443416760690124945)
                    ·
                      refine ⟨1178637332562570517593709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1571516443416760690124945 1178637332562570517593709)
                      ·
                        rfl

theorem cell23_2295388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 1, 3, 3, 2].length) (baseStart_2295388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2295388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2295388 prefixEnd_2295388 := by exact prefixLift 2295388
  have htrace : WordTrace (prefixWord ++ tailWord_2295388) baseStart_2295388 baseEnd_2295388 := by
    simpa [prefixWord, tailWord_2295388, baseEnd_2295388] using wordTrace_append hprefix tailTrace_2295388
  have hstable : (prefixWord ++ tailWord_2295388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2295388).length < 2 ^ (prefixWord ++ tailWord_2295388).sum := by decide
  have hdescent : baseEnd_2295388 < baseStart_2295388 := by decide
  rcases family_descends (prefixWord ++ tailWord_2295388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2295401 : List Nat := [1, 2, 1, 1, 1, 4, 2, 1, 6, 2, 2]
def baseStart_2295401 : Nat := 118140960795 + 2295401 * 2 ^ 59
def prefixEnd_2295401 : Nat := 4983230072969 + 3 ^ 40 * 2295401 * 2
def baseEnd_2295401 : Nat := 1178644007811078966731149

theorem tailTrace_2295401 : CollatzResearch.WordTrace tailWord_2295401 prefixEnd_2295401 1178644007811078966731149 := by
  unfold tailWord_2295401
  simp only [CollatzResearch.WordTrace]
  refine ⟨83720152357161675125342057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55813434904774450083561371 83720152357161675125342057)
  ·
    refine ⟨62790114267871256344006543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83720152357161675125342057 62790114267871256344006543)
    ·
      refine ⟨94185171401806884516009815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62790114267871256344006543 94185171401806884516009815)
      ·
        refine ⟨141277757102710326774014723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94185171401806884516009815 141277757102710326774014723)
        ·
          refine ⟨211916635654065490161022085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141277757102710326774014723 211916635654065490161022085)
          ·
            refine ⟨39734369185137279405191641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 211916635654065490161022085 39734369185137279405191641)
            ·
              refine ⟨29800776888852959553893731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39734369185137279405191641 29800776888852959553893731)
              ·
                refine ⟨44701165333279439330840597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29800776888852959553893731 44701165333279439330840597)
                ·
                  refine ⟨2095367124997473718633153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 44701165333279439330840597 2095367124997473718633153)
                  ·
                    refine ⟨1571525343748105288974865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2095367124997473718633153 1571525343748105288974865)
                    ·
                      refine ⟨1178644007811078966731149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1571525343748105288974865 1178644007811078966731149)
                      ·
                        rfl

theorem cell23_2295401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 6, 2, 2].length) (baseStart_2295401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2295401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2295401 prefixEnd_2295401 := by exact prefixLift 2295401
  have htrace : WordTrace (prefixWord ++ tailWord_2295401) baseStart_2295401 baseEnd_2295401 := by
    simpa [prefixWord, tailWord_2295401, baseEnd_2295401] using wordTrace_append hprefix tailTrace_2295401
  have hstable : (prefixWord ++ tailWord_2295401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2295401).length < 2 ^ (prefixWord ++ tailWord_2295401).sum := by decide
  have hdescent : baseEnd_2295401 < baseStart_2295401 := by decide
  rcases family_descends (prefixWord ++ tailWord_2295401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2295427 : List Nat := [1, 1, 1, 3, 3, 1, 1, 1, 2, 1, 8]
def baseStart_2295427 : Nat := 118140960795 + 2295427 * 2 ^ 59
def prefixEnd_2295427 : Nat := 4983230072969 + 3 ^ 40 * 2295427 * 2
def baseEnd_2295427 : Nat := 1178657358308095865006029

theorem tailTrace_2295427 : CollatzResearch.WordTrace tailWord_2295427 prefixEnd_2295427 1178657358308095865006029 := by
  unfold tailWord_2295427
  simp only [CollatzResearch.WordTrace]
  refine ⟨83721100655067481565788535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55814067103378321043859023 83721100655067481565788535)
  ·
    refine ⟨125581650982601222348682803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83721100655067481565788535 125581650982601222348682803)
    ·
      refine ⟨188372476473901833523024205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125581650982601222348682803 188372476473901833523024205)
      ·
        refine ⟨70639678677713187571134077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 188372476473901833523024205 70639678677713187571134077)
        ·
          refine ⟨26489879504142445339175279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70639678677713187571134077 26489879504142445339175279)
          ·
            refine ⟨39734819256213668008762919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26489879504142445339175279 39734819256213668008762919)
            ·
              refine ⟨59602228884320502013144379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39734819256213668008762919 59602228884320502013144379)
              ·
                refine ⟨89403343326480753019716569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59602228884320502013144379 89403343326480753019716569)
                ·
                  refine ⟨67052507494860564764787427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 89403343326480753019716569 67052507494860564764787427)
                  ·
                    refine ⟨100578761242290847147181141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 67052507494860564764787427 100578761242290847147181141)
                    ·
                      refine ⟨1178657358308095865006029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 100578761242290847147181141 1178657358308095865006029)
                      ·
                        rfl

theorem cell23_2295427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 1, 8].length) (baseStart_2295427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2295427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2295427 prefixEnd_2295427 := by exact prefixLift 2295427
  have htrace : WordTrace (prefixWord ++ tailWord_2295427) baseStart_2295427 baseEnd_2295427 := by
    simpa [prefixWord, tailWord_2295427, baseEnd_2295427] using wordTrace_append hprefix tailTrace_2295427
  have hstable : (prefixWord ++ tailWord_2295427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2295427).length < 2 ^ (prefixWord ++ tailWord_2295427).sum := by decide
  have hdescent : baseEnd_2295427 < baseStart_2295427 := by decide
  rcases family_descends (prefixWord ++ tailWord_2295427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2295511 : List Nat := [1, 1, 3, 2, 1, 3, 2, 3, 2, 2, 3]
def baseStart_2295511 : Nat := 118140960795 + 2295511 * 2 ^ 59
def prefixEnd_2295511 : Nat := 4983230072969 + 3 ^ 40 * 2295511 * 2
def baseEnd_2295511 : Nat := 1178700490683073536355643

theorem tailTrace_2295511 : CollatzResearch.WordTrace tailWord_2295511 prefixEnd_2295511 1178700490683073536355643 := by
  unfold tailWord_2295511
  simp only [CollatzResearch.WordTrace]
  refine ⟨83724164386763163911846387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55816109591175442607897591 83724164386763163911846387)
  ·
    refine ⟨125586246580144745867769581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83724164386763163911846387 125586246580144745867769581)
    ·
      refine ⟨47094842467554279700413593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 125586246580144745867769581 47094842467554279700413593)
      ·
        refine ⟨35321131850665709775310195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47094842467554279700413593 35321131850665709775310195)
        ·
          refine ⟨52981697775998564662965293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35321131850665709775310195 52981697775998564662965293)
          ·
            refine ⟨19868136665999461748611985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52981697775998564662965293 19868136665999461748611985)
            ·
              refine ⟨14901102499499596311458989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19868136665999461748611985 14901102499499596311458989)
              ·
                refine ⟨5587913437312348616797121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14901102499499596311458989 5587913437312348616797121)
                ·
                  refine ⟨4190935077984261462597841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5587913437312348616797121 4190935077984261462597841)
                  ·
                    refine ⟨3143201308488196096948381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4190935077984261462597841 3143201308488196096948381)
                    ·
                      refine ⟨1178700490683073536355643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3143201308488196096948381 1178700490683073536355643)
                      ·
                        rfl

theorem cell23_2295511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 3, 2, 2, 3].length) (baseStart_2295511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2295511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2295511 prefixEnd_2295511 := by exact prefixLift 2295511
  have htrace : WordTrace (prefixWord ++ tailWord_2295511) baseStart_2295511 baseEnd_2295511 := by
    simpa [prefixWord, tailWord_2295511, baseEnd_2295511] using wordTrace_append hprefix tailTrace_2295511
  have hstable : (prefixWord ++ tailWord_2295511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2295511).length < 2 ^ (prefixWord ++ tailWord_2295511).sum := by decide
  have hdescent : baseEnd_2295511 < baseStart_2295511 := by decide
  rcases family_descends (prefixWord ++ tailWord_2295511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2295514 : List Nat := [3, 1, 1, 2, 2, 3, 1, 2, 8]
def baseStart_2295514 : Nat := 118140960795 + 2295514 * 2 ^ 59
def prefixEnd_2295514 : Nat := 4983230072969 + 3 ^ 40 * 2295514 * 2
def baseEnd_2295514 : Nat := 130966892347226336068681

theorem tailTrace_2295514 : CollatzResearch.WordTrace tailWord_2295514 prefixEnd_2295514 130966892347226336068681 := by
  unfold tailWord_2295514
  simp only [CollatzResearch.WordTrace]
  refine ⟨20931068451438073856051399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55816182537168196949470397 20931068451438073856051399)
  ·
    refine ⟨31396602677157110784077099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20931068451438073856051399 31396602677157110784077099)
    ·
      refine ⟨47094904015735666176115649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31396602677157110784077099 47094904015735666176115649)
      ·
        refine ⟨35321178011801749632086737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47094904015735666176115649 35321178011801749632086737)
        ·
          refine ⟨26490883508851312224065053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35321178011801749632086737 26490883508851312224065053)
          ·
            refine ⟨9934081315819242084024395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26490883508851312224065053 9934081315819242084024395)
            ·
              refine ⟨14901121973728863126036593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9934081315819242084024395 14901121973728863126036593)
              ·
                refine ⟨11175841480296647344527445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14901121973728863126036593 11175841480296647344527445)
                ·
                  refine ⟨130966892347226336068681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11175841480296647344527445 130966892347226336068681)
                  ·
                    rfl

theorem cell23_2295514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 2, 8].length) (baseStart_2295514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2295514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2295514 prefixEnd_2295514 := by exact prefixLift 2295514
  have htrace : WordTrace (prefixWord ++ tailWord_2295514) baseStart_2295514 baseEnd_2295514 := by
    simpa [prefixWord, tailWord_2295514, baseEnd_2295514] using wordTrace_append hprefix tailTrace_2295514
  have hstable : (prefixWord ++ tailWord_2295514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2295514).length < 2 ^ (prefixWord ++ tailWord_2295514).sum := by decide
  have hdescent : baseEnd_2295514 < baseStart_2295514 := by decide
  rcases family_descends (prefixWord ++ tailWord_2295514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2295528 : List Nat := [2, 1, 4, 1, 3, 2, 1, 2, 2, 2, 3]
def baseStart_2295528 : Nat := 118140960795 + 2295528 * 2 ^ 59
def prefixEnd_2295528 : Nat := 4983230072969 + 3 ^ 40 * 2295528 * 2
def baseEnd_2295528 : Nat := 1178709219854199969843065

theorem tailTrace_2295528 : CollatzResearch.WordTrace tailWord_2295528 prefixEnd_2295528 1178709219854199969843065 := by
  unfold tailWord_2295528
  simp only [CollatzResearch.WordTrace]
  refine ⟨41862392213850787907607619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55816522951801050543476825 41862392213850787907607619)
  ·
    refine ⟨62793588320776181861411429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41862392213850787907607619 62793588320776181861411429)
    ·
      refine ⟨11773797810145534099014643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62793588320776181861411429 11773797810145534099014643)
      ·
        refine ⟨17660696715218301148521965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11773797810145534099014643 17660696715218301148521965)
        ·
          refine ⟨6622761268206862930695737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17660696715218301148521965 6622761268206862930695737)
          ·
            refine ⟨4967070951155147198021803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6622761268206862930695737 4967070951155147198021803)
            ·
              refine ⟨7450606426732720797032705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4967070951155147198021803 7450606426732720797032705)
              ·
                refine ⟨5587954820049540597774529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7450606426732720797032705 5587954820049540597774529)
                ·
                  refine ⟨4190966115037155448330897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5587954820049540597774529 4190966115037155448330897)
                  ·
                    refine ⟨3143224586277866586248173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4190966115037155448330897 3143224586277866586248173)
                    ·
                      refine ⟨1178709219854199969843065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3143224586277866586248173 1178709219854199969843065)
                      ·
                        rfl

theorem cell23_2295528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 2, 2, 2, 3].length) (baseStart_2295528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2295528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2295528 prefixEnd_2295528 := by exact prefixLift 2295528
  have htrace : WordTrace (prefixWord ++ tailWord_2295528) baseStart_2295528 baseEnd_2295528 := by
    simpa [prefixWord, tailWord_2295528, baseEnd_2295528] using wordTrace_append hprefix tailTrace_2295528
  have hstable : (prefixWord ++ tailWord_2295528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2295528).length < 2 ^ (prefixWord ++ tailWord_2295528).sum := by decide
  have hdescent : baseEnd_2295528 < baseStart_2295528 := by decide
  rcases family_descends (prefixWord ++ tailWord_2295528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2295535 : List Nat := [1, 1, 2, 1, 5, 1, 5, 2, 1, 4]
def baseStart_2295535 : Nat := 118140960795 + 2295535 * 2 ^ 59
def prefixEnd_2295535 : Nat := 4983230072969 + 3 ^ 40 * 2295535 * 2
def baseEnd_2295535 : Nat := 392904271406260480818511

theorem tailTrace_2295535 : CollatzResearch.WordTrace tailWord_2295535 prefixEnd_2295535 392904271406260480818511 := by
  unfold tailWord_2295535
  simp only [CollatzResearch.WordTrace]
  refine ⟨83725039738676216010720059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55816693159117477340480039 83725039738676216010720059)
  ·
    refine ⟨125587559608014324016080089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83725039738676216010720059 125587559608014324016080089)
    ·
      refine ⟨94190669706010743012060067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125587559608014324016080089 94190669706010743012060067)
      ·
        refine ⟨141286004559016114518090101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94190669706010743012060067 141286004559016114518090101)
        ·
          refine ⟨13245562927407760736070947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 141286004559016114518090101 13245562927407760736070947)
          ·
            refine ⟨19868344391111641104106421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13245562927407760736070947 19868344391111641104106421)
            ·
              refine ⟨1862657286666716353509977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19868344391111641104106421 1862657286666716353509977)
              ·
                refine ⟨1396992965000037265132483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1862657286666716353509977 1396992965000037265132483)
                ·
                  refine ⟨2095489447500055897698725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1396992965000037265132483 2095489447500055897698725)
                  ·
                    refine ⟨392904271406260480818511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2095489447500055897698725 392904271406260480818511)
                    ·
                      rfl

theorem cell23_2295535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 5, 2, 1, 4].length) (baseStart_2295535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2295535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2295535 prefixEnd_2295535 := by exact prefixLift 2295535
  have htrace : WordTrace (prefixWord ++ tailWord_2295535) baseStart_2295535 baseEnd_2295535 := by
    simpa [prefixWord, tailWord_2295535, baseEnd_2295535] using wordTrace_append hprefix tailTrace_2295535
  have hstable : (prefixWord ++ tailWord_2295535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2295535).length < 2 ^ (prefixWord ++ tailWord_2295535).sum := by decide
  have hdescent : baseEnd_2295535 < baseStart_2295535 := by decide
  rcases family_descends (prefixWord ++ tailWord_2295535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2295551 : List Nat := [1, 1, 2, 2, 1, 3, 2, 1, 3, 5, 2]
def baseStart_2295551 : Nat := 118140960795 + 2295551 * 2 ^ 59
def prefixEnd_2295551 : Nat := 4983230072969 + 3 ^ 40 * 2295551 * 2
def baseEnd_2295551 : Nat := 1178721029909253379855459

theorem tailTrace_2295551 : CollatzResearch.WordTrace tailWord_2295551 prefixEnd_2295551 1178721029909253379855459 := by
  unfold tailWord_2295551
  simp only [CollatzResearch.WordTrace]
  refine ⟨83725623306618250743302507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55817082204412167162201671 83725623306618250743302507)
  ·
    refine ⟨125588434959927376114953761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83725623306618250743302507 125588434959927376114953761)
    ·
      refine ⟨94191326219945532086215321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125588434959927376114953761 94191326219945532086215321)
      ·
        refine ⟨70643494664959149064661491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94191326219945532086215321 70643494664959149064661491)
        ·
          refine ⟨105965241997438723596992237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70643494664959149064661491 105965241997438723596992237)
          ·
            refine ⟨39736965749039521348872089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 105965241997438723596992237 39736965749039521348872089)
            ·
              refine ⟨29802724311779641011654067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39736965749039521348872089 29802724311779641011654067)
              ·
                refine ⟨44704086467669461517481101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29802724311779641011654067 44704086467669461517481101)
                ·
                  refine ⟨16764032425376048069055413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44704086467669461517481101 16764032425376048069055413)
                  ·
                    refine ⟨1571628039879004506473945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16764032425376048069055413 1571628039879004506473945)
                    ·
                      refine ⟨1178721029909253379855459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1571628039879004506473945 1178721029909253379855459)
                      ·
                        rfl

theorem cell23_2295551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 1, 3, 5, 2].length) (baseStart_2295551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2295551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2295551 prefixEnd_2295551 := by exact prefixLift 2295551
  have htrace : WordTrace (prefixWord ++ tailWord_2295551) baseStart_2295551 baseEnd_2295551 := by
    simpa [prefixWord, tailWord_2295551, baseEnd_2295551] using wordTrace_append hprefix tailTrace_2295551
  have hstable : (prefixWord ++ tailWord_2295551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2295551).length < 2 ^ (prefixWord ++ tailWord_2295551).sum := by decide
  have hdescent : baseEnd_2295551 < baseStart_2295551 := by decide
  rcases family_descends (prefixWord ++ tailWord_2295551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2295582 : List Nat := [4, 3, 2, 2, 1, 1, 2, 2, 6]
def baseStart_2295582 : Nat := 118140960795 + 2295582 * 2 ^ 59
def prefixEnd_2295582 : Nat := 4983230072969 + 3 ^ 40 * 2295582 * 2
def baseEnd_2295582 : Nat := 130970771978838084285313

theorem tailTrace_2295582 : CollatzResearch.WordTrace tailWord_2295582 prefixEnd_2295582 130970771978838084285313 := by
  unfold tailWord_2295582
  simp only [CollatzResearch.WordTrace]
  refine ⟨10465844246188242879710125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55817835979670628691787333 10465844246188242879710125)
  ·
    refine ⟨3924691592320591079891297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10465844246188242879710125 3924691592320591079891297)
    ·
      refine ⟨2943518694240443309918473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3924691592320591079891297 2943518694240443309918473)
      ·
        refine ⟨2207639020680332482438855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2943518694240443309918473 2207639020680332482438855)
        ·
          refine ⟨3311458531020498723658283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2207639020680332482438855 3311458531020498723658283)
          ·
            refine ⟨4967187796530748085487425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3311458531020498723658283 4967187796530748085487425)
            ·
              refine ⟨3725390847398061064115569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4967187796530748085487425 3725390847398061064115569)
              ·
                refine ⟨2794043135548545798086677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3725390847398061064115569 2794043135548545798086677)
                ·
                  refine ⟨130970771978838084285313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2794043135548545798086677 130970771978838084285313)
                  ·
                    rfl

theorem cell23_2295582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 2, 2, 6].length) (baseStart_2295582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2295582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2295582 prefixEnd_2295582 := by exact prefixLift 2295582
  have htrace : WordTrace (prefixWord ++ tailWord_2295582) baseStart_2295582 baseEnd_2295582 := by
    simpa [prefixWord, tailWord_2295582, baseEnd_2295582] using wordTrace_append hprefix tailTrace_2295582
  have hstable : (prefixWord ++ tailWord_2295582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2295582).length < 2 ^ (prefixWord ++ tailWord_2295582).sum := by decide
  have hdescent : baseEnd_2295582 < baseStart_2295582 := by decide
  rcases family_descends (prefixWord ++ tailWord_2295582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2295592 : List Nat := [2, 1, 5, 1, 1, 3, 1, 4, 1, 1, 3]
def baseStart_2295592 : Nat := 118140960795 + 2295592 * 2 ^ 59
def prefixEnd_2295592 : Nat := 4983230072969 + 3 ^ 40 * 2295592 * 2
def baseEnd_2295592 : Nat := 1178742082616087719442771

theorem tailTrace_2295592 : CollatzResearch.WordTrace tailWord_2295592 prefixEnd_2295592 1178742082616087719442771 := by
  unfold tailWord_2295592
  simp only [CollatzResearch.WordTrace]
  refine ⟨41863559349734857372772515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55818079132979809830363353 41863559349734857372772515)
  ·
    refine ⟨62795339024602286059158773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41863559349734857372772515 62795339024602286059158773)
    ·
      refine ⟨5887063033556464318046135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 62795339024602286059158773 5887063033556464318046135)
      ·
        refine ⟨8830594550334696477069203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5887063033556464318046135 8830594550334696477069203)
        ·
          refine ⟨13245891825502044715603805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8830594550334696477069203 13245891825502044715603805)
          ·
            refine ⟨4967209434563266768351427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13245891825502044715603805 4967209434563266768351427)
            ·
              refine ⟨7450814151844900152527141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4967209434563266768351427 7450814151844900152527141)
              ·
                refine ⟨1397027653470918778598839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7450814151844900152527141 1397027653470918778598839)
                ·
                  refine ⟨2095541480206378167898259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1397027653470918778598839 2095541480206378167898259)
                  ·
                    refine ⟨3143312220309567251847389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2095541480206378167898259 3143312220309567251847389)
                    ·
                      refine ⟨1178742082616087719442771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3143312220309567251847389 1178742082616087719442771)
                      ·
                        rfl

theorem cell23_2295592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 4, 1, 1, 3].length) (baseStart_2295592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2295592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2295592 prefixEnd_2295592 := by exact prefixLift 2295592
  have htrace : WordTrace (prefixWord ++ tailWord_2295592) baseStart_2295592 baseEnd_2295592 := by
    simpa [prefixWord, tailWord_2295592, baseEnd_2295592] using wordTrace_append hprefix tailTrace_2295592
  have hstable : (prefixWord ++ tailWord_2295592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2295592).length < 2 ^ (prefixWord ++ tailWord_2295592).sum := by decide
  have hdescent : baseEnd_2295592 < baseStart_2295592 := by decide
  rcases family_descends (prefixWord ++ tailWord_2295592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2295608 : List Nat := [2, 1, 2, 1, 3, 3, 2, 3, 2, 4]
def baseStart_2295608 : Nat := 118140960795 + 2295608 * 2 ^ 59
def prefixEnd_2295608 : Nat := 4983230072969 + 3 ^ 40 * 2295608 * 2
def baseEnd_2295608 : Nat := 392916766102186552280899

theorem tailTrace_2295608 : CollatzResearch.WordTrace tailWord_2295608 prefixEnd_2295608 392916766102186552280899 := by
  unfold tailWord_2295608
  simp only [CollatzResearch.WordTrace]
  refine ⟨41863851133705874739063739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55818468178274499652084985 41863851133705874739063739)
  ·
    refine ⟨62795776700558812108595609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41863851133705874739063739 62795776700558812108595609)
    ·
      refine ⟨47096832525419109081446707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62795776700558812108595609 47096832525419109081446707)
      ·
        refine ⟨70645248788128663622170061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47096832525419109081446707 70645248788128663622170061)
        ·
          refine ⟨26491968295548248858313773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70645248788128663622170061 26491968295548248858313773)
          ·
            refine ⟨9934488110830593321867665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26491968295548248858313773 9934488110830593321867665)
            ·
              refine ⟨7450866083122944991400749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9934488110830593321867665 7450866083122944991400749)
              ·
                refine ⟨2794074781171104371775281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7450866083122944991400749 2794074781171104371775281)
                ·
                  refine ⟨2095556085878328278831461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2794074781171104371775281 2095556085878328278831461)
                  ·
                    refine ⟨392916766102186552280899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2095556085878328278831461 392916766102186552280899)
                    ·
                      rfl

theorem cell23_2295608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 3, 2, 4].length) (baseStart_2295608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2295608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2295608 prefixEnd_2295608 := by exact prefixLift 2295608
  have htrace : WordTrace (prefixWord ++ tailWord_2295608) baseStart_2295608 baseEnd_2295608 := by
    simpa [prefixWord, tailWord_2295608, baseEnd_2295608] using wordTrace_append hprefix tailTrace_2295608
  have hstable : (prefixWord ++ tailWord_2295608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2295608).length < 2 ^ (prefixWord ++ tailWord_2295608).sum := by decide
  have hdescent : baseEnd_2295608 < baseStart_2295608 := by decide
  rcases family_descends (prefixWord ++ tailWord_2295608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2295621 : List Nat := [1, 3, 1, 1, 1, 2, 7, 7]
def baseStart_2295621 : Nat := 118140960795 + 2295621 * 2 ^ 59
def prefixEnd_2295621 : Nat := 4983230072969 + 3 ^ 40 * 2295621 * 2
def baseEnd_2295621 : Nat := 43657665687224744665931

theorem tailTrace_2295621 : CollatzResearch.WordTrace tailWord_2295621 prefixEnd_2295621 43657665687224744665931 := by
  unfold tailWord_2295621
  simp only [CollatzResearch.WordTrace]
  refine ⟨83728176416364652698350717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55818784277576435132233811 83728176416364652698350717)
  ·
    refine ⟨31398066156136744761881519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83728176416364652698350717 31398066156136744761881519)
    ·
      refine ⟨47097099234205117142822279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31398066156136744761881519 47097099234205117142822279)
      ·
        refine ⟨70645648851307675714233419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47097099234205117142822279 70645648851307675714233419)
        ·
          refine ⟨105968473276961513571350129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70645648851307675714233419 105968473276961513571350129)
          ·
            refine ⟨79476354957721135178512597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105968473276961513571350129 79476354957721135178512597)
            ·
              refine ⟨1862727069321589105746389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 79476354957721135178512597 1862727069321589105746389)
              ·
                refine ⟨43657665687224744665931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1862727069321589105746389 43657665687224744665931)
                ·
                  rfl

theorem cell23_2295621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 7, 7].length) (baseStart_2295621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2295621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2295621 prefixEnd_2295621 := by exact prefixLift 2295621
  have htrace : WordTrace (prefixWord ++ tailWord_2295621) baseStart_2295621 baseEnd_2295621 := by
    simpa [prefixWord, tailWord_2295621, baseEnd_2295621] using wordTrace_append hprefix tailTrace_2295621
  have hstable : (prefixWord ++ tailWord_2295621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2295621).length < 2 ^ (prefixWord ++ tailWord_2295621).sum := by decide
  have hdescent : baseEnd_2295621 < baseStart_2295621 := by decide
  rcases family_descends (prefixWord ++ tailWord_2295621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2295691 : List Nat := [1, 1, 1, 1, 4, 2, 1, 2, 1, 6, 3]
def baseStart_2295691 : Nat := 118140960795 + 2295691 * 2 ^ 59
def prefixEnd_2295691 : Nat := 4983230072969 + 3 ^ 40 * 2295691 * 2
def baseEnd_2295691 : Nat := 1178792917200882832104815

theorem tailTrace_2295691 : CollatzResearch.WordTrace tailWord_2295691 prefixEnd_2295691 1178792917200882832104815 := by
  unfold tailWord_2295691
  simp only [CollatzResearch.WordTrace]
  refine ⟨83730729526111054653398927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55820486350740703102265951 83730729526111054653398927)
  ·
    refine ⟨125596094289166581980098391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83730729526111054653398927 125596094289166581980098391)
    ·
      refine ⟨188394141433749872970147587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125596094289166581980098391 188394141433749872970147587)
      ·
        refine ⟨282591212150624809455221381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188394141433749872970147587 282591212150624809455221381)
        ·
          refine ⟨52985852278242151772854009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 282591212150624809455221381 52985852278242151772854009)
          ·
            refine ⟨39739389208681613829640507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52985852278242151772854009 39739389208681613829640507)
            ·
              refine ⟨59609083813022420744460761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39739389208681613829640507 59609083813022420744460761)
              ·
                refine ⟨44706812859766815558345571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59609083813022420744460761 44706812859766815558345571)
                ·
                  refine ⟨67060219289650223337518357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44706812859766815558345571 67060219289650223337518357)
                  ·
                    refine ⟨3143447779202354218946173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 67060219289650223337518357 3143447779202354218946173)
                    ·
                      refine ⟨1178792917200882832104815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3143447779202354218946173 1178792917200882832104815)
                      ·
                        rfl

theorem cell23_2295691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 2, 1, 6, 3].length) (baseStart_2295691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2295691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2295691 prefixEnd_2295691 := by exact prefixLift 2295691
  have htrace : WordTrace (prefixWord ++ tailWord_2295691) baseStart_2295691 baseEnd_2295691 := by
    simpa [prefixWord, tailWord_2295691, baseEnd_2295691] using wordTrace_append hprefix tailTrace_2295691
  have hstable : (prefixWord ++ tailWord_2295691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2295691).length < 2 ^ (prefixWord ++ tailWord_2295691).sum := by decide
  have hdescent : baseEnd_2295691 < baseStart_2295691 := by decide
  rcases family_descends (prefixWord ++ tailWord_2295691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2295705 : List Nat := [1, 2, 1, 2, 1, 3, 4, 1, 4, 2, 2]
def baseStart_2295705 : Nat := 118140960795 + 2295705 * 2 ^ 59
def prefixEnd_2295705 : Nat := 4983230072969 + 3 ^ 40 * 2295705 * 2
def baseEnd_2295705 : Nat := 1178800105930045777329751

theorem tailTrace_2295705 : CollatzResearch.WordTrace tailWord_2295705 prefixEnd_2295705 1178800105930045777329751 := by
  unfold tailWord_2295705
  simp only [CollatzResearch.WordTrace]
  refine ⟨83731240148060335044408569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55820826765373556696272379 83731240148060335044408569)
  ·
    refine ⟨62798430111045251283306427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83731240148060335044408569 62798430111045251283306427)
    ·
      refine ⟨94197645166567876924959641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62798430111045251283306427 94197645166567876924959641)
      ·
        refine ⟨70648233874925907693719731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94197645166567876924959641 70648233874925907693719731)
        ·
          refine ⟨105972350812388861540579597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70648233874925907693719731 105972350812388861540579597)
          ·
            refine ⟨39739631554645823077717349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 105972350812388861540579597 39739631554645823077717349)
            ·
              refine ⟨7451180916496091827072003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39739631554645823077717349 7451180916496091827072003)
              ·
                refine ⟨11176771374744137740608005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7451180916496091827072003 11176771374744137740608005)
                ·
                  refine ⟨2095644632764525826364001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11176771374744137740608005 2095644632764525826364001)
                  ·
                    refine ⟨1571733474573394369773001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2095644632764525826364001 1571733474573394369773001)
                    ·
                      refine ⟨1178800105930045777329751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1571733474573394369773001 1178800105930045777329751)
                      ·
                        rfl

theorem cell23_2295705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 1, 4, 2, 2].length) (baseStart_2295705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2295705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2295705 prefixEnd_2295705 := by exact prefixLift 2295705
  have htrace : WordTrace (prefixWord ++ tailWord_2295705) baseStart_2295705 baseEnd_2295705 := by
    simpa [prefixWord, tailWord_2295705, baseEnd_2295705] using wordTrace_append hprefix tailTrace_2295705
  have hstable : (prefixWord ++ tailWord_2295705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2295705).length < 2 ^ (prefixWord ++ tailWord_2295705).sum := by decide
  have hdescent : baseEnd_2295705 < baseStart_2295705 := by decide
  rcases family_descends (prefixWord ++ tailWord_2295705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2295726 : List Nat := [4, 1, 5, 1, 1, 1, 1, 1, 3, 3, 2]
def baseStart_2295726 : Nat := 118140960795 + 2295726 * 2 ^ 59
def prefixEnd_2295726 : Nat := 4983230072969 + 3 ^ 40 * 2295726 * 2
def baseEnd_2295726 : Nat := 1178810889023790195167155

theorem tailTrace_2295726 : CollatzResearch.WordTrace tailWord_2295726 prefixEnd_2295726 1178810889023790195167155 := by
  unfold tailWord_2295726
  simp only [CollatzResearch.WordTrace]
  refine ⟨10466500760123031953865379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55821337387322837087282021 10466500760123031953865379)
  ·
    refine ⟨15699751140184547930798069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10466500760123031953865379 15699751140184547930798069)
    ·
      refine ⟨1471851669392301368512319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15699751140184547930798069 1471851669392301368512319)
      ·
        refine ⟨2207777504088452052768479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1471851669392301368512319 2207777504088452052768479)
        ·
          refine ⟨3311666256132678079152719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2207777504088452052768479 3311666256132678079152719)
          ·
            refine ⟨4967499384199017118729079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3311666256132678079152719 4967499384199017118729079)
            ·
              refine ⟨7451249076298525678093619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4967499384199017118729079 7451249076298525678093619)
              ·
                refine ⟨11176873614447788517140429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7451249076298525678093619 11176873614447788517140429)
                ·
                  refine ⟨4191327605417920693927661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11176873614447788517140429 4191327605417920693927661)
                  ·
                    refine ⟨1571747852031720260222873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4191327605417920693927661 1571747852031720260222873)
                    ·
                      refine ⟨1178810889023790195167155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1571747852031720260222873 1178810889023790195167155)
                      ·
                        rfl

theorem cell23_2295726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_2295726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2295726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2295726 prefixEnd_2295726 := by exact prefixLift 2295726
  have htrace : WordTrace (prefixWord ++ tailWord_2295726) baseStart_2295726 baseEnd_2295726 := by
    simpa [prefixWord, tailWord_2295726, baseEnd_2295726] using wordTrace_append hprefix tailTrace_2295726
  have hstable : (prefixWord ++ tailWord_2295726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2295726).length < 2 ^ (prefixWord ++ tailWord_2295726).sum := by decide
  have hdescent : baseEnd_2295726 < baseStart_2295726 := by decide
  rcases family_descends (prefixWord ++ tailWord_2295726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2295758 : List Nat := [4, 1, 1, 1, 2, 2, 1, 4, 2, 5]
def baseStart_2295758 : Nat := 118140960795 + 2295758 * 2 ^ 59
def prefixEnd_2295758 : Nat := 4983230072969 + 3 ^ 40 * 2295758 * 2
def baseEnd_2295758 : Nat := 392942440134911356655669

theorem tailTrace_2295758 : CollatzResearch.WordTrace tailWord_2295758 prefixEnd_2295758 392942440134911356655669 := by
  unfold tailWord_2295758
  simp only [CollatzResearch.WordTrace]
  refine ⟨10466646652108540637010991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55822115477912216730725285 10466646652108540637010991)
  ·
    refine ⟨15699969978162810955516487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10466646652108540637010991 15699969978162810955516487)
    ·
      refine ⟨23549954967244216433274731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15699969978162810955516487 23549954967244216433274731)
      ·
        refine ⟨35324932450866324649912097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23549954967244216433274731 35324932450866324649912097)
        ·
          refine ⟨26493699338149743487434073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35324932450866324649912097 26493699338149743487434073)
          ·
            refine ⟨19870274503612307615575555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26493699338149743487434073 19870274503612307615575555)
            ·
              refine ⟨29805411755418461423363333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19870274503612307615575555 29805411755418461423363333)
              ·
                refine ⟨5588514704140961516880625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29805411755418461423363333 5588514704140961516880625)
                ·
                  refine ⟨4191386028105721137660469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5588514704140961516880625 4191386028105721137660469)
                  ·
                    refine ⟨392942440134911356655669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4191386028105721137660469 392942440134911356655669)
                    ·
                      rfl

theorem cell23_2295758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 4, 2, 5].length) (baseStart_2295758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2295758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2295758 prefixEnd_2295758 := by exact prefixLift 2295758
  have htrace : WordTrace (prefixWord ++ tailWord_2295758) baseStart_2295758 baseEnd_2295758 := by
    simpa [prefixWord, tailWord_2295758, baseEnd_2295758] using wordTrace_append hprefix tailTrace_2295758
  have hstable : (prefixWord ++ tailWord_2295758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2295758).length < 2 ^ (prefixWord ++ tailWord_2295758).sum := by decide
  have hdescent : baseEnd_2295758 < baseStart_2295758 := by decide
  rcases family_descends (prefixWord ++ tailWord_2295758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2295762 : List Nat := [3, 2, 2, 3, 2, 1, 1, 4, 5]
def baseStart_2295762 : Nat := 118140960795 + 2295762 * 2 ^ 59
def prefixEnd_2295762 : Nat := 4983230072969 + 3 ^ 40 * 2295762 * 2
def baseEnd_2295762 : Nat := 130981041591928006035221

theorem tailTrace_2295762 : CollatzResearch.WordTrace tailWord_2295762 prefixEnd_2295762 130981041591928006035221 := by
  unfold tailWord_2295762
  simp only [CollatzResearch.WordTrace]
  refine ⟨20933329777213458444808385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55822212739235889186155693 20933329777213458444808385)
  ·
    refine ⟨15699997332910093833606289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20933329777213458444808385 15699997332910093833606289)
    ·
      refine ⟨11774997999682570375204717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15699997332910093833606289 11774997999682570375204717)
      ·
        refine ⟨4415624249880963890701769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11774997999682570375204717 4415624249880963890701769)
        ·
          refine ⟨3311718187410722918026327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4415624249880963890701769 3311718187410722918026327)
          ·
            refine ⟨4967577281116084377039491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3311718187410722918026327 4967577281116084377039491)
            ·
              refine ⟨7451365921674126565559237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4967577281116084377039491 7451365921674126565559237)
              ·
                refine ⟨1397131110313898731042357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7451365921674126565559237 1397131110313898731042357)
                ·
                  refine ⟨130981041591928006035221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1397131110313898731042357 130981041591928006035221)
                  ·
                    rfl

theorem cell23_2295762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 4, 5].length) (baseStart_2295762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2295762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2295762 prefixEnd_2295762 := by exact prefixLift 2295762
  have htrace : WordTrace (prefixWord ++ tailWord_2295762) baseStart_2295762 baseEnd_2295762 := by
    simpa [prefixWord, tailWord_2295762, baseEnd_2295762] using wordTrace_append hprefix tailTrace_2295762
  have hstable : (prefixWord ++ tailWord_2295762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2295762).length < 2 ^ (prefixWord ++ tailWord_2295762).sum := by decide
  have hdescent : baseEnd_2295762 < baseStart_2295762 := by decide
  rcases family_descends (prefixWord ++ tailWord_2295762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2295765 : List Nat := [1, 3, 2, 3, 2, 1, 1, 1, 2, 5, 2]
def baseStart_2295765 : Nat := 118140960795 + 2295765 * 2 ^ 59
def prefixEnd_2295765 : Nat := 4983230072969 + 3 ^ 40 * 2295765 * 2
def baseEnd_2295765 : Nat := 1178830914769315542579475

theorem tailTrace_2295765 : CollatzResearch.WordTrace tailWord_2295765 prefixEnd_2295765 1178830914769315542579475 := by
  unfold tailWord_2295765
  simp only [CollatzResearch.WordTrace]
  refine ⟨83733428527842965291592749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55822285685228643527728499 83733428527842965291592749)
  ·
    refine ⟨31400035697941111984347281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83733428527842965291592749 31400035697941111984347281)
    ·
      refine ⟨23550026773455833988260461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31400035697941111984347281 23550026773455833988260461)
      ·
        refine ⟨8831260040045937745597673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23550026773455833988260461 8831260040045937745597673)
        ·
          refine ⟨6623445030034453309198255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8831260040045937745597673 6623445030034453309198255)
          ·
            refine ⟨9935167545051679963797383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6623445030034453309198255 9935167545051679963797383)
            ·
              refine ⟨14902751317577519945696075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9935167545051679963797383 14902751317577519945696075)
              ·
                refine ⟨22354126976366279918544113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14902751317577519945696075 22354126976366279918544113)
                ·
                  refine ⟨16765595232274709938908085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22354126976366279918544113 16765595232274709938908085)
                  ·
                    refine ⟨1571774553025754056772633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16765595232274709938908085 1571774553025754056772633)
                    ·
                      refine ⟨1178830914769315542579475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1571774553025754056772633 1178830914769315542579475)
                      ·
                        rfl

theorem cell23_2295765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 1, 2, 5, 2].length) (baseStart_2295765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2295765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2295765 prefixEnd_2295765 := by exact prefixLift 2295765
  have htrace : WordTrace (prefixWord ++ tailWord_2295765) baseStart_2295765 baseEnd_2295765 := by
    simpa [prefixWord, tailWord_2295765, baseEnd_2295765] using wordTrace_append hprefix tailTrace_2295765
  have hstable : (prefixWord ++ tailWord_2295765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2295765).length < 2 ^ (prefixWord ++ tailWord_2295765).sum := by decide
  have hdescent : baseEnd_2295765 < baseStart_2295765 := by decide
  rcases family_descends (prefixWord ++ tailWord_2295765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2295822 : List Nat := [4, 1, 1, 2, 2, 1, 1, 6, 1, 4]
def baseStart_2295822 : Nat := 118140960795 + 2295822 * 2 ^ 59
def prefixEnd_2295822 : Nat := 4983230072969 + 3 ^ 40 * 2295822 * 2
def baseEnd_2295822 : Nat := 392953394388873939855571

theorem tailTrace_2295822 : CollatzResearch.WordTrace tailWord_2295822 prefixEnd_2295822 392953394388873939855571 := by
  unfold tailWord_2295822
  simp only [CollatzResearch.WordTrace]
  refine ⟨10466938436079558003302215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55823671659090976017611813 10466938436079558003302215)
  ·
    refine ⟨15700407654119337004953323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10466938436079558003302215 15700407654119337004953323)
    ·
      refine ⟨23550611481179005507429985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15700407654119337004953323 23550611481179005507429985)
      ·
        refine ⟨17662958610884254130572489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23550611481179005507429985 17662958610884254130572489)
        ·
          refine ⟨13247218958163190597929367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17662958610884254130572489 13247218958163190597929367)
          ·
            refine ⟨19870828437244785896894051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13247218958163190597929367 19870828437244785896894051)
            ·
              refine ⟨29806242655867178845341077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19870828437244785896894051 29806242655867178845341077)
              ·
                refine ⟨1397167624493774008375363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 29806242655867178845341077 1397167624493774008375363)
                ·
                  refine ⟨2095751436740661012563045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1397167624493774008375363 2095751436740661012563045)
                  ·
                    refine ⟨392953394388873939855571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2095751436740661012563045 392953394388873939855571)
                    ·
                      rfl

theorem cell23_2295822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 6, 1, 4].length) (baseStart_2295822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2295822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2295822 prefixEnd_2295822 := by exact prefixLift 2295822
  have htrace : WordTrace (prefixWord ++ tailWord_2295822) baseStart_2295822 baseEnd_2295822 := by
    simpa [prefixWord, tailWord_2295822, baseEnd_2295822] using wordTrace_append hprefix tailTrace_2295822
  have hstable : (prefixWord ++ tailWord_2295822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2295822).length < 2 ^ (prefixWord ++ tailWord_2295822).sum := by decide
  have hdescent : baseEnd_2295822 < baseStart_2295822 := by decide
  rcases family_descends (prefixWord ++ tailWord_2295822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2295872 : List Nat := [2, 1, 1, 2, 2, 5, 1, 2, 2, 3, 2]
def baseStart_2295872 : Nat := 118140960795 + 2295872 * 2 ^ 59
def prefixEnd_2295872 : Nat := 4983230072969 + 3 ^ 40 * 2295872 * 2
def baseEnd_2295872 : Nat := 1178885857199346623941483

theorem tailTrace_2295872 : CollatzResearch.WordTrace tailWord_2295872 prefixEnd_2295872 1178885857199346623941483 := by
  unfold tailWord_2295872
  simp only [CollatzResearch.WordTrace]
  refine ⟨41868665569227661282868935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55824887425636881710491913 41868665569227661282868935)
  ·
    refine ⟨62802998353841491924303403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41868665569227661282868935 62802998353841491924303403)
    ·
      refine ⟨94204497530762237886455105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62802998353841491924303403 94204497530762237886455105)
      ·
        refine ⟨70653373148071678414841329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94204497530762237886455105 70653373148071678414841329)
        ·
          refine ⟨52990029861053758811130997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70653373148071678414841329 52990029861053758811130997)
          ·
            refine ⟨4967815299473789888543531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 52990029861053758811130997 4967815299473789888543531)
            ·
              refine ⟨7451722949210684832815297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4967815299473789888543531 7451722949210684832815297)
              ·
                refine ⟨5588792211908013624611473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7451722949210684832815297 5588792211908013624611473)
                ·
                  refine ⟨4191594158931010218458605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5588792211908013624611473 4191594158931010218458605)
                  ·
                    refine ⟨1571847809599128831921977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4191594158931010218458605 1571847809599128831921977)
                    ·
                      refine ⟨1178885857199346623941483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1571847809599128831921977 1178885857199346623941483)
                      ·
                        rfl

theorem cell23_2295872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 2, 2, 3, 2].length) (baseStart_2295872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2295872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2295872 prefixEnd_2295872 := by exact prefixLift 2295872
  have htrace : WordTrace (prefixWord ++ tailWord_2295872) baseStart_2295872 baseEnd_2295872 := by
    simpa [prefixWord, tailWord_2295872, baseEnd_2295872] using wordTrace_append hprefix tailTrace_2295872
  have hstable : (prefixWord ++ tailWord_2295872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2295872).length < 2 ^ (prefixWord ++ tailWord_2295872).sum := by decide
  have hdescent : baseEnd_2295872 < baseStart_2295872 := by decide
  rcases family_descends (prefixWord ++ tailWord_2295872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2295888 : List Nat := [2, 1, 1, 1, 1, 3, 1, 1, 1, 8, 3]
def baseStart_2295888 : Nat := 118140960795 + 2295888 * 2 ^ 59
def prefixEnd_2295888 : Nat := 4983230072969 + 3 ^ 40 * 2295888 * 2
def baseEnd_2295888 : Nat := 1178894072889818561341409

theorem tailTrace_2295888 : CollatzResearch.WordTrace tailWord_2295888 prefixEnd_2295888 1178894072889818561341409 := by
  unfold tailWord_2295888
  simp only [CollatzResearch.WordTrace]
  refine ⟨41868957353198678649160159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55825276470931571532213545 41868957353198678649160159)
  ·
    refine ⟨62803436029798017973740239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41868957353198678649160159 62803436029798017973740239)
    ·
      refine ⟨94205154044697026960610359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62803436029798017973740239 94205154044697026960610359)
      ·
        refine ⟨141307731067045540440915539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94205154044697026960610359 141307731067045540440915539)
        ·
          refine ⟨211961596600568310661373309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141307731067045540440915539 211961596600568310661373309)
          ·
            refine ⟨79485598725213116498014991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 211961596600568310661373309 79485598725213116498014991)
            ·
              refine ⟨119228398087819674747022487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79485598725213116498014991 119228398087819674747022487)
              ·
                refine ⟨178842597131729512120533731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 119228398087819674747022487 178842597131729512120533731)
                ·
                  refine ⟨268263895697594268180800597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 178842597131729512120533731 268263895697594268180800597)
                  ·
                    refine ⟨3143717527706182830243757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 268263895697594268180800597 3143717527706182830243757)
                    ·
                      refine ⟨1178894072889818561341409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3143717527706182830243757 1178894072889818561341409)
                      ·
                        rfl

theorem cell23_2295888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 1, 8, 3].length) (baseStart_2295888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2295888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2295888 prefixEnd_2295888 := by exact prefixLift 2295888
  have htrace : WordTrace (prefixWord ++ tailWord_2295888) baseStart_2295888 baseEnd_2295888 := by
    simpa [prefixWord, tailWord_2295888, baseEnd_2295888] using wordTrace_append hprefix tailTrace_2295888
  have hstable : (prefixWord ++ tailWord_2295888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2295888).length < 2 ^ (prefixWord ++ tailWord_2295888).sum := by decide
  have hdescent : baseEnd_2295888 < baseStart_2295888 := by decide
  rcases family_descends (prefixWord ++ tailWord_2295888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2295898 : List Nat := [3, 1, 1, 2, 1, 1, 3, 3, 1, 1, 6]
def baseStart_2295898 : Nat := 118140960795 + 2295898 * 2 ^ 59
def prefixEnd_2295898 : Nat := 4983230072969 + 3 ^ 40 * 2295898 * 2
def baseEnd_2295898 : Nat := 1178899207696363522216363

theorem tailTrace_2295898 : CollatzResearch.WordTrace tailWord_2295898 prefixEnd_2295898 1178899207696363522216363 := by
  unfold tailWord_2295898
  simp only [CollatzResearch.WordTrace]
  refine ⟨20934569859090282251546087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55825519624240752670789565 20934569859090282251546087)
  ·
    refine ⟨31401854788635423377319131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20934569859090282251546087 31401854788635423377319131)
    ·
      refine ⟨47102782182953135065978697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31401854788635423377319131 47102782182953135065978697)
      ·
        refine ⟨35327086637214851299484023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47102782182953135065978697 35327086637214851299484023)
        ·
          refine ⟨52990629955822276949226035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35327086637214851299484023 52990629955822276949226035)
          ·
            refine ⟨79485944933733415423839053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52990629955822276949226035 79485944933733415423839053)
            ·
              refine ⟨29807229350150030783939645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79485944933733415423839053 29807229350150030783939645)
              ·
                refine ⟨11177711006306261543977367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29807229350150030783939645 11177711006306261543977367)
                ·
                  refine ⟨16766566509459392315966051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11177711006306261543977367 16766566509459392315966051)
                  ·
                    refine ⟨25149849764189088473949077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16766566509459392315966051 25149849764189088473949077)
                    ·
                      refine ⟨1178899207696363522216363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25149849764189088473949077 1178899207696363522216363)
                      ·
                        rfl

theorem cell23_2295898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 3, 1, 1, 6].length) (baseStart_2295898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2295898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2295898 prefixEnd_2295898 := by exact prefixLift 2295898
  have htrace : WordTrace (prefixWord ++ tailWord_2295898) baseStart_2295898 baseEnd_2295898 := by
    simpa [prefixWord, tailWord_2295898, baseEnd_2295898] using wordTrace_append hprefix tailTrace_2295898
  have hstable : (prefixWord ++ tailWord_2295898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2295898).length < 2 ^ (prefixWord ++ tailWord_2295898).sum := by decide
  have hdescent : baseEnd_2295898 < baseStart_2295898 := by decide
  rcases family_descends (prefixWord ++ tailWord_2295898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2295906 : List Nat := [3, 3, 2, 2, 2, 1, 2, 1, 2, 3, 2]
def baseStart_2295906 : Nat := 118140960795 + 2295906 * 2 ^ 59
def prefixEnd_2295906 : Nat := 4983230072969 + 3 ^ 40 * 2295906 * 2
def baseEnd_2295906 : Nat := 1178903315541599490916327

theorem tailTrace_2295906 : CollatzResearch.WordTrace tailWord_2295906 prefixEnd_2295906 1178903315541599490916327 := by
  unfold tailWord_2295906
  simp only [CollatzResearch.WordTrace]
  refine ⟨20934642805083036593118893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55825714146888097581650381 20934642805083036593118893)
  ·
    refine ⟨7850491051906138722419585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20934642805083036593118893 7850491051906138722419585)
    ·
      refine ⟨5887868288929604041814689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7850491051906138722419585 5887868288929604041814689)
      ·
        refine ⟨4415901216697203031361017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5887868288929604041814689 4415901216697203031361017)
        ·
          refine ⟨3311925912522902273520763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4415901216697203031361017 3311925912522902273520763)
          ·
            refine ⟨4967888868784353410281145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3311925912522902273520763 4967888868784353410281145)
            ·
              refine ⟨3725916651588265057710859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4967888868784353410281145 3725916651588265057710859)
              ·
                refine ⟨5588874977382397586566289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3725916651588265057710859 5588874977382397586566289)
                ·
                  refine ⟨4191656233036798189924717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5588874977382397586566289 4191656233036798189924717)
                  ·
                    refine ⟨1571871087388799321221769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4191656233036798189924717 1571871087388799321221769)
                    ·
                      refine ⟨1178903315541599490916327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1571871087388799321221769 1178903315541599490916327)
                      ·
                        rfl

theorem cell23_2295906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 2, 1, 2, 3, 2].length) (baseStart_2295906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2295906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2295906 prefixEnd_2295906 := by exact prefixLift 2295906
  have htrace : WordTrace (prefixWord ++ tailWord_2295906) baseStart_2295906 baseEnd_2295906 := by
    simpa [prefixWord, tailWord_2295906, baseEnd_2295906] using wordTrace_append hprefix tailTrace_2295906
  have hstable : (prefixWord ++ tailWord_2295906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2295906).length < 2 ^ (prefixWord ++ tailWord_2295906).sum := by decide
  have hdescent : baseEnd_2295906 < baseStart_2295906 := by decide
  rcases family_descends (prefixWord ++ tailWord_2295906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2295908 : List Nat := [2, 3, 1, 1, 2, 1, 4, 9]
def baseStart_2295908 : Nat := 118140960795 + 2295908 * 2 ^ 59
def prefixEnd_2295908 : Nat := 4983230072969 + 3 ^ 40 * 2295908 * 2
def baseEnd_2295908 : Nat := 43663123796404017892271

theorem tailTrace_2295908 : CollatzResearch.WordTrace tailWord_2295908 prefixEnd_2295908 43663123796404017892271 := by
  unfold tailWord_2295908
  simp only [CollatzResearch.WordTrace]
  refine ⟨41869322083162450357024189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55825762777549933809365585 41869322083162450357024189)
  ·
    refine ⟨15700995781185918883884071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41869322083162450357024189 15700995781185918883884071)
    ·
      refine ⟨23551493671778878325826107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15700995781185918883884071 23551493671778878325826107)
      ·
        refine ⟨35327240507668317488739161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23551493671778878325826107 35327240507668317488739161)
        ·
          refine ⟨26495430380751238116554371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35327240507668317488739161 26495430380751238116554371)
          ·
            refine ⟨39743145571126857174831557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26495430380751238116554371 39743145571126857174831557)
            ·
              refine ⟨7451839794586285720280917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39743145571126857174831557 7451839794586285720280917)
              ·
                refine ⟨43663123796404017892271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7451839794586285720280917 43663123796404017892271)
                ·
                  rfl

theorem cell23_2295908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 9].length) (baseStart_2295908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2295908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2295908 prefixEnd_2295908 := by exact prefixLift 2295908
  have htrace : WordTrace (prefixWord ++ tailWord_2295908) baseStart_2295908 baseEnd_2295908 := by
    simpa [prefixWord, tailWord_2295908, baseEnd_2295908] using wordTrace_append hprefix tailTrace_2295908
  have hstable : (prefixWord ++ tailWord_2295908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2295908).length < 2 ^ (prefixWord ++ tailWord_2295908).sum := by decide
  have hdescent : baseEnd_2295908 < baseStart_2295908 := by decide
  rcases family_descends (prefixWord ++ tailWord_2295908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2295922 : List Nat := [3, 2, 1, 2, 2, 4, 1, 1, 1, 1, 5]
def baseStart_2295922 : Nat := 118140960795 + 2295922 * 2 ^ 59
def prefixEnd_2295922 : Nat := 4983230072969 + 3 ^ 40 * 2295922 * 2
def baseEnd_2295922 : Nat := 1178911531232071428316253

theorem tailTrace_2295922 : CollatzResearch.WordTrace tailWord_2295922 prefixEnd_2295922 1178911531232071428316253 := by
  unfold tailWord_2295922
  simp only [CollatzResearch.WordTrace]
  refine ⟨20934788697068545276264505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55826103192182787403372013 20934788697068545276264505)
  ·
    refine ⟨15701091522801408957198379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20934788697068545276264505 15701091522801408957198379)
    ·
      refine ⟨23551637284202113435797569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15701091522801408957198379 23551637284202113435797569)
      ·
        refine ⟨17663727963151585076848177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23551637284202113435797569 17663727963151585076848177)
        ·
          refine ⟨13247795972363688807636133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17663727963151585076848177 13247795972363688807636133)
          ·
            refine ⟨2483961744818191651431775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13247795972363688807636133 2483961744818191651431775)
            ·
              refine ⟨3725942617227287477147663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2483961744818191651431775 3725942617227287477147663)
              ·
                refine ⟨5588913925840931215721495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3725942617227287477147663 5588913925840931215721495)
                ·
                  refine ⟨8383370888761396823582243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5588913925840931215721495 8383370888761396823582243)
                  ·
                    refine ⟨12575056333142095235373365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8383370888761396823582243 12575056333142095235373365)
                    ·
                      refine ⟨1178911531232071428316253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12575056333142095235373365 1178911531232071428316253)
                      ·
                        rfl

theorem cell23_2295922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 1, 1, 1, 1, 5].length) (baseStart_2295922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2295922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2295922 prefixEnd_2295922 := by exact prefixLift 2295922
  have htrace : WordTrace (prefixWord ++ tailWord_2295922) baseStart_2295922 baseEnd_2295922 := by
    simpa [prefixWord, tailWord_2295922, baseEnd_2295922] using wordTrace_append hprefix tailTrace_2295922
  have hstable : (prefixWord ++ tailWord_2295922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2295922).length < 2 ^ (prefixWord ++ tailWord_2295922).sum := by decide
  have hdescent : baseEnd_2295922 < baseStart_2295922 := by decide
  rcases family_descends (prefixWord ++ tailWord_2295922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2295948 : List Nat := [2, 2, 1, 2, 1, 1, 1, 1, 3, 4, 5]
def baseStart_2295948 : Nat := 118140960795 + 2295948 * 2 ^ 59
def prefixEnd_2295948 : Nat := 4983230072969 + 3 ^ 40 * 2295948 * 2
def baseEnd_2295948 : Nat := 1178924881729088326591133

theorem tailTrace_2295948 : CollatzResearch.WordTrace tailWord_2295948 prefixEnd_2295948 1178924881729088326591133 := by
  unfold tailWord_2295948
  simp only [CollatzResearch.WordTrace]
  refine ⟨41870051543089993772752249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55826735390786658363669665 41870051543089993772752249)
  ·
    refine ⟨31402538657317495329564187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41870051543089993772752249 31402538657317495329564187)
    ·
      refine ⟨47103807985976242994346281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31402538657317495329564187 47103807985976242994346281)
      ·
        refine ⟨35327855989482182245759711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47103807985976242994346281 35327855989482182245759711)
        ·
          refine ⟨52991783984223273368639567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35327855989482182245759711 52991783984223273368639567)
          ·
            refine ⟨79487675976334910052959351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52991783984223273368639567 79487675976334910052959351)
            ·
              refine ⟨119231513964502365079439027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79487675976334910052959351 119231513964502365079439027)
              ·
                refine ⟨178847270946753547619158541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 119231513964502365079439027 178847270946753547619158541)
                ·
                  refine ⟨67067726605032580357184453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 178847270946753547619158541 67067726605032580357184453)
                  ·
                    refine ⟨12575198738443608816972085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 67067726605032580357184453 12575198738443608816972085)
                    ·
                      refine ⟨1178924881729088326591133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12575198738443608816972085 1178924881729088326591133)
                      ·
                        rfl

theorem cell23_2295948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 3, 4, 5].length) (baseStart_2295948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2295948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2295948 prefixEnd_2295948 := by exact prefixLift 2295948
  have htrace : WordTrace (prefixWord ++ tailWord_2295948) baseStart_2295948 baseEnd_2295948 := by
    simpa [prefixWord, tailWord_2295948, baseEnd_2295948] using wordTrace_append hprefix tailTrace_2295948
  have hstable : (prefixWord ++ tailWord_2295948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2295948).length < 2 ^ (prefixWord ++ tailWord_2295948).sum := by decide
  have hdescent : baseEnd_2295948 < baseStart_2295948 := by decide
  rcases family_descends (prefixWord ++ tailWord_2295948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2295952 : List Nat := [2, 1, 1, 1, 1, 1, 5, 5, 2, 1, 3]
def baseStart_2295952 : Nat := 118140960795 + 2295952 * 2 ^ 59
def prefixEnd_2295952 : Nat := 4983230072969 + 3 ^ 40 * 2295952 * 2
def baseEnd_2295952 : Nat := 1178926935651706310941115

theorem tailTrace_2295952 : CollatzResearch.WordTrace tailWord_2295952 prefixEnd_2295952 1178926935651706310941115 := by
  unfold tailWord_2295952
  simp only [CollatzResearch.WordTrace]
  refine ⟨41870124489082748114325055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55826832652110330819100073 41870124489082748114325055)
  ·
    refine ⟨62805186733624122171487583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41870124489082748114325055 62805186733624122171487583)
    ·
      refine ⟨94207780100436183257231375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62805186733624122171487583 94207780100436183257231375)
      ·
        refine ⟨141311670150654274885847063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94207780100436183257231375 141311670150654274885847063)
        ·
          refine ⟨211967505225981412328770595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141311670150654274885847063 211967505225981412328770595)
          ·
            refine ⟨317951257838972118493155893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 211967505225981412328770595 317951257838972118493155893)
            ·
              refine ⟨29807930422403636108733365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 317951257838972118493155893 29807930422403636108733365)
              ·
                refine ⟨2794493477100340885193753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29807930422403636108733365 2794493477100340885193753)
                ·
                  refine ⟨2095870107825255663895315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2794493477100340885193753 2095870107825255663895315)
                  ·
                    refine ⟨3143805161737883495842973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2095870107825255663895315 3143805161737883495842973)
                    ·
                      refine ⟨1178926935651706310941115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3143805161737883495842973 1178926935651706310941115)
                      ·
                        rfl

theorem cell23_2295952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 5, 2, 1, 3].length) (baseStart_2295952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2295952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2295952 prefixEnd_2295952 := by exact prefixLift 2295952
  have htrace : WordTrace (prefixWord ++ tailWord_2295952) baseStart_2295952 baseEnd_2295952 := by
    simpa [prefixWord, tailWord_2295952, baseEnd_2295952] using wordTrace_append hprefix tailTrace_2295952
  have hstable : (prefixWord ++ tailWord_2295952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2295952).length < 2 ^ (prefixWord ++ tailWord_2295952).sum := by decide
  have hdescent : baseEnd_2295952 < baseStart_2295952 := by decide
  rcases family_descends (prefixWord ++ tailWord_2295952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2296005 : List Nat := [1, 3, 1, 1, 1, 1, 6, 1, 2, 2, 4]
def baseStart_2296005 : Nat := 118140960795 + 2296005 * 2 ^ 59
def prefixEnd_2296005 : Nat := 4983230072969 + 3 ^ 40 * 2296005 * 2
def baseEnd_2296005 : Nat := 1178954150126394603578371

theorem tailTrace_2296005 : CollatzResearch.WordTrace tailWord_2296005 prefixEnd_2296005 1178954150126394603578371 := by
  unfold tailWord_2296005
  simp only [CollatzResearch.WordTrace]
  refine ⟨83742182046973486280329469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55828121364648990853552979 83742182046973486280329469)
  ·
    refine ⟨31403318267615057355123551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83742182046973486280329469 31403318267615057355123551)
    ·
      refine ⟨47104977401422586032685327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31403318267615057355123551 47104977401422586032685327)
      ·
        refine ⟨70657466102133879049027991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47104977401422586032685327 70657466102133879049027991)
        ·
          refine ⟨105986199153200818573541987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70657466102133879049027991 105986199153200818573541987)
          ·
            refine ⟨158979298729801227860312981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105986199153200818573541987 158979298729801227860312981)
            ·
              refine ⟨7452154627959432555952171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 158979298729801227860312981 7452154627959432555952171)
              ·
                refine ⟨11178231941939148833928257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7452154627959432555952171 11178231941939148833928257)
                ·
                  refine ⟨8383673956454361625446193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11178231941939148833928257 8383673956454361625446193)
                  ·
                    refine ⟨6287755467340771219084645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8383673956454361625446193 6287755467340771219084645)
                    ·
                      refine ⟨1178954150126394603578371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6287755467340771219084645 1178954150126394603578371)
                      ·
                        rfl

theorem cell23_2296005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 1, 2, 2, 4].length) (baseStart_2296005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2296005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2296005 prefixEnd_2296005 := by exact prefixLift 2296005
  have htrace : WordTrace (prefixWord ++ tailWord_2296005) baseStart_2296005 baseEnd_2296005 := by
    simpa [prefixWord, tailWord_2296005, baseEnd_2296005] using wordTrace_append hprefix tailTrace_2296005
  have hstable : (prefixWord ++ tailWord_2296005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2296005).length < 2 ^ (prefixWord ++ tailWord_2296005).sum := by decide
  have hdescent : baseEnd_2296005 < baseStart_2296005 := by decide
  rcases family_descends (prefixWord ++ tailWord_2296005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2296025 : List Nat := [1, 2, 1, 2, 3, 1, 2, 2, 1, 5, 3]
def baseStart_2296025 : Nat := 118140960795 + 2296025 * 2 ^ 59
def prefixEnd_2296025 : Nat := 4983230072969 + 3 ^ 40 * 2296025 * 2
def baseEnd_2296025 : Nat := 1178964419739484525328279

theorem tailTrace_2296025 : CollatzResearch.WordTrace tailWord_2296025 prefixEnd_2296025 1178964419739484525328279 := by
  unfold tailWord_2296025
  simp only [CollatzResearch.WordTrace]
  refine ⟨83742911506901029696057529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55828607671267353130705019 83742911506901029696057529)
  ·
    refine ⟨62807183630175772272043147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83742911506901029696057529 62807183630175772272043147)
    ·
      refine ⟨94210775445263658408064721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62807183630175772272043147 94210775445263658408064721)
      ·
        refine ⟨70658081583947743806048541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94210775445263658408064721 70658081583947743806048541)
        ·
          refine ⟨26496780593980403927268203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70658081583947743806048541 26496780593980403927268203)
          ·
            refine ⟨39745170890970605890902305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26496780593980403927268203 39745170890970605890902305)
            ·
              refine ⟨29808878168227954418176729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39745170890970605890902305 29808878168227954418176729)
              ·
                refine ⟨22356658626170965813632547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29808878168227954418176729 22356658626170965813632547)
                ·
                  refine ⟨33534987939256448720448821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22356658626170965813632547 33534987939256448720448821)
                  ·
                    refine ⟨3143905119305292067542077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33534987939256448720448821 3143905119305292067542077)
                    ·
                      refine ⟨1178964419739484525328279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3143905119305292067542077 1178964419739484525328279)
                      ·
                        rfl

theorem cell23_2296025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 2, 1, 5, 3].length) (baseStart_2296025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2296025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2296025 prefixEnd_2296025 := by exact prefixLift 2296025
  have htrace : WordTrace (prefixWord ++ tailWord_2296025) baseStart_2296025 baseEnd_2296025 := by
    simpa [prefixWord, tailWord_2296025, baseEnd_2296025] using wordTrace_append hprefix tailTrace_2296025
  have hstable : (prefixWord ++ tailWord_2296025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2296025).length < 2 ^ (prefixWord ++ tailWord_2296025).sum := by decide
  have hdescent : baseEnd_2296025 < baseStart_2296025 := by decide
  rcases family_descends (prefixWord ++ tailWord_2296025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2296062 : List Nat := [4, 2, 2, 1, 1, 1, 1, 2, 4, 5]
def baseStart_2296062 : Nat := 118140960795 + 2296062 * 2 ^ 59
def prefixEnd_2296062 : Nat := 4983230072969 + 3 ^ 40 * 2296062 * 2
def baseEnd_2296062 : Nat := 392994472841233626855203

theorem tailTrace_2296062 : CollatzResearch.WordTrace tailWord_2296062 prefixEnd_2296062 392994472841233626855203 := by
  unfold tailWord_2296062
  simp only [CollatzResearch.WordTrace]
  refine ⟨10468032625970873126894305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55829507338511323343436293 10468032625970873126894305)
  ·
    refine ⟨7851024469478154845170729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10468032625970873126894305 7851024469478154845170729)
    ·
      refine ⟨5888268352108616133878047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7851024469478154845170729 5888268352108616133878047)
      ·
        refine ⟨8832402528162924200817071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5888268352108616133878047 8832402528162924200817071)
        ·
          refine ⟨13248603792244386301225607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8832402528162924200817071 13248603792244386301225607)
          ·
            refine ⟨19872905688366579451838411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13248603792244386301225607 19872905688366579451838411)
            ·
              refine ⟨29809358532549869177757617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19872905688366579451838411 29809358532549869177757617)
              ·
                refine ⟨22357018899412401883318213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29809358532549869177757617 22357018899412401883318213)
                ·
                  refine ⟨4191941043639825353122165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22357018899412401883318213 4191941043639825353122165)
                  ·
                    refine ⟨392994472841233626855203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4191941043639825353122165 392994472841233626855203)
                    ·
                      rfl

theorem cell23_2296062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 2, 4, 5].length) (baseStart_2296062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2296062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2296062 prefixEnd_2296062 := by exact prefixLift 2296062
  have htrace : WordTrace (prefixWord ++ tailWord_2296062) baseStart_2296062 baseEnd_2296062 := by
    simpa [prefixWord, tailWord_2296062, baseEnd_2296062] using wordTrace_append hprefix tailTrace_2296062
  have hstable : (prefixWord ++ tailWord_2296062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2296062).length < 2 ^ (prefixWord ++ tailWord_2296062).sum := by decide
  have hdescent : baseEnd_2296062 < baseStart_2296062 := by decide
  rcases family_descends (prefixWord ++ tailWord_2296062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2296116 : List Nat := [2, 5, 1, 1, 1, 3, 1, 1, 2, 4, 2]
def baseStart_2296116 : Nat := 118140960795 + 2296116 * 2 ^ 59
def prefixEnd_2296116 : Nat := 4983230072969 + 3 ^ 40 * 2296116 * 2
def baseEnd_2296116 : Nat := 1179011146479043669290361

theorem tailTrace_2296116 : CollatzResearch.WordTrace tailWord_2296116 prefixEnd_2296116 1179011146479043669290361 := by
  unfold tailWord_2296116
  simp only [CollatzResearch.WordTrace]
  refine ⟨41873115274785676118810101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55830820366380901491746801 41873115274785676118810101)
  ·
    refine ⟨3925604557011157136138447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 41873115274785676118810101 3925604557011157136138447)
    ·
      refine ⟨5888406835516735704207671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3925604557011157136138447 5888406835516735704207671)
      ·
        refine ⟨8832610253275103556311507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5888406835516735704207671 8832610253275103556311507)
        ·
          refine ⟨13248915379912655334467261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8832610253275103556311507 13248915379912655334467261)
          ·
            refine ⟨4968343267467245750425223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13248915379912655334467261 4968343267467245750425223)
            ·
              refine ⟨7452514901200868625637835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4968343267467245750425223 7452514901200868625637835)
              ·
                refine ⟨11178772351801302938456753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7452514901200868625637835 11178772351801302938456753)
                ·
                  refine ⟨8384079263850977203842565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11178772351801302938456753 8384079263850977203842565)
                  ·
                    refine ⟨1572014861972058225720481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8384079263850977203842565 1572014861972058225720481)
                    ·
                      refine ⟨1179011146479043669290361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1572014861972058225720481 1179011146479043669290361)
                      ·
                        rfl

theorem cell23_2296116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 1, 2, 4, 2].length) (baseStart_2296116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2296116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2296116 prefixEnd_2296116 := by exact prefixLift 2296116
  have htrace : WordTrace (prefixWord ++ tailWord_2296116) baseStart_2296116 baseEnd_2296116 := by
    simpa [prefixWord, tailWord_2296116, baseEnd_2296116] using wordTrace_append hprefix tailTrace_2296116
  have hstable : (prefixWord ++ tailWord_2296116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2296116).length < 2 ^ (prefixWord ++ tailWord_2296116).sum := by decide
  have hdescent : baseEnd_2296116 < baseStart_2296116 := by decide
  rcases family_descends (prefixWord ++ tailWord_2296116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2296122 : List Nat := [3, 1, 1, 1, 4, 2, 2, 3, 6]
def baseStart_2296122 : Nat := 118140960795 + 2296122 * 2 ^ 59
def prefixEnd_2296122 : Nat := 4983230072969 + 3 ^ 40 * 2296122 * 2
def baseEnd_2296122 : Nat := 131001580818107849535037

theorem tailTrace_2296122 : CollatzResearch.WordTrace tailWord_2296122 prefixEnd_2296122 131001580818107849535037 := by
  unfold tailWord_2296122
  simp only [CollatzResearch.WordTrace]
  refine ⟨20936612346887403815584655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55830966258366410174892413 20936612346887403815584655)
  ·
    refine ⟨31404918520331105723376983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20936612346887403815584655 31404918520331105723376983)
    ·
      refine ⟨47107377780496658585065475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31404918520331105723376983 47107377780496658585065475)
      ·
        refine ⟨70661066670744987877598213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47107377780496658585065475 70661066670744987877598213)
        ·
          refine ⟨13248950000764685227049665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 70661066670744987877598213 13248950000764685227049665)
          ·
            refine ⟨9936712500573513920287249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13248950000764685227049665 9936712500573513920287249)
            ·
              refine ⟨7452534375430135440215437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9936712500573513920287249 7452534375430135440215437)
              ·
                refine ⟨2794700390786300790080789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7452534375430135440215437 2794700390786300790080789)
                ·
                  refine ⟨131001580818107849535037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2794700390786300790080789 131001580818107849535037)
                  ·
                    rfl

theorem cell23_2296122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 3, 6].length) (baseStart_2296122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2296122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2296122 prefixEnd_2296122 := by exact prefixLift 2296122
  have htrace : WordTrace (prefixWord ++ tailWord_2296122) baseStart_2296122 baseEnd_2296122 := by
    simpa [prefixWord, tailWord_2296122, baseEnd_2296122] using wordTrace_append hprefix tailTrace_2296122
  have hstable : (prefixWord ++ tailWord_2296122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2296122).length < 2 ^ (prefixWord ++ tailWord_2296122).sum := by decide
  have hdescent : baseEnd_2296122 < baseStart_2296122 := by decide
  rcases family_descends (prefixWord ++ tailWord_2296122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2296159 : List Nat := [1, 1, 2, 3, 1, 2, 2, 4, 2, 3, 2]
def baseStart_2296159 : Nat := 118140960795 + 2296159 * 2 ^ 59
def prefixEnd_2296159 : Nat := 4983230072969 + 3 ^ 40 * 2296159 * 2
def baseEnd_2296159 : Nat := 1179033226147187001052663

theorem tailTrace_2296159 : CollatzResearch.WordTrace tailWord_2296159 prefixEnd_2296159 1179033226147187001052663 := by
  unfold tailWord_2296159
  simp only [CollatzResearch.WordTrace]
  refine ⟨83747798888415570581435531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55831865925610380387623687 83747798888415570581435531)
  ·
    refine ⟨125621698332623355872153297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83747798888415570581435531 125621698332623355872153297)
    ·
      refine ⟨94216273749467516904114973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125621698332623355872153297 94216273749467516904114973)
      ·
        refine ⟨35331102656050318839043115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94216273749467516904114973 35331102656050318839043115)
        ·
          refine ⟨52996653984075478258564673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35331102656050318839043115 52996653984075478258564673)
          ·
            refine ⟨39747490488056608693923505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52996653984075478258564673 39747490488056608693923505)
            ·
              refine ⟨29810617866042456520442629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39747490488056608693923505 29810617866042456520442629)
              ·
                refine ⟨5589490849882960597582993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29810617866042456520442629 5589490849882960597582993)
                ·
                  refine ⟨4192118137412220448187245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5589490849882960597582993 4192118137412220448187245)
                  ·
                    refine ⟨1572044301529582668070217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4192118137412220448187245 1572044301529582668070217)
                    ·
                      refine ⟨1179033226147187001052663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1572044301529582668070217 1179033226147187001052663)
                      ·
                        rfl

theorem cell23_2296159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 4, 2, 3, 2].length) (baseStart_2296159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2296159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2296159 prefixEnd_2296159 := by exact prefixLift 2296159
  have htrace : WordTrace (prefixWord ++ tailWord_2296159) baseStart_2296159 baseEnd_2296159 := by
    simpa [prefixWord, tailWord_2296159, baseEnd_2296159] using wordTrace_append hprefix tailTrace_2296159
  have hstable : (prefixWord ++ tailWord_2296159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2296159).length < 2 ^ (prefixWord ++ tailWord_2296159).sum := by decide
  have hdescent : baseEnd_2296159 < baseStart_2296159 := by decide
  rcases family_descends (prefixWord ++ tailWord_2296159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2296189 : List Nat := [1, 4, 1, 1, 2, 3, 1, 4, 1, 1, 4]
def baseStart_2296189 : Nat := 118140960795 + 2296189 * 2 ^ 59
def prefixEnd_2296189 : Nat := 4983230072969 + 3 ^ 40 * 2296189 * 2
def baseEnd_2296189 : Nat := 1179048630566821883677525

theorem tailTrace_2296189 : CollatzResearch.WordTrace tailWord_2296189 prefixEnd_2296189 1179048630566821883677525 := by
  unfold tailWord_2296189
  simp only [CollatzResearch.WordTrace]
  refine ⟨83748893078306885705027621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55832595385537923803351747 83748893078306885705027621)
  ·
    refine ⟨15702917452182541069692679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83748893078306885705027621 15702917452182541069692679)
    ·
      refine ⟨23554376178273811604539019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15702917452182541069692679 23554376178273811604539019)
      ·
        refine ⟨35331564267410717406808529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23554376178273811604539019 35331564267410717406808529)
        ·
          refine ⟨26498673200558038055106397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35331564267410717406808529 26498673200558038055106397)
          ·
            refine ⟨9937002450209264270664899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26498673200558038055106397 9937002450209264270664899)
            ·
              refine ⟨14905503675313896405997349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9937002450209264270664899 14905503675313896405997349)
              ·
                refine ⟨2794781939121355576124503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14905503675313896405997349 2794781939121355576124503)
                ·
                  refine ⟨4192172908682033364186755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2794781939121355576124503 4192172908682033364186755)
                  ·
                    refine ⟨6288259363023050046280133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4192172908682033364186755 6288259363023050046280133)
                    ·
                      refine ⟨1179048630566821883677525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6288259363023050046280133 1179048630566821883677525)
                      ·
                        rfl

theorem cell23_2296189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 4, 1, 1, 4].length) (baseStart_2296189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2296189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2296189 prefixEnd_2296189 := by exact prefixLift 2296189
  have htrace : WordTrace (prefixWord ++ tailWord_2296189) baseStart_2296189 baseEnd_2296189 := by
    simpa [prefixWord, tailWord_2296189, baseEnd_2296189] using wordTrace_append hprefix tailTrace_2296189
  have hstable : (prefixWord ++ tailWord_2296189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2296189).length < 2 ^ (prefixWord ++ tailWord_2296189).sum := by decide
  have hdescent : baseEnd_2296189 < baseStart_2296189 := by decide
  rcases family_descends (prefixWord ++ tailWord_2296189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2296206 : List Nat := [4, 1, 1, 4, 1, 1, 2, 3, 1, 1, 4]
def baseStart_2296206 : Nat := 118140960795 + 2296206 * 2 ^ 59
def prefixEnd_2296206 : Nat := 4983230072969 + 3 ^ 40 * 2296206 * 2
def baseEnd_2296206 : Nat := 1179057359737948317164947

theorem tailTrace_2296206 : CollatzResearch.WordTrace tailWord_2296206 prefixEnd_2296206 1179057359737948317164947 := by
  unfold tailWord_2296206
  simp only [CollatzResearch.WordTrace]
  refine ⟨10468689139905662201049559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55833008746163531738930981 10468689139905662201049559)
  ·
    refine ⟨15703033709858493301574339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10468689139905662201049559 15703033709858493301574339)
    ·
      refine ⟨23554550564787739952361509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15703033709858493301574339 23554550564787739952361509)
      ·
        refine ⟨4416478230897701241067783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23554550564787739952361509 4416478230897701241067783)
        ·
          refine ⟨6624717346346551861601675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4416478230897701241067783 6624717346346551861601675)
          ·
            refine ⟨9937076019519827792402513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6624717346346551861601675 9937076019519827792402513)
            ·
              refine ⟨7452807014639870844301885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9937076019519827792402513 7452807014639870844301885)
              ·
                refine ⟨2794802630489951566613207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7452807014639870844301885 2794802630489951566613207)
                ·
                  refine ⟨4192203945734927349919811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2794802630489951566613207 4192203945734927349919811)
                  ·
                    refine ⟨6288305918602391024879717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4192203945734927349919811 6288305918602391024879717)
                    ·
                      refine ⟨1179057359737948317164947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6288305918602391024879717 1179057359737948317164947)
                      ·
                        rfl

theorem cell23_2296206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_2296206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2296206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2296206 prefixEnd_2296206 := by exact prefixLift 2296206
  have htrace : WordTrace (prefixWord ++ tailWord_2296206) baseStart_2296206 baseEnd_2296206 := by
    simpa [prefixWord, tailWord_2296206, baseEnd_2296206] using wordTrace_append hprefix tailTrace_2296206
  have hstable : (prefixWord ++ tailWord_2296206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2296206).length < 2 ^ (prefixWord ++ tailWord_2296206).sum := by decide
  have hdescent : baseEnd_2296206 < baseStart_2296206 := by decide
  rcases family_descends (prefixWord ++ tailWord_2296206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2296257 : List Nat := [1, 2, 7, 1, 1, 1, 3, 1, 1, 1, 4]
def baseStart_2296257 : Nat := 118140960795 + 2296257 * 2 ^ 59
def prefixEnd_2296257 : Nat := 4983230072969 + 3 ^ 40 * 2296257 * 2
def baseEnd_2296257 : Nat := 1179083547251327617627213

theorem tailTrace_2296257 : CollatzResearch.WordTrace tailWord_2296257 prefixEnd_2296257 1179083547251327617627213 := by
  unfold tailWord_2296257
  simp only [CollatzResearch.WordTrace]
  refine ⟨83751373242060533318503025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55834248828040355545668683 83751373242060533318503025)
  ·
    refine ⟨62813529931545399988877269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83751373242060533318503025 62813529931545399988877269)
    ·
      refine ⟨1472192107770595312239311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 62813529931545399988877269 1472192107770595312239311)
      ·
        refine ⟨2208288161655892968358967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1472192107770595312239311 2208288161655892968358967)
        ·
          refine ⟨3312432242483839452538451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2208288161655892968358967 3312432242483839452538451)
          ·
            refine ⟨4968648363725759178807677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3312432242483839452538451 4968648363725759178807677)
            ·
              refine ⟨1863243136397159692052879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4968648363725759178807677 1863243136397159692052879)
              ·
                refine ⟨2794864704595739538079319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1863243136397159692052879 2794864704595739538079319)
                ·
                  refine ⟨4192297056893609307118979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2794864704595739538079319 4192297056893609307118979)
                  ·
                    refine ⟨6288445585340413960678469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4192297056893609307118979 6288445585340413960678469)
                    ·
                      refine ⟨1179083547251327617627213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6288445585340413960678469 1179083547251327617627213)
                      ·
                        rfl

theorem cell23_2296257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_2296257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2296257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2296257 prefixEnd_2296257 := by exact prefixLift 2296257
  have htrace : WordTrace (prefixWord ++ tailWord_2296257) baseStart_2296257 baseEnd_2296257 := by
    simpa [prefixWord, tailWord_2296257, baseEnd_2296257] using wordTrace_append hprefix tailTrace_2296257
  have hstable : (prefixWord ++ tailWord_2296257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2296257).length < 2 ^ (prefixWord ++ tailWord_2296257).sum := by decide
  have hdescent : baseEnd_2296257 < baseStart_2296257 := by decide
  rcases family_descends (prefixWord ++ tailWord_2296257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2296260 : List Nat := [2, 3, 3, 2, 2, 1, 3, 1, 1, 2, 3]
def baseStart_2296260 : Nat := 118140960795 + 2296260 * 2 ^ 59
def prefixEnd_2296260 : Nat := 4983230072969 + 3 ^ 40 * 2296260 * 2
def baseEnd_2296260 : Nat := 1179085087693291105889699

theorem tailTrace_2296260 : CollatzResearch.WordTrace tailWord_2296260 prefixEnd_2296260 1179085087693291105889699 := by
  unfold tailWord_2296260
  simp only [CollatzResearch.WordTrace]
  refine ⟨41875741330524832415431117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55834321774033109887241489 41875741330524832415431117)
  ·
    refine ⟨15703402998946812155786669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41875741330524832415431117 15703402998946812155786669)
    ·
      refine ⟨5888776124605054558420001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15703402998946812155786669 5888776124605054558420001)
      ·
        refine ⟨4416582093453790918815001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5888776124605054558420001 4416582093453790918815001)
        ·
          refine ⟨3312436570090343189111251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4416582093453790918815001 3312436570090343189111251)
          ·
            refine ⟨4968654855135514783666877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3312436570090343189111251 4968654855135514783666877)
            ·
              refine ⟨1863245570675818043875079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4968654855135514783666877 1863245570675818043875079)
              ·
                refine ⟨2794868356013727065812619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1863245570675818043875079 2794868356013727065812619)
                ·
                  refine ⟨4192302534020590598718929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2794868356013727065812619 4192302534020590598718929)
                  ·
                    refine ⟨3144226900515442949039197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4192302534020590598718929 3144226900515442949039197)
                    ·
                      refine ⟨1179085087693291105889699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3144226900515442949039197 1179085087693291105889699)
                      ·
                        rfl

theorem cell23_2296260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 3, 1, 1, 2, 3].length) (baseStart_2296260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2296260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2296260 prefixEnd_2296260 := by exact prefixLift 2296260
  have htrace : WordTrace (prefixWord ++ tailWord_2296260) baseStart_2296260 baseEnd_2296260 := by
    simpa [prefixWord, tailWord_2296260, baseEnd_2296260] using wordTrace_append hprefix tailTrace_2296260
  have hstable : (prefixWord ++ tailWord_2296260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2296260).length < 2 ^ (prefixWord ++ tailWord_2296260).sum := by decide
  have hdescent : baseEnd_2296260 < baseStart_2296260 := by decide
  rcases family_descends (prefixWord ++ tailWord_2296260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2296290 : List Nat := [3, 3, 3, 2, 1, 1, 2, 1, 1, 3, 3]
def baseStart_2296290 : Nat := 118140960795 + 2296290 * 2 ^ 59
def prefixEnd_2296290 : Nat := 4983230072969 + 3 ^ 40 * 2296290 * 2
def baseEnd_2296290 : Nat := 1179100492112925988514561

theorem tailTrace_2296290 : CollatzResearch.WordTrace tailWord_2296290 prefixEnd_2296290 1179100492112925988514561 := by
  unfold tailWord_2296290
  simp only [CollatzResearch.WordTrace]
  refine ⟨20938144212735244988613581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55835051233960653302969549 20938144212735244988613581)
  ·
    refine ⟨7851804079775716870730093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20938144212735244988613581 7851804079775716870730093)
    ·
      refine ⟨2944426529915893826523785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7851804079775716870730093 2944426529915893826523785)
      ·
        refine ⟨2208319897436920369892839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2944426529915893826523785 2208319897436920369892839)
        ·
          refine ⟨3312479846155380554839259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2208319897436920369892839 3312479846155380554839259)
          ·
            refine ⟨4968719769233070832258889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3312479846155380554839259 4968719769233070832258889)
            ·
              refine ⟨3726539826924803124194167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4968719769233070832258889 3726539826924803124194167)
              ·
                refine ⟨5589809740387204686291251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3726539826924803124194167 5589809740387204686291251)
                ·
                  refine ⟨8384714610580807029436877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5589809740387204686291251 8384714610580807029436877)
                  ·
                    refine ⟨3144267978967802636038829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8384714610580807029436877 3144267978967802636038829)
                    ·
                      refine ⟨1179100492112925988514561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3144267978967802636038829 1179100492112925988514561)
                      ·
                        rfl

theorem cell23_2296290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_2296290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2296290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2296290 prefixEnd_2296290 := by exact prefixLift 2296290
  have htrace : WordTrace (prefixWord ++ tailWord_2296290) baseStart_2296290 baseEnd_2296290 := by
    simpa [prefixWord, tailWord_2296290, baseEnd_2296290] using wordTrace_append hprefix tailTrace_2296290
  have hstable : (prefixWord ++ tailWord_2296290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2296290).length < 2 ^ (prefixWord ++ tailWord_2296290).sum := by decide
  have hdescent : baseEnd_2296290 < baseStart_2296290 := by decide
  rcases family_descends (prefixWord ++ tailWord_2296290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2296296 : List Nat := [2, 1, 4, 1, 1, 3, 1, 3, 1, 4, 2]
def baseStart_2296296 : Nat := 118140960795 + 2296296 * 2 ^ 59
def prefixEnd_2296296 : Nat := 4983230072969 + 3 ^ 40 * 2296296 * 2
def baseEnd_2296296 : Nat := 1179103572996852965039533

theorem tailTrace_2296296 : CollatzResearch.WordTrace tailWord_2296296 prefixEnd_2296296 1179103572996852965039533 := by
  unfold tailWord_2296296
  simp only [CollatzResearch.WordTrace]
  refine ⟨41876397844459621489586371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55835197125946161986115161 41876397844459621489586371)
  ·
    refine ⟨62814596766689432234379557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41876397844459621489586371 62814596766689432234379557)
    ·
      refine ⟨11777736893754268543946167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62814596766689432234379557 11777736893754268543946167)
      ·
        refine ⟨17666605340631402815919251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11777736893754268543946167 17666605340631402815919251)
        ·
          refine ⟨26499908010947104223878877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17666605340631402815919251 26499908010947104223878877)
          ·
            refine ⟨9937465504105164083954579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26499908010947104223878877 9937465504105164083954579)
            ·
              refine ⟨14906198256157746125931869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9937465504105164083954579 14906198256157746125931869)
              ·
                refine ⟨5589824346059154797224451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14906198256157746125931869 5589824346059154797224451)
                ·
                  refine ⟨8384736519088732195836677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5589824346059154797224451 8384736519088732195836677)
                  ·
                    refine ⟨1572138097329137286719377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8384736519088732195836677 1572138097329137286719377)
                    ·
                      refine ⟨1179103572996852965039533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1572138097329137286719377 1179103572996852965039533)
                      ·
                        rfl

theorem cell23_2296296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 3, 1, 4, 2].length) (baseStart_2296296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2296296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2296296 prefixEnd_2296296 := by exact prefixLift 2296296
  have htrace : WordTrace (prefixWord ++ tailWord_2296296) baseStart_2296296 baseEnd_2296296 := by
    simpa [prefixWord, tailWord_2296296, baseEnd_2296296] using wordTrace_append hprefix tailTrace_2296296
  have hstable : (prefixWord ++ tailWord_2296296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2296296).length < 2 ^ (prefixWord ++ tailWord_2296296).sum := by decide
  have hdescent : baseEnd_2296296 < baseStart_2296296 := by decide
  rcases family_descends (prefixWord ++ tailWord_2296296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2296349 : List Nat := [1, 4, 2, 2, 1, 2, 1, 2, 1, 7]
def baseStart_2296349 : Nat := 118140960795 + 2296349 * 2 ^ 59
def prefixEnd_2296349 : Nat := 4983230072969 + 3 ^ 40 * 2296349 * 2
def baseEnd_2296349 : Nat := 393043595823847085892263

theorem tailTrace_2296349 : CollatzResearch.WordTrace tailWord_2296349 prefixEnd_2296349 393043595823847085892263 := by
  unfold tailWord_2296349
  simp only [CollatzResearch.WordTrace]
  refine ⟨83754728757727233030852101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55836485838484822020568067 83754728757727233030852101)
  ·
    refine ⟨15704011642073856193284769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83754728757727233030852101 15704011642073856193284769)
    ·
      refine ⟨11778008731555392144963577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15704011642073856193284769 11778008731555392144963577)
      ·
        refine ⟨8833506548666544108722683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11778008731555392144963577 8833506548666544108722683)
        ·
          refine ⟨13250259822999816163084025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8833506548666544108722683 13250259822999816163084025)
          ·
            refine ⟨9937694867249862122313019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13250259822999816163084025 9937694867249862122313019)
            ·
              refine ⟨14906542300874793183469529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9937694867249862122313019 14906542300874793183469529)
              ·
                refine ⟨11179906725656094887602147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14906542300874793183469529 11179906725656094887602147)
                ·
                  refine ⟨16769860088484142331403221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11179906725656094887602147 16769860088484142331403221)
                  ·
                    refine ⟨393043595823847085892263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16769860088484142331403221 393043595823847085892263)
                    ·
                      rfl

theorem cell23_2296349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 2, 1, 7].length) (baseStart_2296349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2296349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2296349 prefixEnd_2296349 := by exact prefixLift 2296349
  have htrace : WordTrace (prefixWord ++ tailWord_2296349) baseStart_2296349 baseEnd_2296349 := by
    simpa [prefixWord, tailWord_2296349, baseEnd_2296349] using wordTrace_append hprefix tailTrace_2296349
  have hstable : (prefixWord ++ tailWord_2296349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2296349).length < 2 ^ (prefixWord ++ tailWord_2296349).sum := by decide
  have hdescent : baseEnd_2296349 < baseStart_2296349 := by decide
  rcases family_descends (prefixWord ++ tailWord_2296349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2296369 : List Nat := [1, 2, 2, 3, 1, 1, 4, 1, 1, 3, 4]
def baseStart_2296369 : Nat := 118140960795 + 2296369 * 2 ^ 59
def prefixEnd_2296369 : Nat := 4983230072969 + 3 ^ 40 * 2296369 * 2
def baseEnd_2296369 : Nat := 1179141057084631179426697

theorem tailTrace_2296369 : CollatzResearch.WordTrace tailWord_2296369 prefixEnd_2296369 1179141057084631179426697 := by
  unfold tailWord_2296369
  simp only [CollatzResearch.WordTrace]
  refine ⟨83755458217654776446580161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55836972145103184297720107 83755458217654776446580161)
  ·
    refine ⟨62816593663241082334935121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83755458217654776446580161 62816593663241082334935121)
    ·
      refine ⟨47112445247430811751201341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62816593663241082334935121 47112445247430811751201341)
      ·
        refine ⟨17667166967786554406700503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47112445247430811751201341 17667166967786554406700503)
        ·
          refine ⟨26500750451679831610050755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17667166967786554406700503 26500750451679831610050755)
          ·
            refine ⟨39751125677519747415076133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26500750451679831610050755 39751125677519747415076133)
            ·
              refine ⟨7453336064534952640326775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39751125677519747415076133 7453336064534952640326775)
              ·
                refine ⟨11180004096802428960490163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7453336064534952640326775 11180004096802428960490163)
                ·
                  refine ⟨16770006145203643440735245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11180004096802428960490163 16770006145203643440735245)
                  ·
                    refine ⟨6288752304451366290275717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16770006145203643440735245 6288752304451366290275717)
                    ·
                      refine ⟨1179141057084631179426697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6288752304451366290275717 1179141057084631179426697)
                      ·
                        rfl

theorem cell23_2296369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 1, 1, 3, 4].length) (baseStart_2296369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2296369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2296369 prefixEnd_2296369 := by exact prefixLift 2296369
  have htrace : WordTrace (prefixWord ++ tailWord_2296369) baseStart_2296369 baseEnd_2296369 := by
    simpa [prefixWord, tailWord_2296369, baseEnd_2296369] using wordTrace_append hprefix tailTrace_2296369
  have hstable : (prefixWord ++ tailWord_2296369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2296369).length < 2 ^ (prefixWord ++ tailWord_2296369).sum := by decide
  have hdescent : baseEnd_2296369 < baseStart_2296369 := by decide
  rcases family_descends (prefixWord ++ tailWord_2296369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2296499 : List Nat := [1, 1, 1, 2, 3, 5, 10]
def baseStart_2296499 : Nat := 118140960795 + 2296499 * 2 ^ 59
def prefixEnd_2296499 : Nat := 4983230072969 + 3 ^ 40 * 2296499 * 2
def baseEnd_2296499 : Nat := 14558121105798958898779

theorem tailTrace_2296499 : CollatzResearch.WordTrace tailWord_2296499 prefixEnd_2296499 14558121105798958898779 := by
  unfold tailWord_2296499
  simp only [CollatzResearch.WordTrace]
  refine ⟨83760199707183808648812551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55840133138122539099208367 83760199707183808648812551)
  ·
    refine ⟨125640299560775712973218827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83760199707183808648812551 125640299560775712973218827)
    ·
      refine ⟨188460449341163569459828241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125640299560775712973218827 188460449341163569459828241)
      ·
        refine ⟨141345337005872677094871181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 188460449341163569459828241 141345337005872677094871181)
        ·
          refine ⟨53004501377202253910576693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 141345337005872677094871181 53004501377202253910576693)
          ·
            refine ⟨4969172004112711304116565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 53004501377202253910576693 4969172004112711304116565)
            ·
              refine ⟨14558121105798958898779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 4969172004112711304116565 14558121105798958898779)
              ·
                rfl

theorem cell23_2296499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 10].length) (baseStart_2296499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2296499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2296499 prefixEnd_2296499 := by exact prefixLift 2296499
  have htrace : WordTrace (prefixWord ++ tailWord_2296499) baseStart_2296499 baseEnd_2296499 := by
    simpa [prefixWord, tailWord_2296499, baseEnd_2296499] using wordTrace_append hprefix tailTrace_2296499
  have hstable : (prefixWord ++ tailWord_2296499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2296499).length < 2 ^ (prefixWord ++ tailWord_2296499).sum := by decide
  have hdescent : baseEnd_2296499 < baseStart_2296499 := by decide
  rcases family_descends (prefixWord ++ tailWord_2296499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2296503 : List Nat := [1, 1, 3, 1, 6, 1, 1, 1, 4, 4]
def baseStart_2296503 : Nat := 118140960795 + 2296503 * 2 ^ 59
def prefixEnd_2296503 : Nat := 4983230072969 + 3 ^ 40 * 2296503 * 2
def baseEnd_2296503 : Nat := 393069954497444551717027

theorem tailTrace_2296503 : CollatzResearch.WordTrace tailWord_2296503 prefixEnd_2296503 393069954497444551717027 := by
  unfold tailWord_2296503
  simp only [CollatzResearch.WordTrace]
  refine ⟨83760345599169317331958163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55840230399446211554638775 83760345599169317331958163)
  ·
    refine ⟨125640518398753975997937245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83760345599169317331958163 125640518398753975997937245)
    ·
      refine ⟨47115194399532740999226467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 125640518398753975997937245 47115194399532740999226467)
      ·
        refine ⟨70672791599299111498839701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47115194399532740999226467 70672791599299111498839701)
        ·
          refine ⟨3312787106217145851508111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 70672791599299111498839701 3312787106217145851508111)
          ·
            refine ⟨4969180659325718777262167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3312787106217145851508111 4969180659325718777262167)
            ·
              refine ⟨7453770988988578165893251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4969180659325718777262167 7453770988988578165893251)
              ·
                refine ⟨11180656483482867248839877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7453770988988578165893251 11180656483482867248839877)
                ·
                  refine ⟨2096373090653037609157477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11180656483482867248839877 2096373090653037609157477)
                  ·
                    refine ⟨393069954497444551717027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2096373090653037609157477 393069954497444551717027)
                    ·
                      rfl

theorem cell23_2296503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 1, 4, 4].length) (baseStart_2296503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2296503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2296503 prefixEnd_2296503 := by exact prefixLift 2296503
  have htrace : WordTrace (prefixWord ++ tailWord_2296503) baseStart_2296503 baseEnd_2296503 := by
    simpa [prefixWord, tailWord_2296503, baseEnd_2296503] using wordTrace_append hprefix tailTrace_2296503
  have hstable : (prefixWord ++ tailWord_2296503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2296503).length < 2 ^ (prefixWord ++ tailWord_2296503).sum := by decide
  have hdescent : baseEnd_2296503 < baseStart_2296503 := by decide
  rcases family_descends (prefixWord ++ tailWord_2296503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2296519 : List Nat := [1, 1, 4, 1, 1, 1, 2, 1, 1, 4, 6]
def baseStart_2296519 : Nat := 118140960795 + 2296519 * 2 ^ 59
def prefixEnd_2296519 : Nat := 4983230072969 + 3 ^ 40 * 2296519 * 2
def baseEnd_2296519 : Nat := 1179218079182805592551007

theorem tailTrace_2296519 : CollatzResearch.WordTrace tailWord_2296519 prefixEnd_2296519 1179218079182805592551007 := by
  unfold tailWord_2296519
  simp only [CollatzResearch.WordTrace]
  refine ⟨83760929167111352064540611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55840619444740901376360407 83760929167111352064540611)
  ·
    refine ⟨125641393750667028096810917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83760929167111352064540611 125641393750667028096810917)
    ·
      refine ⟨23557761328250067768152047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 125641393750667028096810917 23557761328250067768152047)
      ·
        refine ⟨35336641992375101652228071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23557761328250067768152047 35336641992375101652228071)
        ·
          refine ⟨53004962988562652478342107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35336641992375101652228071 53004962988562652478342107)
          ·
            refine ⟨79507444482843978717513161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53004962988562652478342107 79507444482843978717513161)
            ·
              refine ⟨59630583362132984038134871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79507444482843978717513161 59630583362132984038134871)
              ·
                refine ⟨89445875043199476057202307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59630583362132984038134871 89445875043199476057202307)
                ·
                  refine ⟨134168812564799214085803461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 89445875043199476057202307 134168812564799214085803461)
                  ·
                    refine ⟨25156652355899852641088149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 134168812564799214085803461 25156652355899852641088149)
                    ·
                      refine ⟨1179218079182805592551007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25156652355899852641088149 1179218079182805592551007)
                      ·
                        rfl

theorem cell23_2296519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 4, 6].length) (baseStart_2296519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2296519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2296519 prefixEnd_2296519 := by exact prefixLift 2296519
  have htrace : WordTrace (prefixWord ++ tailWord_2296519) baseStart_2296519 baseEnd_2296519 := by
    simpa [prefixWord, tailWord_2296519, baseEnd_2296519] using wordTrace_append hprefix tailTrace_2296519
  have hstable : (prefixWord ++ tailWord_2296519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2296519).length < 2 ^ (prefixWord ++ tailWord_2296519).sum := by decide
  have hdescent : baseEnd_2296519 < baseStart_2296519 := by decide
  rcases family_descends (prefixWord ++ tailWord_2296519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2296520 : List Nat := [2, 1, 3, 1, 2, 4, 3, 1, 2, 4]
def baseStart_2296520 : Nat := 118140960795 + 2296520 * 2 ^ 59
def prefixEnd_2296520 : Nat := 4983230072969 + 3 ^ 40 * 2296520 * 2
def baseEnd_2296520 : Nat := 393072864221153362879501

theorem tailTrace_2296520 : CollatzResearch.WordTrace tailWord_2296520 prefixEnd_2296520 393072864221153362879501 := by
  unfold tailWord_2296520
  simp only [CollatzResearch.WordTrace]
  refine ⟨41880482820053864617663507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55840643760071819490218009 41880482820053864617663507)
  ·
    refine ⟨62820724230080796926495261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41880482820053864617663507 62820724230080796926495261)
    ·
      refine ⟨23557771586280298847435723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62820724230080796926495261 23557771586280298847435723)
      ·
        refine ⟨35336657379420448271153585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23557771586280298847435723 35336657379420448271153585)
        ·
          refine ⟨26502493034565336203365189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35336657379420448271153585 26502493034565336203365189)
          ·
            refine ⟨4969217443981000538130973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26502493034565336203365189 4969217443981000538130973)
            ·
              refine ⟨1863456541492875201799115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4969217443981000538130973 1863456541492875201799115)
              ·
                refine ⟨2795184812239312802698673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1863456541492875201799115 2795184812239312802698673)
                ·
                  refine ⟨2096388609179484602024005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2795184812239312802698673 2096388609179484602024005)
                  ·
                    refine ⟨393072864221153362879501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2096388609179484602024005 393072864221153362879501)
                    ·
                      rfl

theorem cell23_2296520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 3, 1, 2, 4].length) (baseStart_2296520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2296520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2296520 prefixEnd_2296520 := by exact prefixLift 2296520
  have htrace : WordTrace (prefixWord ++ tailWord_2296520) baseStart_2296520 baseEnd_2296520 := by
    simpa [prefixWord, tailWord_2296520, baseEnd_2296520] using wordTrace_append hprefix tailTrace_2296520
  have hstable : (prefixWord ++ tailWord_2296520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2296520).length < 2 ^ (prefixWord ++ tailWord_2296520).sum := by decide
  have hdescent : baseEnd_2296520 < baseStart_2296520 := by decide
  rcases family_descends (prefixWord ++ tailWord_2296520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2296533 : List Nat := [1, 3, 2, 5, 1, 1, 1, 9]
def baseStart_2296533 : Nat := 118140960795 + 2296533 * 2 ^ 59
def prefixEnd_2296533 : Nat := 4983230072969 + 3 ^ 40 * 2296533 * 2
def baseEnd_2296533 : Nat := 43675009922665501399109

theorem tailTrace_2296533 : CollatzResearch.WordTrace tailWord_2296533 prefixEnd_2296533 43675009922665501399109 := by
  unfold tailWord_2296533
  simp only [CollatzResearch.WordTrace]
  refine ⟨83761439789060632455550253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55840959859373754970366835 83761439789060632455550253)
  ·
    refine ⟨31410539920897737170831345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83761439789060632455550253 31410539920897737170831345)
    ·
      refine ⟨23557904940673302878123509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31410539920897737170831345 23557904940673302878123509)
      ·
        refine ⟨2208553588188122144824079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23557904940673302878123509 2208553588188122144824079)
        ·
          refine ⟨3312830382282183217236119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2208553588188122144824079 3312830382282183217236119)
          ·
            refine ⟨4969245573423274825854179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3312830382282183217236119 4969245573423274825854179)
            ·
              refine ⟨7453868360134912238781269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4969245573423274825854179 7453868360134912238781269)
              ·
                refine ⟨43675009922665501399109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7453868360134912238781269 43675009922665501399109)
                ·
                  rfl

theorem cell23_2296533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 9].length) (baseStart_2296533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2296533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2296533 prefixEnd_2296533 := by exact prefixLift 2296533
  have htrace : WordTrace (prefixWord ++ tailWord_2296533) baseStart_2296533 baseEnd_2296533 := by
    simpa [prefixWord, tailWord_2296533, baseEnd_2296533] using wordTrace_append hprefix tailTrace_2296533
  have hstable : (prefixWord ++ tailWord_2296533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2296533).length < 2 ^ (prefixWord ++ tailWord_2296533).sum := by decide
  have hdescent : baseEnd_2296533 < baseStart_2296533 := by decide
  rcases family_descends (prefixWord ++ tailWord_2296533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2296543 : List Nat := [1, 1, 2, 3, 2, 3, 1, 2, 4, 1, 3]
def baseStart_2296543 : Nat := 118140960795 + 2296543 * 2 ^ 59
def prefixEnd_2296543 : Nat := 4983230072969 + 3 ^ 40 * 2296543 * 2
def baseEnd_2296543 : Nat := 1179230402718513498650897

theorem tailTrace_2296543 : CollatzResearch.WordTrace tailWord_2296543 prefixEnd_2296543 1179230402718513498650897 := by
  unfold tailWord_2296543
  simp only [CollatzResearch.WordTrace]
  refine ⟨83761804519024404163414283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55841203012682936108942855 83761804519024404163414283)
  ·
    refine ⟨125642706778536606245121425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83761804519024404163414283 125642706778536606245121425)
    ·
      refine ⟨94232030083902454683841069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125642706778536606245121425 94232030083902454683841069)
      ·
        refine ⟨35337011281463420506440401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94232030083902454683841069 35337011281463420506440401)
        ·
          refine ⟨26502758461097565379830301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35337011281463420506440401 26502758461097565379830301)
          ·
            refine ⟨9938534422911587017436363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26502758461097565379830301 9938534422911587017436363)
            ·
              refine ⟨14907801634367380526154545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9938534422911587017436363 14907801634367380526154545)
              ·
                refine ⟨11180851225775535394615909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14907801634367380526154545 11180851225775535394615909)
                ·
                  refine ⟨2096409604832912886490483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11180851225775535394615909 2096409604832912886490483)
                  ·
                    refine ⟨3144614407249369329735725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2096409604832912886490483 3144614407249369329735725)
                    ·
                      refine ⟨1179230402718513498650897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3144614407249369329735725 1179230402718513498650897)
                      ·
                        rfl

theorem cell23_2296543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 2, 4, 1, 3].length) (baseStart_2296543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2296543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2296543 prefixEnd_2296543 := by exact prefixLift 2296543
  have htrace : WordTrace (prefixWord ++ tailWord_2296543) baseStart_2296543 baseEnd_2296543 := by
    simpa [prefixWord, tailWord_2296543, baseEnd_2296543] using wordTrace_append hprefix tailTrace_2296543
  have hstable : (prefixWord ++ tailWord_2296543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2296543).length < 2 ^ (prefixWord ++ tailWord_2296543).sum := by decide
  have hdescent : baseEnd_2296543 < baseStart_2296543 := by decide
  rcases family_descends (prefixWord ++ tailWord_2296543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2296586 : List Nat := [3, 1, 2, 2, 1, 2, 1, 1, 4, 1, 5]
def baseStart_2296586 : Nat := 118140960795 + 2296586 * 2 ^ 59
def prefixEnd_2296586 : Nat := 4983230072969 + 3 ^ 40 * 2296586 * 2
def baseEnd_2296586 : Nat := 1179252482386656830413199

theorem tailTrace_2296586 : CollatzResearch.WordTrace tailWord_2296586 prefixEnd_2296586 1179252482386656830413199 := by
  unfold tailWord_2296586
  simp only [CollatzResearch.WordTrace]
  refine ⟨20940843214467155626807403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55842248571912415004819741 20940843214467155626807403)
  ·
    refine ⟨31411264821700733440211105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20940843214467155626807403 31411264821700733440211105)
    ·
      refine ⟨23558448616275550080158329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31411264821700733440211105 23558448616275550080158329)
      ·
        refine ⟨17668836462206662560118747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23558448616275550080158329 17668836462206662560118747)
        ·
          refine ⟨26503254693309993840178121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17668836462206662560118747 26503254693309993840178121)
          ·
            refine ⟨19877441019982495380133591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26503254693309993840178121 19877441019982495380133591)
            ·
              refine ⟨29816161529973743070200387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19877441019982495380133591 29816161529973743070200387)
              ·
                refine ⟨44724242294960614605300581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29816161529973743070200387 44724242294960614605300581)
                ·
                  refine ⟨8385795430305115238493859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44724242294960614605300581 8385795430305115238493859)
                  ·
                    refine ⟨12578693145457672857740789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8385795430305115238493859 12578693145457672857740789)
                    ·
                      refine ⟨1179252482386656830413199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12578693145457672857740789 1179252482386656830413199)
                      ·
                        rfl

theorem cell23_2296586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 4, 1, 5].length) (baseStart_2296586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2296586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2296586 prefixEnd_2296586 := by exact prefixLift 2296586
  have htrace : WordTrace (prefixWord ++ tailWord_2296586) baseStart_2296586 baseEnd_2296586 := by
    simpa [prefixWord, tailWord_2296586, baseEnd_2296586] using wordTrace_append hprefix tailTrace_2296586
  have hstable : (prefixWord ++ tailWord_2296586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2296586).length < 2 ^ (prefixWord ++ tailWord_2296586).sum := by decide
  have hdescent : baseEnd_2296586 < baseStart_2296586 := by decide
  rcases family_descends (prefixWord ++ tailWord_2296586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2296636 : List Nat := [2, 2, 2, 2, 1, 1, 1, 4, 1, 7]
def baseStart_2296636 : Nat := 118140960795 + 2296636 * 2 ^ 59
def prefixEnd_2296636 : Nat := 4983230072969 + 3 ^ 40 * 2296636 * 2
def baseEnd_2296636 : Nat := 393092718806460544929323

theorem tailTrace_2296636 : CollatzResearch.WordTrace tailWord_2296636 prefixEnd_2296636 393092718806460544929323 := by
  unfold tailWord_2296636
  simp only [CollatzResearch.WordTrace]
  refine ⟨41882598253843740523274881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55843464338458320697699841 41882598253843740523274881)
  ·
    refine ⟨31411948690382805392456161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41882598253843740523274881 31411948690382805392456161)
    ·
      refine ⟨23558961517787104044342121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31411948690382805392456161 23558961517787104044342121)
      ·
        refine ⟨17669221138340328033256591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23558961517787104044342121 17669221138340328033256591)
        ·
          refine ⟨26503831707510492049884887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17669221138340328033256591 26503831707510492049884887)
          ·
            refine ⟨39755747561265738074827331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26503831707510492049884887 39755747561265738074827331)
            ·
              refine ⟨59633621341898607112240997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39755747561265738074827331 59633621341898607112240997)
              ·
                refine ⟨11181304001605988833545187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 59633621341898607112240997 11181304001605988833545187)
                ·
                  refine ⟨16771956002408983250317781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11181304001605988833545187 16771956002408983250317781)
                  ·
                    refine ⟨393092718806460544929323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16771956002408983250317781 393092718806460544929323)
                    ·
                      rfl

theorem cell23_2296636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 4, 1, 7].length) (baseStart_2296636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2296636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2296636 prefixEnd_2296636 := by exact prefixLift 2296636
  have htrace : WordTrace (prefixWord ++ tailWord_2296636) baseStart_2296636 baseEnd_2296636 := by
    simpa [prefixWord, tailWord_2296636, baseEnd_2296636] using wordTrace_append hprefix tailTrace_2296636
  have hstable : (prefixWord ++ tailWord_2296636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2296636).length < 2 ^ (prefixWord ++ tailWord_2296636).sum := by decide
  have hdescent : baseEnd_2296636 < baseStart_2296636 := by decide
  rcases family_descends (prefixWord ++ tailWord_2296636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2296643 : List Nat := [1, 1, 1, 3, 1, 4, 1, 2, 2, 5, 2]
def baseStart_2296643 : Nat := 118140960795 + 2296643 * 2 ^ 59
def prefixEnd_2296643 : Nat := 4983230072969 + 3 ^ 40 * 2296643 * 2
def baseEnd_2296643 : Nat := 1179281750783963107400437

theorem tailTrace_2296643 : CollatzResearch.WordTrace tailWord_2296643 prefixEnd_2296643 1179281750783963107400437 := by
  unfold tailWord_2296643
  simp only [CollatzResearch.WordTrace]
  refine ⟨83765451818662121242054583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55843634545774747494703055 83765451818662121242054583)
  ·
    refine ⟨125648177727993181863081875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83765451818662121242054583 125648177727993181863081875)
    ·
      refine ⟨188472266591989772794622813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125648177727993181863081875 188472266591989772794622813)
      ·
        refine ⟨70677099971996164797983555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 188472266591989772794622813 70677099971996164797983555)
        ·
          refine ⟨106015649957994247196975333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70677099971996164797983555 106015649957994247196975333)
          ·
            refine ⟨19877934367123921349432875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 106015649957994247196975333 19877934367123921349432875)
            ·
              refine ⟨29816901550685882024149313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19877934367123921349432875 29816901550685882024149313)
              ·
                refine ⟨22362676163014411518111985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29816901550685882024149313 22362676163014411518111985)
                ·
                  refine ⟨16772007122260808638583989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22362676163014411518111985 16772007122260808638583989)
                  ·
                    refine ⟨1572375667711950809867249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16772007122260808638583989 1572375667711950809867249)
                    ·
                      refine ⟨1179281750783963107400437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1572375667711950809867249 1179281750783963107400437)
                      ·
                        rfl

theorem cell23_2296643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 2, 2, 5, 2].length) (baseStart_2296643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2296643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2296643 prefixEnd_2296643 := by exact prefixLift 2296643
  have htrace : WordTrace (prefixWord ++ tailWord_2296643) baseStart_2296643 baseEnd_2296643 := by
    simpa [prefixWord, tailWord_2296643, baseEnd_2296643] using wordTrace_append hprefix tailTrace_2296643
  have hstable : (prefixWord ++ tailWord_2296643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2296643).length < 2 ^ (prefixWord ++ tailWord_2296643).sum := by decide
  have hdescent : baseEnd_2296643 < baseStart_2296643 := by decide
  rcases family_descends (prefixWord ++ tailWord_2296643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2296683 : List Nat := [1, 1, 1, 1, 2, 2, 5, 3, 3, 4]
def baseStart_2296683 : Nat := 118140960795 + 2296683 * 2 ^ 59
def prefixEnd_2296683 : Nat := 4983230072969 + 3 ^ 40 * 2296683 * 2
def baseEnd_2296683 : Nat := 393100763336714316966751

theorem tailTrace_2296683 : CollatzResearch.WordTrace tailWord_2296683 prefixEnd_2296683 393100763336714316966751 := by
  unfold tailWord_2296683
  simp only [CollatzResearch.WordTrace]
  refine ⟨83766910738517208073510703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55844607159011472049007135 83766910738517208073510703)
  ·
    refine ⟨125650366107775812110266055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83766910738517208073510703 125650366107775812110266055)
    ·
      refine ⟨188475549161663718165399083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125650366107775812110266055 188475549161663718165399083)
      ·
        refine ⟨282713323742495577248098625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188475549161663718165399083 282713323742495577248098625)
        ·
          refine ⟨212034992806871682936073969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 282713323742495577248098625 212034992806871682936073969)
          ·
            refine ⟨159026244605153762202055477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 212034992806871682936073969 159026244605153762202055477)
            ·
              refine ⟨14908710431733165206442701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 159026244605153762202055477 14908710431733165206442701)
              ·
                refine ⟨5590766411899936952416013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14908710431733165206442701 5590766411899936952416013)
                ·
                  refine ⟨2096537404462476357156005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5590766411899936952416013 2096537404462476357156005)
                  ·
                    refine ⟨393100763336714316966751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2096537404462476357156005 393100763336714316966751)
                    ·
                      rfl

theorem cell23_2296683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 3, 3, 4].length) (baseStart_2296683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2296683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2296683 prefixEnd_2296683 := by exact prefixLift 2296683
  have htrace : WordTrace (prefixWord ++ tailWord_2296683) baseStart_2296683 baseEnd_2296683 := by
    simpa [prefixWord, tailWord_2296683, baseEnd_2296683] using wordTrace_append hprefix tailTrace_2296683
  have hstable : (prefixWord ++ tailWord_2296683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2296683).length < 2 ^ (prefixWord ++ tailWord_2296683).sum := by decide
  have hdescent : baseEnd_2296683 < baseStart_2296683 := by decide
  rcases family_descends (prefixWord ++ tailWord_2296683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2296690 : List Nat := [3, 2, 1, 2, 1, 1, 4, 1, 2, 4, 2]
def baseStart_2296690 : Nat := 118140960795 + 2296690 * 2 ^ 59
def prefixEnd_2296690 : Nat := 4983230072969 + 3 ^ 40 * 2296690 * 2
def baseEnd_2296690 : Nat := 1179305884374724423512721

theorem tailTrace_2296690 : CollatzResearch.WordTrace tailWord_2296690 prefixEnd_2296690 1179305884374724423512721 := by
  unfold tailWord_2296690
  simp only [CollatzResearch.WordTrace]
  refine ⟨20941791512372962067253881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55844777366327898846010349 20941791512372962067253881)
  ·
    refine ⟨15706343634279721550440411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20941791512372962067253881 15706343634279721550440411)
    ·
      refine ⟨23559515451419582325660617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15706343634279721550440411 23559515451419582325660617)
      ·
        refine ⟨17669636588564686744245463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23559515451419582325660617 17669636588564686744245463)
        ·
          refine ⟨26504454882847030116368195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17669636588564686744245463 26504454882847030116368195)
          ·
            refine ⟨39756682324270545174552293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26504454882847030116368195 39756682324270545174552293)
            ·
              refine ⟨7454377935800727220228555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39756682324270545174552293 7454377935800727220228555)
              ·
                refine ⟨11181566903701090830342833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7454377935800727220228555 11181566903701090830342833)
                ·
                  refine ⟨8386175177775818122757125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11181566903701090830342833 8386175177775818122757125)
                  ·
                    refine ⟨1572407845832965898016961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8386175177775818122757125 1572407845832965898016961)
                    ·
                      refine ⟨1179305884374724423512721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1572407845832965898016961 1179305884374724423512721)
                      ·
                        rfl

theorem cell23_2296690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 1, 2, 4, 2].length) (baseStart_2296690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2296690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2296690 prefixEnd_2296690 := by exact prefixLift 2296690
  have htrace : WordTrace (prefixWord ++ tailWord_2296690) baseStart_2296690 baseEnd_2296690 := by
    simpa [prefixWord, tailWord_2296690, baseEnd_2296690] using wordTrace_append hprefix tailTrace_2296690
  have hstable : (prefixWord ++ tailWord_2296690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2296690).length < 2 ^ (prefixWord ++ tailWord_2296690).sum := by decide
  have hdescent : baseEnd_2296690 < baseStart_2296690 := by decide
  rcases family_descends (prefixWord ++ tailWord_2296690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2296760 : List Nat := [2, 1, 2, 1, 2, 4, 3, 2, 1, 5]
def baseStart_2296760 : Nat := 118140960795 + 2296760 * 2 ^ 59
def prefixEnd_2296760 : Nat := 4983230072969 + 3 ^ 40 * 2296760 * 2
def baseEnd_2296760 : Nat := 393113942673513049879133

theorem tailTrace_2296760 : CollatzResearch.WordTrace tailWord_2296760 prefixEnd_2296760 393113942673513049879133 := by
  unfold tailWord_2296760
  simp only [CollatzResearch.WordTrace]
  refine ⟨41884859579619125112031867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55846479439492166816042489 41884859579619125112031867)
  ·
    refine ⟨62827289369428687668047801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41884859579619125112031867 62827289369428687668047801)
    ·
      refine ⟨47120467027071515751035851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62827289369428687668047801 47120467027071515751035851)
      ·
        refine ⟨70680700540607273626553777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47120467027071515751035851 70680700540607273626553777)
        ·
          refine ⟨53010525405455455219915333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70680700540607273626553777 53010525405455455219915333)
          ·
            refine ⟨9939473513522897853734125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53010525405455455219915333 9939473513522897853734125)
            ·
              refine ⟨3727302567571086695150297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9939473513522897853734125 3727302567571086695150297)
              ·
                refine ⟨2795476925678315021362723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3727302567571086695150297 2795476925678315021362723)
                ·
                  refine ⟨4193215388517472532044085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2795476925678315021362723 4193215388517472532044085)
                  ·
                    refine ⟨393113942673513049879133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4193215388517472532044085 393113942673513049879133)
                    ·
                      rfl

theorem cell23_2296760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 3, 2, 1, 5].length) (baseStart_2296760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2296760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2296760 prefixEnd_2296760 := by exact prefixLift 2296760
  have htrace : WordTrace (prefixWord ++ tailWord_2296760) baseStart_2296760 baseEnd_2296760 := by
    simpa [prefixWord, tailWord_2296760, baseEnd_2296760] using wordTrace_append hprefix tailTrace_2296760
  have hstable : (prefixWord ++ tailWord_2296760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2296760).length < 2 ^ (prefixWord ++ tailWord_2296760).sum := by decide
  have hdescent : baseEnd_2296760 < baseStart_2296760 := by decide
  rcases family_descends (prefixWord ++ tailWord_2296760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2296781 : List Nat := [1, 6, 3, 1, 1, 1, 2, 2, 6]
def baseStart_2296781 : Nat := 118140960795 + 2296781 * 2 ^ 59
def prefixEnd_2296781 : Nat := 4983230072969 + 3 ^ 40 * 2296781 * 2
def baseEnd_2296781 : Nat := 131039179012698174163867

theorem tailTrace_2296781 : CollatzResearch.WordTrace tailWord_2296781 prefixEnd_2296781 131039179012698174163867 := by
  unfold tailWord_2296781
  simp only [CollatzResearch.WordTrace]
  refine ⟨83770485092162170810578197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55846990061441447207052131 83770485092162170810578197)
  ·
    refine ⟨3926741488695101756745853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 83770485092162170810578197 3926741488695101756745853)
    ·
      refine ⟨1472528058260663158779695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3926741488695101756745853 1472528058260663158779695)
      ·
        refine ⟨2208792087390994738169543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1472528058260663158779695 2208792087390994738169543)
        ·
          refine ⟨3313188131086492107254315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2208792087390994738169543 3313188131086492107254315)
          ·
            refine ⟨4969782196629738160881473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3313188131086492107254315 4969782196629738160881473)
            ·
              refine ⟨3727336647472303620661105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4969782196629738160881473 3727336647472303620661105)
              ·
                refine ⟨2795502485604227715495829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3727336647472303620661105 2795502485604227715495829)
                ·
                  refine ⟨131039179012698174163867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2795502485604227715495829 131039179012698174163867)
                  ·
                    rfl

theorem cell23_2296781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 2, 2, 6].length) (baseStart_2296781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2296781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2296781 prefixEnd_2296781 := by exact prefixLift 2296781
  have htrace : WordTrace (prefixWord ++ tailWord_2296781) baseStart_2296781 baseEnd_2296781 := by
    simpa [prefixWord, tailWord_2296781, baseEnd_2296781] using wordTrace_append hprefix tailTrace_2296781
  have hstable : (prefixWord ++ tailWord_2296781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2296781).length < 2 ^ (prefixWord ++ tailWord_2296781).sum := by decide
  have hdescent : baseEnd_2296781 < baseStart_2296781 := by decide
  rcases family_descends (prefixWord ++ tailWord_2296781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2296807 : List Nat := [1, 1, 5, 2, 2, 1, 2, 3, 2, 4]
def baseStart_2296807 : Nat := 118140960795 + 2296807 * 2 ^ 59
def prefixEnd_2296807 : Nat := 4983230072969 + 3 ^ 40 * 2296807 * 2
def baseEnd_2296807 : Nat := 393121987203766821916561

theorem tailTrace_2296807 : CollatzResearch.WordTrace tailWord_2296807 prefixEnd_2296807 393121987203766821916561 := by
  unfold tailWord_2296807
  simp only [CollatzResearch.WordTrace]
  refine ⟨83771433390067977251024675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55847622260045318167349783 83771433390067977251024675)
  ·
    refine ⟨125657150085101965876537013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83771433390067977251024675 125657150085101965876537013)
    ·
      refine ⟨11780357820478309300925345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 125657150085101965876537013 11780357820478309300925345)
      ·
        refine ⟨8835268365358731975694009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11780357820478309300925345 8835268365358731975694009)
        ·
          refine ⟨6626451274019048981770507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8835268365358731975694009 6626451274019048981770507)
          ·
            refine ⟨9939676911028573472655761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6626451274019048981770507 9939676911028573472655761)
            ·
              refine ⟨7454757683271430104491821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9939676911028573472655761 7454757683271430104491821)
              ·
                refine ⟨2795534131226786289184433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7454757683271430104491821 2795534131226786289184433)
                ·
                  refine ⟨2096650598420089716888325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2795534131226786289184433 2096650598420089716888325)
                  ·
                    refine ⟨393121987203766821916561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2096650598420089716888325 393121987203766821916561)
                    ·
                      rfl

theorem cell23_2296807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 3, 2, 4].length) (baseStart_2296807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2296807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2296807 prefixEnd_2296807 := by exact prefixLift 2296807
  have htrace : WordTrace (prefixWord ++ tailWord_2296807) baseStart_2296807 baseEnd_2296807 := by
    simpa [prefixWord, tailWord_2296807, baseEnd_2296807] using wordTrace_append hprefix tailTrace_2296807
  have hstable : (prefixWord ++ tailWord_2296807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2296807).length < 2 ^ (prefixWord ++ tailWord_2296807).sum := by decide
  have hdescent : baseEnd_2296807 < baseStart_2296807 := by decide
  rcases family_descends (prefixWord ++ tailWord_2296807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2296810 : List Nat := [3, 1, 3, 1, 2, 2, 1, 3, 1, 2, 4]
def baseStart_2296810 : Nat := 118140960795 + 2296810 * 2 ^ 59
def prefixEnd_2296810 : Nat := 4983230072969 + 3 ^ 40 * 2296810 * 2
def baseEnd_2296810 : Nat := 1179367502053263954012169

theorem tailTrace_2296810 : CollatzResearch.WordTrace tailWord_2296810 prefixEnd_2296810 1179367502053263954012169 := by
  unfold tailWord_2296810
  simp only [CollatzResearch.WordTrace]
  refine ⟨20942885702264277190845971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55847695206038072508922589 20942885702264277190845971)
  ·
    refine ⟨31414328553396415786268957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20942885702264277190845971 31414328553396415786268957)
    ·
      refine ⟨11780373207523655919850859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31414328553396415786268957 11780373207523655919850859)
      ·
        refine ⟨17670559811285483879776289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11780373207523655919850859 17670559811285483879776289)
        ·
          refine ⟨13252919858464112909832217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17670559811285483879776289 13252919858464112909832217)
          ·
            refine ⟨9939689893848084682374163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13252919858464112909832217 9939689893848084682374163)
            ·
              refine ⟨14909534840772127023561245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9939689893848084682374163 14909534840772127023561245)
              ·
                refine ⟨5591075565289547633835467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14909534840772127023561245 5591075565289547633835467)
                ·
                  refine ⟨8386613347934321450753201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5591075565289547633835467 8386613347934321450753201)
                  ·
                    refine ⟨6289960010950741088064901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8386613347934321450753201 6289960010950741088064901)
                    ·
                      refine ⟨1179367502053263954012169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6289960010950741088064901 1179367502053263954012169)
                      ·
                        rfl

theorem cell23_2296810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 3, 1, 2, 4].length) (baseStart_2296810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2296810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2296810 prefixEnd_2296810 := by exact prefixLift 2296810
  have htrace : WordTrace (prefixWord ++ tailWord_2296810) baseStart_2296810 baseEnd_2296810 := by
    simpa [prefixWord, tailWord_2296810, baseEnd_2296810] using wordTrace_append hprefix tailTrace_2296810
  have hstable : (prefixWord ++ tailWord_2296810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2296810).length < 2 ^ (prefixWord ++ tailWord_2296810).sum := by decide
  have hdescent : baseEnd_2296810 < baseStart_2296810 := by decide
  rcases family_descends (prefixWord ++ tailWord_2296810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2296818 : List Nat := [3, 2, 1, 5, 2, 1, 1, 1, 2, 3, 2]
def baseStart_2296818 : Nat := 118140960795 + 2296818 * 2 ^ 59
def prefixEnd_2296818 : Nat := 4983230072969 + 3 ^ 40 * 2296818 * 2
def baseEnd_2296818 : Nat := 1179371609898499922712133

theorem tailTrace_2296818 : CollatzResearch.WordTrace tailWord_2296818 prefixEnd_2296818 1179371609898499922712133 := by
  unfold tailWord_2296818
  simp only [CollatzResearch.WordTrace]
  refine ⟨20942958648257031532418777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55847889728685417419783405 20942958648257031532418777)
  ·
    refine ⟨15707218986192773649314083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20942958648257031532418777 15707218986192773649314083)
    ·
      refine ⟨23560828479289160473971125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15707218986192773649314083 23560828479289160473971125)
      ·
        refine ⟨2208827669933358794434793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23560828479289160473971125 2208827669933358794434793)
        ·
          refine ⟨1656620752450019095826095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2208827669933358794434793 1656620752450019095826095)
          ·
            refine ⟨2484931128675028643739143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1656620752450019095826095 2484931128675028643739143)
            ·
              refine ⟨3727396693012542965608715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2484931128675028643739143 3727396693012542965608715)
              ·
                refine ⟨5591095039518814448413073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3727396693012542965608715 5591095039518814448413073)
                ·
                  refine ⟨4193321279639110836309805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5591095039518814448413073 4193321279639110836309805)
                  ·
                    refine ⟨1572495479864666563616177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4193321279639110836309805 1572495479864666563616177)
                    ·
                      refine ⟨1179371609898499922712133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1572495479864666563616177 1179371609898499922712133)
                      ·
                        rfl

theorem cell23_2296818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_2296818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2296818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2296818 prefixEnd_2296818 := by exact prefixLift 2296818
  have htrace : WordTrace (prefixWord ++ tailWord_2296818) baseStart_2296818 baseEnd_2296818 := by
    simpa [prefixWord, tailWord_2296818, baseEnd_2296818] using wordTrace_append hprefix tailTrace_2296818
  have hstable : (prefixWord ++ tailWord_2296818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2296818).length < 2 ^ (prefixWord ++ tailWord_2296818).sum := by decide
  have hdescent : baseEnd_2296818 < baseStart_2296818 := by decide
  rcases family_descends (prefixWord ++ tailWord_2296818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2296904 : List Nat := [2, 1, 3, 1, 1, 1, 4, 4, 2, 2, 2]
def baseStart_2296904 : Nat := 118140960795 + 2296904 * 2 ^ 59
def prefixEnd_2296904 : Nat := 4983230072969 + 3 ^ 40 * 2296904 * 2
def baseEnd_2296904 : Nat := 1179415769234786586236737

theorem tailTrace_2296904 : CollatzResearch.WordTrace tailWord_2296904 prefixEnd_2296904 1179415769234786586236737 := by
  unfold tailWord_2296904
  simp only [CollatzResearch.WordTrace]
  refine ⟨41887485635358281408652883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55849980847144375211537177 41887485635358281408652883)
  ·
    refine ⟨62831228453037422112979325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41887485635358281408652883 62831228453037422112979325)
    ·
      refine ⟨23561710669889033292367247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62831228453037422112979325 23561710669889033292367247)
      ·
        refine ⟨35342566004833549938550871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23561710669889033292367247 35342566004833549938550871)
        ·
          refine ⟨53013849007250324907826307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35342566004833549938550871 53013849007250324907826307)
          ·
            refine ⟨79520773510875487361739461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53013849007250324907826307 79520773510875487361739461)
            ·
              refine ⟨14910145033289153880326149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 79520773510875487361739461 14910145033289153880326149)
              ·
                refine ⟨2795652193741716352561153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14910145033289153880326149 2795652193741716352561153)
                ·
                  refine ⟨2096739145306287264420865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2795652193741716352561153 2096739145306287264420865)
                  ·
                    refine ⟨1572554358979715448315649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2096739145306287264420865 1572554358979715448315649)
                    ·
                      refine ⟨1179415769234786586236737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1572554358979715448315649 1179415769234786586236737)
                      ·
                        rfl

theorem cell23_2296904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 4, 2, 2, 2].length) (baseStart_2296904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2296904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2296904 prefixEnd_2296904 := by exact prefixLift 2296904
  have htrace : WordTrace (prefixWord ++ tailWord_2296904) baseStart_2296904 baseEnd_2296904 := by
    simpa [prefixWord, tailWord_2296904, baseEnd_2296904] using wordTrace_append hprefix tailTrace_2296904
  have hstable : (prefixWord ++ tailWord_2296904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2296904).length < 2 ^ (prefixWord ++ tailWord_2296904).sum := by decide
  have hdescent : baseEnd_2296904 < baseStart_2296904 := by decide
  rcases family_descends (prefixWord ++ tailWord_2296904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2296920 : List Nat := [2, 1, 2, 2, 1, 3, 2, 1, 1, 5, 3]
def baseStart_2296920 : Nat := 118140960795 + 2296920 * 2 ^ 59
def prefixEnd_2296920 : Nat := 4983230072969 + 3 ^ 40 * 2296920 * 2
def baseEnd_2296920 : Nat := 1179423984925258523636663

theorem tailTrace_2296920 : CollatzResearch.WordTrace tailWord_2296920 prefixEnd_2296920 1179423984925258523636663 := by
  unfold tailWord_2296920
  simp only [CollatzResearch.WordTrace]
  refine ⟨41887777419329298774944107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55850369892439065033258809 41887777419329298774944107)
  ·
    refine ⟨62831666128993948162416161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41887777419329298774944107 62831666128993948162416161)
    ·
      refine ⟨47123749596745461121812121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62831666128993948162416161 47123749596745461121812121)
      ·
        refine ⟨35342812197559095841359091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47123749596745461121812121 35342812197559095841359091)
        ·
          refine ⟨53014218296338643762038637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35342812197559095841359091 53014218296338643762038637)
          ·
            refine ⟨19880331861126991410764489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53014218296338643762038637 19880331861126991410764489)
            ·
              refine ⟨14910248895845243558073367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19880331861126991410764489 14910248895845243558073367)
              ·
                refine ⟨22365373343767865337110051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14910248895845243558073367 22365373343767865337110051)
                ·
                  refine ⟨33548060015651798005665077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22365373343767865337110051 33548060015651798005665077)
                  ·
                    refine ⟨3145130626467356063031101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33548060015651798005665077 3145130626467356063031101)
                    ·
                      refine ⟨1179423984925258523636663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3145130626467356063031101 1179423984925258523636663)
                      ·
                        rfl

theorem cell23_2296920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 1, 1, 5, 3].length) (baseStart_2296920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2296920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2296920 prefixEnd_2296920 := by exact prefixLift 2296920
  have htrace : WordTrace (prefixWord ++ tailWord_2296920) baseStart_2296920 baseEnd_2296920 := by
    simpa [prefixWord, tailWord_2296920, baseEnd_2296920] using wordTrace_append hprefix tailTrace_2296920
  have hstable : (prefixWord ++ tailWord_2296920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2296920).length < 2 ^ (prefixWord ++ tailWord_2296920).sum := by decide
  have hdescent : baseEnd_2296920 < baseStart_2296920 := by decide
  rcases family_descends (prefixWord ++ tailWord_2296920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2296925 : List Nat := [1, 4, 4, 1, 3, 1, 1, 2, 1, 3, 2]
def baseStart_2296925 : Nat := 118140960795 + 2296925 * 2 ^ 59
def prefixEnd_2296925 : Nat := 4983230072969 + 3 ^ 40 * 2296925 * 2
def baseEnd_2296925 : Nat := 1179426552328531004074141

theorem tailTrace_2296925 : CollatzResearch.WordTrace tailWord_2296925 prefixEnd_2296925 1179426552328531004074141 := by
  unfold tailWord_2296925
  simp only [CollatzResearch.WordTrace]
  refine ⟨83775737203640483403820229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55850491469093655602546819 83775737203640483403820229)
  ·
    refine ⟨15707950725682590638216293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83775737203640483403820229 15707950725682590638216293)
    ·
      refine ⟨2945240761065485744665555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15707950725682590638216293 2945240761065485744665555)
      ·
        refine ⟨4417861141598228616998333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2945240761065485744665555 4417861141598228616998333)
        ·
          refine ⟨1656697928099335731374375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4417861141598228616998333 1656697928099335731374375)
          ·
            refine ⟨2485046892149003597061563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1656697928099335731374375 2485046892149003597061563)
            ·
              refine ⟨3727570338223505395592345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2485046892149003597061563 3727570338223505395592345)
              ·
                refine ⟨2795677753667629046694259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3727570338223505395592345 2795677753667629046694259)
                ·
                  refine ⟨4193516630501443570041389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2795677753667629046694259 4193516630501443570041389)
                  ·
                    refine ⟨1572568736438041338765521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4193516630501443570041389 1572568736438041338765521)
                    ·
                      refine ⟨1179426552328531004074141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1572568736438041338765521 1179426552328531004074141)
                      ·
                        rfl

theorem cell23_2296925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 1, 2, 1, 3, 2].length) (baseStart_2296925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2296925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2296925 prefixEnd_2296925 := by exact prefixLift 2296925
  have htrace : WordTrace (prefixWord ++ tailWord_2296925) baseStart_2296925 baseEnd_2296925 := by
    simpa [prefixWord, tailWord_2296925, baseEnd_2296925] using wordTrace_append hprefix tailTrace_2296925
  have hstable : (prefixWord ++ tailWord_2296925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2296925).length < 2 ^ (prefixWord ++ tailWord_2296925).sum := by decide
  have hdescent : baseEnd_2296925 < baseStart_2296925 := by decide
  rcases family_descends (prefixWord ++ tailWord_2296925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2296961 : List Nat := [1, 2, 4, 2, 2, 3, 2, 2, 5]
def baseStart_2296961 : Nat := 118140960795 + 2296961 * 2 ^ 59
def prefixEnd_2296961 : Nat := 4983230072969 + 3 ^ 40 * 2296961 * 2
def baseEnd_2296961 : Nat := 131049448625788095913775

theorem tailTrace_2296961 : CollatzResearch.WordTrace tailWord_2296961 prefixEnd_2296961 131049448625788095913775 := by
  unfold tailWord_2296961
  simp only [CollatzResearch.WordTrace]
  refine ⟨83777050231510061552130737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55851366821006707701420491 83777050231510061552130737)
  ·
    refine ⟨62832787673632546164098053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83777050231510061552130737 62832787673632546164098053)
    ·
      refine ⟨11781147688806102405768385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62832787673632546164098053 11781147688806102405768385)
      ·
        refine ⟨8835860766604576804326289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11781147688806102405768385 8835860766604576804326289)
        ·
          refine ⟨6626895574953432603244717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8835860766604576804326289 6626895574953432603244717)
          ·
            refine ⟨2485085840607537226216769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6626895574953432603244717 2485085840607537226216769)
            ·
              refine ⟨1863814380455652919662577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2485085840607537226216769 1863814380455652919662577)
              ·
                refine ⟨1397860785341739689746933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1863814380455652919662577 1397860785341739689746933)
                ·
                  refine ⟨131049448625788095913775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1397860785341739689746933 131049448625788095913775)
                  ·
                    rfl

theorem cell23_2296961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 2, 2, 5].length) (baseStart_2296961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2296961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2296961 prefixEnd_2296961 := by exact prefixLift 2296961
  have htrace : WordTrace (prefixWord ++ tailWord_2296961) baseStart_2296961 baseEnd_2296961 := by
    simpa [prefixWord, tailWord_2296961, baseEnd_2296961] using wordTrace_append hprefix tailTrace_2296961
  have hstable : (prefixWord ++ tailWord_2296961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2296961).length < 2 ^ (prefixWord ++ tailWord_2296961).sum := by decide
  have hdescent : baseEnd_2296961 < baseStart_2296961 := by decide
  rcases family_descends (prefixWord ++ tailWord_2296961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2296991 : List Nat := [1, 1, 2, 6, 3, 1, 1, 1, 2, 5]
def baseStart_2296991 : Nat := 118140960795 + 2296991 * 2 ^ 59
def prefixEnd_2296991 : Nat := 4983230072969 + 3 ^ 40 * 2296991 * 2
def baseEnd_2296991 : Nat := 393153480683909248616279

theorem tailTrace_2296991 : CollatzResearch.WordTrace tailWord_2296991 prefixEnd_2296991 393153480683909248616279 := by
  unfold tailWord_2296991
  simp only [CollatzResearch.WordTrace]
  refine ⟨83778144421401376675722827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55852096280934251117148551 83778144421401376675722827)
  ·
    refine ⟨125667216632102065013584241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83778144421401376675722827 125667216632102065013584241)
    ·
      refine ⟨94250412474076548760188181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125667216632102065013584241 94250412474076548760188181)
      ·
        refine ⟨4417988084722338223133821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 94250412474076548760188181 4417988084722338223133821)
        ·
          refine ⟨1656745531770876833675183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4417988084722338223133821 1656745531770876833675183)
          ·
            refine ⟨2485118297656315250512775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1656745531770876833675183 2485118297656315250512775)
            ·
              refine ⟨3727677446484472875769163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2485118297656315250512775 3727677446484472875769163)
              ·
                refine ⟨5591516169726709313653745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3727677446484472875769163 5591516169726709313653745)
                ·
                  refine ⟨4193637127295031985240309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5591516169726709313653745 4193637127295031985240309)
                  ·
                    refine ⟨393153480683909248616279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4193637127295031985240309 393153480683909248616279)
                    ·
                      rfl

theorem cell23_2296991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 1, 1, 2, 5].length) (baseStart_2296991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2296991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2296991 prefixEnd_2296991 := by exact prefixLift 2296991
  have htrace : WordTrace (prefixWord ++ tailWord_2296991) baseStart_2296991 baseEnd_2296991 := by
    simpa [prefixWord, tailWord_2296991, baseEnd_2296991] using wordTrace_append hprefix tailTrace_2296991
  have hstable : (prefixWord ++ tailWord_2296991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2296991).length < 2 ^ (prefixWord ++ tailWord_2296991).sum := by decide
  have hdescent : baseEnd_2296991 < baseStart_2296991 := by decide
  rcases family_descends (prefixWord ++ tailWord_2296991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2296994 : List Nat := [3, 3, 1, 3, 2, 1, 1, 1, 1, 3, 4]
def baseStart_2296994 : Nat := 118140960795 + 2296994 * 2 ^ 59
def prefixEnd_2296994 : Nat := 4983230072969 + 3 ^ 40 * 2296994 * 2
def baseEnd_2296994 : Nat := 1179461982493691234111323

theorem tailTrace_2296994 : CollatzResearch.WordTrace tailWord_2296994 prefixEnd_2296994 1179461982493691234111323 := by
  unfold tailWord_2296994
  simp only [CollatzResearch.WordTrace]
  refine ⟨20944563460097627047020509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55852169226927005458721357 20944563460097627047020509)
  ·
    refine ⟨7854211297536610142632691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20944563460097627047020509 7854211297536610142632691)
    ·
      refine ⟨11781316946304915213949037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7854211297536610142632691 11781316946304915213949037)
      ·
        refine ⟨4417993854864343205230889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11781316946304915213949037 4417993854864343205230889)
        ·
          refine ⟨3313495391148257403923167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4417993854864343205230889 3313495391148257403923167)
          ·
            refine ⟨4970243086722386105884751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3313495391148257403923167 4970243086722386105884751)
            ·
              refine ⟨7455364630083579158827127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4970243086722386105884751 7455364630083579158827127)
              ·
                refine ⟨11183046945125368738240691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7455364630083579158827127 11183046945125368738240691)
                ·
                  refine ⟨16774570417688053107361037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11183046945125368738240691 16774570417688053107361037)
                  ·
                    refine ⟨6290463906633019915260389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16774570417688053107361037 6290463906633019915260389)
                    ·
                      refine ⟨1179461982493691234111323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6290463906633019915260389 1179461982493691234111323)
                      ·
                        rfl

theorem cell23_2296994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_2296994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2296994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2296994 prefixEnd_2296994 := by exact prefixLift 2296994
  have htrace : WordTrace (prefixWord ++ tailWord_2296994) baseStart_2296994 baseEnd_2296994 := by
    simpa [prefixWord, tailWord_2296994, baseEnd_2296994] using wordTrace_append hprefix tailTrace_2296994
  have hstable : (prefixWord ++ tailWord_2296994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2296994).length < 2 ^ (prefixWord ++ tailWord_2296994).sum := by decide
  have hdescent : baseEnd_2296994 < baseStart_2296994 := by decide
  rcases family_descends (prefixWord ++ tailWord_2296994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2296997 : List Nat := [1, 3, 1, 2, 1, 5, 1, 1, 1, 4, 3]
def baseStart_2296997 : Nat := 118140960795 + 2296997 * 2 ^ 59
def prefixEnd_2296997 : Nat := 4983230072969 + 3 ^ 40 * 2296997 * 2
def baseEnd_2296997 : Nat := 1179463522935654722373809

theorem tailTrace_2296997 : CollatzResearch.WordTrace tailWord_2296997 prefixEnd_2296997 1179463522935654722373809 := by
  unfold tailWord_2296997
  simp only [CollatzResearch.WordTrace]
  refine ⟨83778363259379639700441245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55852242172919759800294163 83778363259379639700441245)
  ·
    refine ⟨31416886222267364887665467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83778363259379639700441245 31416886222267364887665467)
    ·
      refine ⟨47125329333401047331498201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31416886222267364887665467 47125329333401047331498201)
      ·
        refine ⟨35343997000050785498623651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47125329333401047331498201 35343997000050785498623651)
        ·
          refine ⟨53015995500076178247935477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35343997000050785498623651 53015995500076178247935477)
          ·
            refine ⟨4970249578132141710743951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 53015995500076178247935477 4970249578132141710743951)
            ·
              refine ⟨7455374367198212566115927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4970249578132141710743951 7455374367198212566115927)
              ·
                refine ⟨11183061550797318849173891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7455374367198212566115927 11183061550797318849173891)
                ·
                  refine ⟨16774592326195978273760837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11183061550797318849173891 16774592326195978273760837)
                  ·
                    refine ⟨3145236061161745926330157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16774592326195978273760837 3145236061161745926330157)
                    ·
                      refine ⟨1179463522935654722373809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3145236061161745926330157 1179463522935654722373809)
                      ·
                        rfl

theorem cell23_2296997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 1, 1, 4, 3].length) (baseStart_2296997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2296997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2296997 prefixEnd_2296997 := by exact prefixLift 2296997
  have htrace : WordTrace (prefixWord ++ tailWord_2296997) baseStart_2296997 baseEnd_2296997 := by
    simpa [prefixWord, tailWord_2296997, baseEnd_2296997] using wordTrace_append hprefix tailTrace_2296997
  have hstable : (prefixWord ++ tailWord_2296997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2296997).length < 2 ^ (prefixWord ++ tailWord_2296997).sum := by decide
  have hdescent : baseEnd_2296997 < baseStart_2296997 := by decide
  rcases family_descends (prefixWord ++ tailWord_2296997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2297017 : List Nat := [1, 2, 1, 4, 1, 3, 3, 2, 6]
def baseStart_2297017 : Nat := 118140960795 + 2297017 * 2 ^ 59
def prefixEnd_2297017 : Nat := 4983230072969 + 3 ^ 40 * 2297017 * 2
def baseEnd_2297017 : Nat := 131052643616527182680413

theorem tailTrace_2297017 : CollatzResearch.WordTrace tailWord_2297017 prefixEnd_2297017 131052643616527182680413 := by
  unfold tailWord_2297017
  simp only [CollatzResearch.WordTrace]
  refine ⟨83779092719307183116169305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55852728479538122077446203 83779092719307183116169305)
  ·
    refine ⟨62834319539480387337126979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83779092719307183116169305 62834319539480387337126979)
    ·
      refine ⟨94251479309220581005690469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62834319539480387337126979 94251479309220581005690469)
      ·
        refine ⟨17672152370478858938566963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 94251479309220581005690469 17672152370478858938566963)
        ·
          refine ⟨26508228555718288407850445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17672152370478858938566963 26508228555718288407850445)
          ·
            refine ⟨9940585708394358152943917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26508228555718288407850445 9940585708394358152943917)
            ·
              refine ⟨3727719640647884307353969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9940585708394358152943917 3727719640647884307353969)
              ·
                refine ⟨2795789730485913230515477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3727719640647884307353969 2795789730485913230515477)
                ·
                  refine ⟨131052643616527182680413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2795789730485913230515477 131052643616527182680413)
                  ·
                    rfl

theorem cell23_2297017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 3, 2, 6].length) (baseStart_2297017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2297017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2297017 prefixEnd_2297017 := by exact prefixLift 2297017
  have htrace : WordTrace (prefixWord ++ tailWord_2297017) baseStart_2297017 baseEnd_2297017 := by
    simpa [prefixWord, tailWord_2297017, baseEnd_2297017] using wordTrace_append hprefix tailTrace_2297017
  have hstable : (prefixWord ++ tailWord_2297017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2297017).length < 2 ^ (prefixWord ++ tailWord_2297017).sum := by decide
  have hdescent : baseEnd_2297017 < baseStart_2297017 := by decide
  rcases family_descends (prefixWord ++ tailWord_2297017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2297034 : List Nat := [3, 1, 2, 1, 3, 3, 3, 1, 6]
def baseStart_2297034 : Nat := 118140960795 + 2297034 * 2 ^ 59
def prefixEnd_2297034 : Nat := 4983230072969 + 3 ^ 40 * 2297034 * 2
def baseEnd_2297034 : Nat := 131053613524430119734571

theorem tailTrace_2297034 : CollatzResearch.WordTrace tailWord_2297034 prefixEnd_2297034 131053613524430119734571 := by
  unfold tailWord_2297034
  simp only [CollatzResearch.WordTrace]
  refine ⟨20944928190061398754884539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55853141840163730013025437 20944928190061398754884539)
  ·
    refine ⟨31417392285092098132326809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20944928190061398754884539 31417392285092098132326809)
    ·
      refine ⟨23563044213819073599245107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31417392285092098132326809 23563044213819073599245107)
      ·
        refine ⟨35344566320728610398867661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23563044213819073599245107 35344566320728610398867661)
        ·
          refine ⟨13254212370273228899575373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35344566320728610398867661 13254212370273228899575373)
          ·
            refine ⟨4970329638852460837340765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13254212370273228899575373 4970329638852460837340765)
            ·
              refine ⟨1863873614569672814002787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4970329638852460837340765 1863873614569672814002787)
              ·
                refine ⟨2795810421854509221004181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1863873614569672814002787 2795810421854509221004181)
                ·
                  refine ⟨131053613524430119734571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2795810421854509221004181 131053613524430119734571)
                  ·
                    rfl

theorem cell23_2297034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 3, 1, 6].length) (baseStart_2297034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2297034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2297034 prefixEnd_2297034 := by exact prefixLift 2297034
  have htrace : WordTrace (prefixWord ++ tailWord_2297034) baseStart_2297034 baseEnd_2297034 := by
    simpa [prefixWord, tailWord_2297034, baseEnd_2297034] using wordTrace_append hprefix tailTrace_2297034
  have hstable : (prefixWord ++ tailWord_2297034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2297034).length < 2 ^ (prefixWord ++ tailWord_2297034).sum := by decide
  have hdescent : baseEnd_2297034 < baseStart_2297034 := by decide
  rcases family_descends (prefixWord ++ tailWord_2297034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2297047 : List Nat := [1, 1, 3, 2, 1, 2, 3, 4, 1, 5]
def baseStart_2297047 : Nat := 118140960795 + 2297047 * 2 ^ 59
def prefixEnd_2297047 : Nat := 4983230072969 + 3 ^ 40 * 2297047 * 2
def baseEnd_2297047 : Nat := 393163065656126508916193

theorem tailTrace_2297047 : CollatzResearch.WordTrace tailWord_2297047 prefixEnd_2297047 393163065656126508916193 := by
  unfold tailWord_2297047
  simp only [CollatzResearch.WordTrace]
  refine ⟨83780186909198498239761395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55853457939465665493174263 83780186909198498239761395)
  ·
    refine ⟨125670280363797747359642093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83780186909198498239761395 125670280363797747359642093)
    ·
      refine ⟨47126355136424155259865785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 125670280363797747359642093 47126355136424155259865785)
      ·
        refine ⟨35344766352318116444899339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47126355136424155259865785 35344766352318116444899339)
        ·
          refine ⟨53017149528477174667349009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35344766352318116444899339 53017149528477174667349009)
          ·
            refine ⟨39762862146357881000511757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53017149528477174667349009 39762862146357881000511757)
            ·
              refine ⟨14911073304884205375191909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39762862146357881000511757 14911073304884205375191909)
              ·
                refine ⟨2795826244665788507848483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14911073304884205375191909 2795826244665788507848483)
                ·
                  refine ⟨4193739366998682761772725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2795826244665788507848483 4193739366998682761772725)
                  ·
                    refine ⟨393163065656126508916193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4193739366998682761772725 393163065656126508916193)
                    ·
                      rfl

theorem cell23_2297047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 4, 1, 5].length) (baseStart_2297047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2297047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2297047 prefixEnd_2297047 := by exact prefixLift 2297047
  have htrace : WordTrace (prefixWord ++ tailWord_2297047) baseStart_2297047 baseEnd_2297047 := by
    simpa [prefixWord, tailWord_2297047, baseEnd_2297047] using wordTrace_append hprefix tailTrace_2297047
  have hstable : (prefixWord ++ tailWord_2297047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2297047).length < 2 ^ (prefixWord ++ tailWord_2297047).sum := by decide
  have hdescent : baseEnd_2297047 < baseStart_2297047 := by decide
  rcases family_descends (prefixWord ++ tailWord_2297047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2297071 : List Nat := [1, 1, 2, 1, 7, 1, 1, 2, 2, 3, 2]
def baseStart_2297071 : Nat := 118140960795 + 2297071 * 2 ^ 59
def prefixEnd_2297071 : Nat := 4983230072969 + 3 ^ 40 * 2297071 * 2
def baseEnd_2297071 : Nat := 1179501520504087432848469

theorem tailTrace_2297071 : CollatzResearch.WordTrace tailWord_2297071 prefixEnd_2297071 1179501520504087432848469 := by
  unfold tailWord_2297071
  simp only [CollatzResearch.WordTrace]
  refine ⟨83781062261111550338635067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55854041507407700225756711 83781062261111550338635067)
  ·
    refine ⟨125671593391667325507952601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83781062261111550338635067 125671593391667325507952601)
    ·
      refine ⟨94253695043750494130964451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125671593391667325507952601 94253695043750494130964451)
      ·
        refine ⟨141380542565625741196446677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94253695043750494130964451 141380542565625741196446677)
        ·
          refine ⟨3313606466381853309291719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 141380542565625741196446677 3313606466381853309291719)
          ·
            refine ⟨4970409699572779963937579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3313606466381853309291719 4970409699572779963937579)
            ·
              refine ⟨7455614549359169945906369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4970409699572779963937579 7455614549359169945906369)
              ·
                refine ⟨5591710912019377459429777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7455614549359169945906369 5591710912019377459429777)
                ·
                  refine ⟨4193783184014533094572333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5591710912019377459429777 4193783184014533094572333)
                  ·
                    refine ⟨1572668694005449910464625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4193783184014533094572333 1572668694005449910464625)
                    ·
                      refine ⟨1179501520504087432848469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1572668694005449910464625 1179501520504087432848469)
                      ·
                        rfl

theorem cell23_2297071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 2, 2, 3, 2].length) (baseStart_2297071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2297071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2297071 prefixEnd_2297071 := by exact prefixLift 2297071
  have htrace : WordTrace (prefixWord ++ tailWord_2297071) baseStart_2297071 baseEnd_2297071 := by
    simpa [prefixWord, tailWord_2297071, baseEnd_2297071] using wordTrace_append hprefix tailTrace_2297071
  have hstable : (prefixWord ++ tailWord_2297071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2297071).length < 2 ^ (prefixWord ++ tailWord_2297071).sum := by decide
  have hdescent : baseEnd_2297071 < baseStart_2297071 := by decide
  rcases family_descends (prefixWord ++ tailWord_2297071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2297087 : List Nat := [1, 1, 2, 2, 1, 5, 2, 2, 1, 1, 5]
def baseStart_2297087 : Nat := 118140960795 + 2297087 * 2 ^ 59
def prefixEnd_2297087 : Nat := 4983230072969 + 3 ^ 40 * 2297087 * 2
def baseEnd_2297087 : Nat := 1179509736194559370248395

theorem tailTrace_2297087 : CollatzResearch.WordTrace tailWord_2297087 prefixEnd_2297087 1179509736194559370248395 := by
  unfold tailWord_2297087
  simp only [CollatzResearch.WordTrace]
  refine ⟨83781645829053585071217515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55854430552702390047478343 83781645829053585071217515)
  ·
    refine ⟨125672468743580377606826273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83781645829053585071217515 125672468743580377606826273)
    ·
      refine ⟨94254351557685283205119705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125672468743580377606826273 94254351557685283205119705)
      ·
        refine ⟨70690763668263962403839779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94254351557685283205119705 70690763668263962403839779)
        ·
          refine ⟨106036145502395943605759669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70690763668263962403839779 106036145502395943605759669)
          ·
            refine ⟨9940888640849619713039969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 106036145502395943605759669 9940888640849619713039969)
            ·
              refine ⟨7455666480637214784779977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9940888640849619713039969 7455666480637214784779977)
              ·
                refine ⟨5591749860477911088584983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7455666480637214784779977 5591749860477911088584983)
                ·
                  refine ⟨8387624790716866632877475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5591749860477911088584983 8387624790716866632877475)
                  ·
                    refine ⟨12581437186075299949316213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8387624790716866632877475 12581437186075299949316213)
                    ·
                      refine ⟨1179509736194559370248395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12581437186075299949316213 1179509736194559370248395)
                      ·
                        rfl

theorem cell23_2297087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 2, 1, 1, 5].length) (baseStart_2297087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2297087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2297087 prefixEnd_2297087 := by exact prefixLift 2297087
  have htrace : WordTrace (prefixWord ++ tailWord_2297087) baseStart_2297087 baseEnd_2297087 := by
    simpa [prefixWord, tailWord_2297087, baseEnd_2297087] using wordTrace_append hprefix tailTrace_2297087
  have hstable : (prefixWord ++ tailWord_2297087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2297087).length < 2 ^ (prefixWord ++ tailWord_2297087).sum := by decide
  have hdescent : baseEnd_2297087 < baseStart_2297087 := by decide
  rcases family_descends (prefixWord ++ tailWord_2297087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2297097 : List Nat := [1, 2, 1, 1, 3, 3, 2, 3, 1, 2, 4]
def baseStart_2297097 : Nat := 118140960795 + 2297097 * 2 ^ 59
def prefixEnd_2297097 : Nat := 4983230072969 + 3 ^ 40 * 2297097 * 2
def baseEnd_2297097 : Nat := 1179514871001104331123349

theorem tailTrace_2297097 : CollatzResearch.WordTrace tailWord_2297097 prefixEnd_2297097 1179514871001104331123349 := by
  unfold tailWord_2297097
  simp only [CollatzResearch.WordTrace]
  refine ⟨83782010559017356779081545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55854673706011571186054363 83782010559017356779081545)
  ·
    refine ⟨62836507919263017584311159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83782010559017356779081545 62836507919263017584311159)
    ·
      refine ⟨94254761878894526376466739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62836507919263017584311159 94254761878894526376466739)
      ·
        refine ⟨141382142818341789564700109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94254761878894526376466739 141382142818341789564700109)
        ·
          refine ⟨53018303556878171086762541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 141382142818341789564700109 53018303556878171086762541)
          ·
            refine ⟨19881863833829314157535953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53018303556878171086762541 19881863833829314157535953)
            ·
              refine ⟨14911397875371985618151965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19881863833829314157535953 14911397875371985618151965)
              ·
                refine ⟨5591774203264494606806987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14911397875371985618151965 5591774203264494606806987)
                ·
                  refine ⟨8387661304896741910210481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5591774203264494606806987 8387661304896741910210481)
                  ·
                    refine ⟨6290745978672556432657861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8387661304896741910210481 6290745978672556432657861)
                    ·
                      refine ⟨1179514871001104331123349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6290745978672556432657861 1179514871001104331123349)
                      ·
                        rfl

theorem cell23_2297097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 3, 1, 2, 4].length) (baseStart_2297097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2297097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2297097 prefixEnd_2297097 := by exact prefixLift 2297097
  have htrace : WordTrace (prefixWord ++ tailWord_2297097) baseStart_2297097 baseEnd_2297097 := by
    simpa [prefixWord, tailWord_2297097, baseEnd_2297097] using wordTrace_append hprefix tailTrace_2297097
  have hstable : (prefixWord ++ tailWord_2297097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2297097).length < 2 ^ (prefixWord ++ tailWord_2297097).sum := by decide
  have hdescent : baseEnd_2297097 < baseStart_2297097 := by decide
  rcases family_descends (prefixWord ++ tailWord_2297097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2297114 : List Nat := [3, 1, 1, 3, 3, 2, 1, 2, 1, 2, 4]
def baseStart_2297114 : Nat := 118140960795 + 2297114 * 2 ^ 59
def prefixEnd_2297114 : Nat := 4983230072969 + 3 ^ 40 * 2297114 * 2
def baseEnd_2297114 : Nat := 1179523600172230764610771

theorem tailTrace_2297114 : CollatzResearch.WordTrace tailWord_2297114 prefixEnd_2297114 1179523600172230764610771 := by
  unfold tailWord_2297114
  simp only [CollatzResearch.WordTrace]
  refine ⟨20945657649988942170612599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55855087066637179121633597 20945657649988942170612599)
  ·
    refine ⟨31418486474983413255918899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20945657649988942170612599 31418486474983413255918899)
    ·
      refine ⟨47127729712475119883878349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31418486474983413255918899 47127729712475119883878349)
      ·
        refine ⟨17672898642178169956454381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47127729712475119883878349 17672898642178169956454381)
        ·
          refine ⟨6627336990816813733670393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17672898642178169956454381 6627336990816813733670393)
          ·
            refine ⟨4970502743112610300252795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6627336990816813733670393 4970502743112610300252795)
            ·
              refine ⟨7455754114668915450379193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4970502743112610300252795 7455754114668915450379193)
              ·
                refine ⟨5591815586001686587784395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7455754114668915450379193 5591815586001686587784395)
                ·
                  refine ⟨8387723379002529881676593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5591815586001686587784395 8387723379002529881676593)
                  ·
                    refine ⟨6290792534251897411257445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8387723379002529881676593 6290792534251897411257445)
                    ·
                      refine ⟨1179523600172230764610771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6290792534251897411257445 1179523600172230764610771)
                      ·
                        rfl

theorem cell23_2297114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 2, 1, 2, 4].length) (baseStart_2297114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2297114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2297114 prefixEnd_2297114 := by exact prefixLift 2297114
  have htrace : WordTrace (prefixWord ++ tailWord_2297114) baseStart_2297114 baseEnd_2297114 := by
    simpa [prefixWord, tailWord_2297114, baseEnd_2297114] using wordTrace_append hprefix tailTrace_2297114
  have hstable : (prefixWord ++ tailWord_2297114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2297114).length < 2 ^ (prefixWord ++ tailWord_2297114).sum := by decide
  have hdescent : baseEnd_2297114 < baseStart_2297114 := by decide
  rcases family_descends (prefixWord ++ tailWord_2297114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2297137 : List Nat := [1, 2, 2, 3, 3, 1, 1, 1, 2, 7]
def baseStart_2297137 : Nat := 118140960795 + 2297137 * 2 ^ 59
def prefixEnd_2297137 : Nat := 4983230072969 + 3 ^ 40 * 2297137 * 2
def baseEnd_2297137 : Nat := 393178470075761391541055

theorem tailTrace_2297137 : CollatzResearch.WordTrace tailWord_2297137 prefixEnd_2297137 393178470075761391541055 := by
  unfold tailWord_2297137
  simp only [CollatzResearch.WordTrace]
  refine ⟨83783469478872443610537665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55855646319248295740358443 83783469478872443610537665)
  ·
    refine ⟨62837602109154332707903249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83783469478872443610537665 62837602109154332707903249)
    ·
      refine ⟨47128201581865749530927437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62837602109154332707903249 47128201581865749530927437)
      ·
        refine ⟨17673075593199656074097789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47128201581865749530927437 17673075593199656074097789)
        ·
          refine ⟨6627403347449871027786671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17673075593199656074097789 6627403347449871027786671)
          ·
            refine ⟨9941105021174806541680007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6627403347449871027786671 9941105021174806541680007)
            ·
              refine ⟨14911657531762209812520011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9941105021174806541680007 14911657531762209812520011)
              ·
                refine ⟨22367486297643314718780017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14911657531762209812520011 22367486297643314718780017)
                ·
                  refine ⟨16775614723232486039085013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22367486297643314718780017 16775614723232486039085013)
                  ·
                    refine ⟨393178470075761391541055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16775614723232486039085013 393178470075761391541055)
                    ·
                      rfl

theorem cell23_2297137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 1, 2, 7].length) (baseStart_2297137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2297137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2297137 prefixEnd_2297137 := by exact prefixLift 2297137
  have htrace : WordTrace (prefixWord ++ tailWord_2297137) baseStart_2297137 baseEnd_2297137 := by
    simpa [prefixWord, tailWord_2297137, baseEnd_2297137] using wordTrace_append hprefix tailTrace_2297137
  have hstable : (prefixWord ++ tailWord_2297137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2297137).length < 2 ^ (prefixWord ++ tailWord_2297137).sum := by decide
  have hdescent : baseEnd_2297137 < baseStart_2297137 := by decide
  rcases family_descends (prefixWord ++ tailWord_2297137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2297151 : List Nat := [1, 1, 2, 2, 4, 2, 2, 3, 2, 1, 3]
def baseStart_2297151 : Nat := 118140960795 + 2297151 * 2 ^ 59
def prefixEnd_2297151 : Nat := 4983230072969 + 3 ^ 40 * 2297151 * 2
def baseEnd_2297151 : Nat := 1179542598956447119848101

theorem tailTrace_2297151 : CollatzResearch.WordTrace tailWord_2297151 prefixEnd_2297151 1179542598956447119848101 := by
  unfold tailWord_2297151
  simp only [CollatzResearch.WordTrace]
  refine ⟨83783980100821724001547307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55855986733881149334364871 83783980100821724001547307)
  ·
    refine ⟨125675970151232586002320961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83783980100821724001547307 125675970151232586002320961)
    ·
      refine ⟨94256977613424439501740721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125675970151232586002320961 94256977613424439501740721)
      ·
        refine ⟨70692733210068329626305541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94256977613424439501740721 70692733210068329626305541)
        ·
          refine ⟨13254887476887811804932289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 70692733210068329626305541 13254887476887811804932289)
          ·
            refine ⟨9941165607665858853699217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13254887476887811804932289 9941165607665858853699217)
            ·
              refine ⟨7455874205749394140274413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9941165607665858853699217 7455874205749394140274413)
              ·
                refine ⟨2795952827156022802602905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7455874205749394140274413 2795952827156022802602905)
                ·
                  refine ⟨2096964620367017101952179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2795952827156022802602905 2096964620367017101952179)
                  ·
                    refine ⟨3145446930550525652928269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2096964620367017101952179 3145446930550525652928269)
                    ·
                      refine ⟨1179542598956447119848101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3145446930550525652928269 1179542598956447119848101)
                      ·
                        rfl

theorem cell23_2297151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 3, 2, 1, 3].length) (baseStart_2297151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2297151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2297151 prefixEnd_2297151 := by exact prefixLift 2297151
  have htrace : WordTrace (prefixWord ++ tailWord_2297151) baseStart_2297151 baseEnd_2297151 := by
    simpa [prefixWord, tailWord_2297151, baseEnd_2297151] using wordTrace_append hprefix tailTrace_2297151
  have hstable : (prefixWord ++ tailWord_2297151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2297151).length < 2 ^ (prefixWord ++ tailWord_2297151).sum := by decide
  have hdescent : baseEnd_2297151 < baseStart_2297151 := by decide
  rcases family_descends (prefixWord ++ tailWord_2297151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2297177 : List Nat := [1, 2, 1, 2, 2, 2, 2, 3, 2, 1, 5]
def baseStart_2297177 : Nat := 118140960795 + 2297177 * 2 ^ 59
def prefixEnd_2297177 : Nat := 4983230072969 + 3 ^ 40 * 2297177 * 2
def baseEnd_2297177 : Nat := 1179555949453464018122981

theorem tailTrace_2297177 : CollatzResearch.WordTrace tailWord_2297177 prefixEnd_2297177 1179555949453464018122981 := by
  unfold tailWord_2297177
  simp only [CollatzResearch.WordTrace]
  refine ⟨83784928398727530441993785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55856618932485020294662523 83784928398727530441993785)
  ·
    refine ⟨62838696299045647831495339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83784928398727530441993785 62838696299045647831495339)
    ·
      refine ⟨94258044448568471747243009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62838696299045647831495339 94258044448568471747243009)
      ·
        refine ⟨70693533336426353810432257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94258044448568471747243009 70693533336426353810432257)
        ·
          refine ⟨53020150002319765357824193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70693533336426353810432257 53020150002319765357824193)
          ·
            refine ⟨39765112501739824018368145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53020150002319765357824193 39765112501739824018368145)
            ·
              refine ⟨29823834376304868013776109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39765112501739824018368145 29823834376304868013776109)
              ·
                refine ⟨11183937891114325505166041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29823834376304868013776109 11183937891114325505166041)
                ·
                  refine ⟨8387953418335744128874531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11183937891114325505166041 8387953418335744128874531)
                  ·
                    refine ⟨12581930127503616193311797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8387953418335744128874531 12581930127503616193311797)
                    ·
                      refine ⟨1179555949453464018122981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12581930127503616193311797 1179555949453464018122981)
                      ·
                        rfl

theorem cell23_2297177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 3, 2, 1, 5].length) (baseStart_2297177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2297177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2297177 prefixEnd_2297177 := by exact prefixLift 2297177
  have htrace : WordTrace (prefixWord ++ tailWord_2297177) baseStart_2297177 baseEnd_2297177 := by
    simpa [prefixWord, tailWord_2297177, baseEnd_2297177] using wordTrace_append hprefix tailTrace_2297177
  have hstable : (prefixWord ++ tailWord_2297177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2297177).length < 2 ^ (prefixWord ++ tailWord_2297177).sum := by decide
  have hdescent : baseEnd_2297177 < baseStart_2297177 := by decide
  rcases family_descends (prefixWord ++ tailWord_2297177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2297178 : List Nat := [3, 1, 1, 2, 1, 2, 6, 1, 1, 3, 2]
def baseStart_2297178 : Nat := 118140960795 + 2297178 * 2 ^ 59
def prefixEnd_2297178 : Nat := 4983230072969 + 3 ^ 40 * 2297178 * 2
def baseEnd_2297178 : Nat := 1179556462934118514210477

theorem tailTrace_2297178 : CollatzResearch.WordTrace tailWord_2297178 prefixEnd_2297178 1179556462934118514210477 := by
  unfold tailWord_2297178
  simp only [CollatzResearch.WordTrace]
  refine ⟨20946241217930976903195047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55856643247815938408520125 20946241217930976903195047)
  ·
    refine ⟨31419361826896465354792571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20946241217930976903195047 31419361826896465354792571)
    ·
      refine ⟨47129042740344698032188857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31419361826896465354792571 47129042740344698032188857)
      ·
        refine ⟨35346782055258523524141643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47129042740344698032188857 35346782055258523524141643)
        ·
          refine ⟨53020173082887785286212465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35346782055258523524141643 53020173082887785286212465)
          ·
            refine ⟨39765129812165838964659349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53020173082887785286212465 39765129812165838964659349)
            ·
              refine ⟨1863990459945273701468407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 39765129812165838964659349 1863990459945273701468407)
              ·
                refine ⟨2795985689917910552202611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1863990459945273701468407 2795985689917910552202611)
                ·
                  refine ⟨4193978534876865828303917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2795985689917910552202611 4193978534876865828303917)
                  ·
                    refine ⟨1572741950578824685613969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4193978534876865828303917 1572741950578824685613969)
                    ·
                      refine ⟨1179556462934118514210477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1572741950578824685613969 1179556462934118514210477)
                      ·
                        rfl

theorem cell23_2297178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 6, 1, 1, 3, 2].length) (baseStart_2297178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2297178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2297178 prefixEnd_2297178 := by exact prefixLift 2297178
  have htrace : WordTrace (prefixWord ++ tailWord_2297178) baseStart_2297178 baseEnd_2297178 := by
    simpa [prefixWord, tailWord_2297178, baseEnd_2297178] using wordTrace_append hprefix tailTrace_2297178
  have hstable : (prefixWord ++ tailWord_2297178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2297178).length < 2 ^ (prefixWord ++ tailWord_2297178).sum := by decide
  have hdescent : baseEnd_2297178 < baseStart_2297178 := by decide
  rcases family_descends (prefixWord ++ tailWord_2297178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2297227 : List Nat := [1, 1, 1, 1, 4, 3, 1, 3, 1, 7]
def baseStart_2297227 : Nat := 118140960795 + 2297227 * 2 ^ 59
def prefixEnd_2297227 : Nat := 4983230072969 + 3 ^ 40 * 2297227 * 2
def baseEnd_2297227 : Nat := 393193874495396274165917

theorem tailTrace_2297227 : CollatzResearch.WordTrace tailWord_2297227 prefixEnd_2297227 393193874495396274165917 := by
  unfold tailWord_2297227
  simp only [CollatzResearch.WordTrace]
  refine ⟨83786752048546388981313935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55857834699030925987542623 83786752048546388981313935)
  ·
    refine ⟨125680128072819583471970903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83786752048546388981313935 125680128072819583471970903)
    ·
      refine ⟨188520192109229375207956355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125680128072819583471970903 188520192109229375207956355)
      ·
        refine ⟨282780288163844062811934533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188520192109229375207956355 282780288163844062811934533)
        ·
          refine ⟨53021304030720761777237725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 282780288163844062811934533 53021304030720761777237725)
          ·
            refine ⟨19882989011520285666464147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53021304030720761777237725 19882989011520285666464147)
            ·
              refine ⟨29824483517280428499696221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19882989011520285666464147 29824483517280428499696221)
              ·
                refine ⟨11184181318980160687386083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29824483517280428499696221 11184181318980160687386083)
                ·
                  refine ⟨16776271978470241031079125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11184181318980160687386083 16776271978470241031079125)
                  ·
                    refine ⟨393193874495396274165917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16776271978470241031079125 393193874495396274165917)
                    ·
                      rfl

theorem cell23_2297227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 3, 1, 7].length) (baseStart_2297227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2297227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2297227 prefixEnd_2297227 := by exact prefixLift 2297227
  have htrace : WordTrace (prefixWord ++ tailWord_2297227) baseStart_2297227 baseEnd_2297227 := by
    simpa [prefixWord, tailWord_2297227, baseEnd_2297227] using wordTrace_append hprefix tailTrace_2297227
  have hstable : (prefixWord ++ tailWord_2297227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2297227).length < 2 ^ (prefixWord ++ tailWord_2297227).sum := by decide
  have hdescent : baseEnd_2297227 < baseStart_2297227 := by decide
  rcases family_descends (prefixWord ++ tailWord_2297227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2297267 : List Nat := [1, 1, 1, 2, 3, 1, 1, 2, 1, 5, 5]
def baseStart_2297267 : Nat := 118140960795 + 2297267 * 2 ^ 59
def prefixEnd_2297267 : Nat := 4983230072969 + 3 ^ 40 * 2297267 * 2
def baseEnd_2297267 : Nat := 1179602162712368665997567

theorem tailTrace_2297267 : CollatzResearch.WordTrace tailWord_2297267 prefixEnd_2297267 1179602162712368665997567 := by
  unfold tailWord_2297267
  simp only [CollatzResearch.WordTrace]
  refine ⟨83788210968401475812770055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55858807312267650541846703 83788210968401475812770055)
  ·
    refine ⟨125682316452602213719155083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83788210968401475812770055 125682316452602213719155083)
    ·
      refine ⟨188523474678903320578732625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125682316452602213719155083 188523474678903320578732625)
      ·
        refine ⟨141392606009177490434049469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 188523474678903320578732625 141392606009177490434049469)
        ·
          refine ⟨53022227253441558912768551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 141392606009177490434049469 53022227253441558912768551)
          ·
            refine ⟨79533340880162338369152827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53022227253441558912768551 79533340880162338369152827)
            ·
              refine ⟨119300011320243507553729241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79533340880162338369152827 119300011320243507553729241)
              ·
                refine ⟨89475008490182630665296931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 119300011320243507553729241 89475008490182630665296931)
                ·
                  refine ⟨134212512735273945997945397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 89475008490182630665296931 134212512735273945997945397)
                  ·
                    refine ⟨12582423068931932437307381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 134212512735273945997945397 12582423068931932437307381)
                    ·
                      refine ⟨1179602162712368665997567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12582423068931932437307381 1179602162712368665997567)
                      ·
                        rfl

theorem cell23_2297267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 5, 5].length) (baseStart_2297267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2297267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2297267 prefixEnd_2297267 := by exact prefixLift 2297267
  have htrace : WordTrace (prefixWord ++ tailWord_2297267) baseStart_2297267 baseEnd_2297267 := by
    simpa [prefixWord, tailWord_2297267, baseEnd_2297267] using wordTrace_append hprefix tailTrace_2297267
  have hstable : (prefixWord ++ tailWord_2297267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2297267).length < 2 ^ (prefixWord ++ tailWord_2297267).sum := by decide
  have hdescent : baseEnd_2297267 < baseStart_2297267 := by decide
  rcases family_descends (prefixWord ++ tailWord_2297267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2297301 : List Nat := [1, 3, 2, 3, 1, 1, 1, 4, 2, 2, 3]
def baseStart_2297301 : Nat := 118140960795 + 2297301 * 2 ^ 59
def prefixEnd_2297301 : Nat := 4983230072969 + 3 ^ 40 * 2297301 * 2
def baseEnd_2297301 : Nat := 1179619621054621532972411

theorem tailTrace_2297301 : CollatzResearch.WordTrace tailWord_2297301 prefixEnd_2297301 1179619621054621532972411 := by
  unfold tailWord_2297301
  simp only [CollatzResearch.WordTrace]
  refine ⟨83789451050278299619507757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55859634033518866413005171 83789451050278299619507757)
  ·
    refine ⟨31421044143854362357315409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83789451050278299619507757 31421044143854362357315409)
    ·
      refine ⟨23565783107890771767986557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31421044143854362357315409 23565783107890771767986557)
      ·
        refine ⟨8837168665459039412994959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23565783107890771767986557 8837168665459039412994959)
        ·
          refine ⟨13255752998188559119492439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8837168665459039412994959 13255752998188559119492439)
          ·
            refine ⟨19883629497282838679238659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13255752998188559119492439 19883629497282838679238659)
            ·
              refine ⟨29825444245924258018857989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19883629497282838679238659 29825444245924258018857989)
              ·
                refine ⟨5592270796110798378535873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29825444245924258018857989 5592270796110798378535873)
                ·
                  refine ⟨4194203097083098783901905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5592270796110798378535873 4194203097083098783901905)
                  ·
                    refine ⟨3145652322812324087926429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4194203097083098783901905 3145652322812324087926429)
                    ·
                      refine ⟨1179619621054621532972411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3145652322812324087926429 1179619621054621532972411)
                      ·
                        rfl

theorem cell23_2297301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 4, 2, 2, 3].length) (baseStart_2297301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2297301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2297301 prefixEnd_2297301 := by exact prefixLift 2297301
  have htrace : WordTrace (prefixWord ++ tailWord_2297301) baseStart_2297301 baseEnd_2297301 := by
    simpa [prefixWord, tailWord_2297301, baseEnd_2297301] using wordTrace_append hprefix tailTrace_2297301
  have hstable : (prefixWord ++ tailWord_2297301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2297301).length < 2 ^ (prefixWord ++ tailWord_2297301).sum := by decide
  have hdescent : baseEnd_2297301 < baseStart_2297301 := by decide
  rcases family_descends (prefixWord ++ tailWord_2297301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2297304 : List Nat := [2, 1, 2, 2, 2, 1, 3, 4, 6]
def baseStart_2297304 : Nat := 118140960795 + 2297304 * 2 ^ 59
def prefixEnd_2297304 : Nat := 4983230072969 + 3 ^ 40 * 2297304 * 2
def baseEnd_2297304 : Nat := 131069017944065002359433

theorem tailTrace_2297304 : CollatzResearch.WordTrace tailWord_2297304 prefixEnd_2297304 131069017944065002359433 := by
  unfold tailWord_2297304
  simp only [CollatzResearch.WordTrace]
  refine ⟨41894780234633715565933483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55859706979511620754577977 41894780234633715565933483)
  ·
    refine ⟨62842170351950573348900225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41894780234633715565933483 62842170351950573348900225)
    ·
      refine ⟨47131627763962930011675169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62842170351950573348900225 47131627763962930011675169)
      ·
        refine ⟨35348720822972197508756377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47131627763962930011675169 35348720822972197508756377)
        ·
          refine ⟨26511540617229148131567283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35348720822972197508756377 26511540617229148131567283)
          ·
            refine ⟨39767310925843722197350925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26511540617229148131567283 39767310925843722197350925)
            ·
              refine ⟨14912741597191395824006597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39767310925843722197350925 14912741597191395824006597)
              ·
                refine ⟨2796139049473386717001237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14912741597191395824006597 2796139049473386717001237)
                ·
                  refine ⟨131069017944065002359433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2796139049473386717001237 131069017944065002359433)
                  ·
                    rfl

theorem cell23_2297304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 4, 6].length) (baseStart_2297304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2297304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2297304 prefixEnd_2297304 := by exact prefixLift 2297304
  have htrace : WordTrace (prefixWord ++ tailWord_2297304) baseStart_2297304 baseEnd_2297304 := by
    simpa [prefixWord, tailWord_2297304, baseEnd_2297304] using wordTrace_append hprefix tailTrace_2297304
  have hstable : (prefixWord ++ tailWord_2297304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2297304).length < 2 ^ (prefixWord ++ tailWord_2297304).sum := by decide
  have hdescent : baseEnd_2297304 < baseStart_2297304 := by decide
  rcases family_descends (prefixWord ++ tailWord_2297304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2297307 : List Nat := [1, 1, 1, 1, 1, 1, 1, 2, 5, 1, 8]
def baseStart_2297307 : Nat := 118140960795 + 2297307 * 2 ^ 59
def prefixEnd_2297307 : Nat := 4983230072969 + 3 ^ 40 * 2297307 * 2
def baseEnd_2297307 : Nat := 1179622701938548509497383

theorem tailTrace_2297307 : CollatzResearch.WordTrace tailWord_2297307 prefixEnd_2297307 1179622701938548509497383 := by
  unfold tailWord_2297307
  simp only [CollatzResearch.WordTrace]
  refine ⟨83789669888256562644226175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55859779925504375096150783 83789669888256562644226175)
  ·
    refine ⟨125684504832384843966339263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83789669888256562644226175 125684504832384843966339263)
    ·
      refine ⟨188526757248577265949508895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125684504832384843966339263 188526757248577265949508895)
      ·
        refine ⟨282790135872865898924263343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188526757248577265949508895 282790135872865898924263343)
        ·
          refine ⟨424185203809298848386395015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 282790135872865898924263343 424185203809298848386395015)
          ·
            refine ⟨636277805713948272579592523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 424185203809298848386395015 636277805713948272579592523)
            ·
              refine ⟨954416708570922408869388785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 636277805713948272579592523 954416708570922408869388785)
              ·
                refine ⟨715812531428191806652041589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 954416708570922408869388785 715812531428191806652041589)
                ·
                  refine ⟨67107424821392981873628899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 715812531428191806652041589 67107424821392981873628899)
                  ·
                    refine ⟨100661137232089472810443349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 67107424821392981873628899 100661137232089472810443349)
                    ·
                      refine ⟨1179622701938548509497383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 100661137232089472810443349 1179622701938548509497383)
                      ·
                        rfl

theorem cell23_2297307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 1, 8].length) (baseStart_2297307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2297307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2297307 prefixEnd_2297307 := by exact prefixLift 2297307
  have htrace : WordTrace (prefixWord ++ tailWord_2297307) baseStart_2297307 baseEnd_2297307 := by
    simpa [prefixWord, tailWord_2297307, baseEnd_2297307] using wordTrace_append hprefix tailTrace_2297307
  have hstable : (prefixWord ++ tailWord_2297307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2297307).length < 2 ^ (prefixWord ++ tailWord_2297307).sum := by decide
  have hdescent : baseEnd_2297307 < baseStart_2297307 := by decide
  rcases family_descends (prefixWord ++ tailWord_2297307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2297365 : List Nat := [1, 3, 2, 1, 3, 2, 2, 4, 1, 1, 3]
def baseStart_2297365 : Nat := 118140960795 + 2297365 * 2 ^ 59
def prefixEnd_2297365 : Nat := 4983230072969 + 3 ^ 40 * 2297365 * 2
def baseEnd_2297365 : Nat := 1179652483816509282572117

theorem tailTrace_2297365 : CollatzResearch.WordTrace tailWord_2297365 prefixEnd_2297365 1179652483816509282572117 := by
  unfold tailWord_2297365
  simp only [CollatzResearch.WordTrace]
  refine ⟨83791785322046438549837549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55861190214697625699891699 83791785322046438549837549)
  ·
    refine ⟨31421919495767414456189081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83791785322046438549837549 31421919495767414456189081)
    ·
      refine ⟨23566439621825560842141811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31421919495767414456189081 23566439621825560842141811)
      ·
        refine ⟨35349659432738341263212717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23566439621825560842141811 35349659432738341263212717)
        ·
          refine ⟨13256122287276877973704769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35349659432738341263212717 13256122287276877973704769)
          ·
            refine ⟨9942091715457658480278577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13256122287276877973704769 9942091715457658480278577)
            ·
              refine ⟨7456568786593243860208933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9942091715457658480278577 7456568786593243860208933)
              ·
                refine ⟨1398106647486233223789175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7456568786593243860208933 1398106647486233223789175)
                ·
                  refine ⟨2097159971229349835683763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1398106647486233223789175 2097159971229349835683763)
                  ·
                    refine ⟨3145739956844024753525645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2097159971229349835683763 3145739956844024753525645)
                    ·
                      refine ⟨1179652483816509282572117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3145739956844024753525645 1179652483816509282572117)
                      ·
                        rfl

theorem cell23_2297365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 4, 1, 1, 3].length) (baseStart_2297365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2297365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2297365 prefixEnd_2297365 := by exact prefixLift 2297365
  have htrace : WordTrace (prefixWord ++ tailWord_2297365) baseStart_2297365 baseEnd_2297365 := by
    simpa [prefixWord, tailWord_2297365, baseEnd_2297365] using wordTrace_append hprefix tailTrace_2297365
  have hstable : (prefixWord ++ tailWord_2297365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2297365).length < 2 ^ (prefixWord ++ tailWord_2297365).sum := by decide
  have hdescent : baseEnd_2297365 < baseStart_2297365 := by decide
  rcases family_descends (prefixWord ++ tailWord_2297365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2297424 : List Nat := [2, 1, 1, 1, 1, 3, 4, 1, 2, 7]
def baseStart_2297424 : Nat := 118140960795 + 2297424 * 2 ^ 59
def prefixEnd_2297424 : Nat := 4983230072969 + 3 ^ 40 * 2297424 * 2
def baseEnd_2297424 : Nat := 393227593058374850578115

theorem tailTrace_2297424 : CollatzResearch.WordTrace tailWord_2297424 prefixEnd_2297424 393227593058374850578115 := by
  unfold tailWord_2297424
  simp only [CollatzResearch.WordTrace]
  refine ⟨41896968614416345813117663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55862624819221794417490217 41896968614416345813117663)
  ·
    refine ⟨62845452921624518719676495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41896968614416345813117663 62845452921624518719676495)
    ·
      refine ⟨94268179382436778079514743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62845452921624518719676495 94268179382436778079514743)
      ·
        refine ⟨141402269073655167119272115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94268179382436778079514743 141402269073655167119272115)
        ·
          refine ⟨212103403610482750678908173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141402269073655167119272115 212103403610482750678908173)
          ·
            refine ⟨79538776353931031504590565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 212103403610482750678908173 79538776353931031504590565)
            ·
              refine ⟨14913520566362068407110731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 79538776353931031504590565 14913520566362068407110731)
              ·
                refine ⟨22370280849543102610666097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14913520566362068407110731 22370280849543102610666097)
                ·
                  refine ⟨16777710637157326957999573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22370280849543102610666097 16777710637157326957999573)
                  ·
                    refine ⟨393227593058374850578115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16777710637157326957999573 393227593058374850578115)
                    ·
                      rfl

theorem cell23_2297424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 1, 2, 7].length) (baseStart_2297424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2297424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2297424 prefixEnd_2297424 := by exact prefixLift 2297424
  have htrace : WordTrace (prefixWord ++ tailWord_2297424) baseStart_2297424 baseEnd_2297424 := by
    simpa [prefixWord, tailWord_2297424, baseEnd_2297424] using wordTrace_append hprefix tailTrace_2297424
  have hstable : (prefixWord ++ tailWord_2297424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2297424).length < 2 ^ (prefixWord ++ tailWord_2297424).sum := by decide
  have hdescent : baseEnd_2297424 < baseStart_2297424 := by decide
  rcases family_descends (prefixWord ++ tailWord_2297424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2297481 : List Nat := [1, 2, 1, 1, 4, 1, 3, 1, 2, 4, 3]
def baseStart_2297481 : Nat := 118140960795 + 2297481 * 2 ^ 59
def prefixEnd_2297481 : Nat := 4983230072969 + 3 ^ 40 * 2297481 * 2
def baseEnd_2297481 : Nat := 1179712047572430828721583

theorem tailTrace_2297481 : CollatzResearch.WordTrace tailWord_2297481 prefixEnd_2297481 1179712047572430828721583 := by
  unfold tailWord_2297481
  simp only [CollatzResearch.WordTrace]
  refine ⟨83796016189626190361060297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55864010793084126907373531 83796016189626190361060297)
  ·
    refine ⟨62847012142219642770795223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83796016189626190361060297 62847012142219642770795223)
    ·
      refine ⟨94270518213329464156192835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62847012142219642770795223 94270518213329464156192835)
      ·
        refine ⟨141405777319994196234289253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94270518213329464156192835 141405777319994196234289253)
        ·
          refine ⟨26513583247498911793929235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 141405777319994196234289253 26513583247498911793929235)
          ·
            refine ⟨39770374871248367690893853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26513583247498911793929235 39770374871248367690893853)
            ·
              refine ⟨14913890576718137884085195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39770374871248367690893853 14913890576718137884085195)
              ·
                refine ⟨22370835865077206826127793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14913890576718137884085195 22370835865077206826127793)
                ·
                  refine ⟨16778126898807905119595845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22370835865077206826127793 16778126898807905119595845)
                  ·
                    refine ⟨3145898793526482209924221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16778126898807905119595845 3145898793526482209924221)
                    ·
                      refine ⟨1179712047572430828721583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3145898793526482209924221 1179712047572430828721583)
                      ·
                        rfl

theorem cell23_2297481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 1, 2, 4, 3].length) (baseStart_2297481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2297481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2297481 prefixEnd_2297481 := by exact prefixLift 2297481
  have htrace : WordTrace (prefixWord ++ tailWord_2297481) baseStart_2297481 baseEnd_2297481 := by
    simpa [prefixWord, tailWord_2297481, baseEnd_2297481] using wordTrace_append hprefix tailTrace_2297481
  have hstable : (prefixWord ++ tailWord_2297481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2297481).length < 2 ^ (prefixWord ++ tailWord_2297481).sum := by decide
  have hdescent : baseEnd_2297481 < baseStart_2297481 := by decide
  rcases family_descends (prefixWord ++ tailWord_2297481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2297495 : List Nat := [1, 1, 3, 3, 2, 3, 2, 1, 1, 4, 2]
def baseStart_2297495 : Nat := 118140960795 + 2297495 * 2 ^ 59
def prefixEnd_2297495 : Nat := 4983230072969 + 3 ^ 40 * 2297495 * 2
def baseEnd_2297495 : Nat := 1179719236301593773946519

theorem tailTrace_2297495 : CollatzResearch.WordTrace tailWord_2297495 prefixEnd_2297495 1179719236301593773946519 := by
  unfold tailWord_2297495
  simp only [CollatzResearch.WordTrace]
  refine ⟨83796526811575470752069939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55864351207716980501379959 83796526811575470752069939)
  ·
    refine ⟨125694790217363206128104909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83796526811575470752069939 125694790217363206128104909)
    ·
      refine ⟨47135546331511202298039341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 125694790217363206128104909 47135546331511202298039341)
      ·
        refine ⟨17675829874316700861764753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47135546331511202298039341 17675829874316700861764753)
        ·
          refine ⟨13256872405737525646323565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17675829874316700861764753 13256872405737525646323565)
          ·
            refine ⟨4971327152151572117371337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13256872405737525646323565 4971327152151572117371337)
            ·
              refine ⟨3728495364113679088028503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4971327152151572117371337 3728495364113679088028503)
              ·
                refine ⟨5592743046170518632042755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3728495364113679088028503 5592743046170518632042755)
                ·
                  refine ⟨8389114569255777948064133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5592743046170518632042755 8389114569255777948064133)
                  ·
                    refine ⟨1572958981735458365262025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8389114569255777948064133 1572958981735458365262025)
                    ·
                      refine ⟨1179719236301593773946519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1572958981735458365262025 1179719236301593773946519)
                      ·
                        rfl

theorem cell23_2297495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 2, 1, 1, 4, 2].length) (baseStart_2297495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2297495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2297495 prefixEnd_2297495 := by exact prefixLift 2297495
  have htrace : WordTrace (prefixWord ++ tailWord_2297495) baseStart_2297495 baseEnd_2297495 := by
    simpa [prefixWord, tailWord_2297495, baseEnd_2297495] using wordTrace_append hprefix tailTrace_2297495
  have hstable : (prefixWord ++ tailWord_2297495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2297495).length < 2 ^ (prefixWord ++ tailWord_2297495).sum := by decide
  have hdescent : baseEnd_2297495 < baseStart_2297495 := by decide
  rcases family_descends (prefixWord ++ tailWord_2297495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2297531 : List Nat := [1, 1, 1, 1, 1, 2, 3, 6, 2, 5]
def baseStart_2297531 : Nat := 118140960795 + 2297531 * 2 ^ 59
def prefixEnd_2297531 : Nat := 4983230072969 + 3 ^ 40 * 2297531 * 2
def baseEnd_2297531 : Nat := 393245907201718544365451

theorem tailTrace_2297531 : CollatzResearch.WordTrace tailWord_2297531 prefixEnd_2297531 393245907201718544365451 := by
  unfold tailWord_2297531
  simp only [CollatzResearch.WordTrace]
  refine ⟨83797839839445048900380447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55865226559630032600253631 83797839839445048900380447)
  ·
    refine ⟨125696759759167573350570671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83797839839445048900380447 125696759759167573350570671)
    ·
      refine ⟨188545139638751360025856007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125696759759167573350570671 188545139638751360025856007)
      ·
        refine ⟨282817709458127040038784011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188545139638751360025856007 282817709458127040038784011)
        ·
          refine ⟨424226564187190560058176017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 282817709458127040038784011 424226564187190560058176017)
          ·
            refine ⟨318169923140392920043632013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 424226564187190560058176017 318169923140392920043632013)
            ·
              refine ⟨119313721177647345016362005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 318169923140392920043632013 119313721177647345016362005)
              ·
                refine ⟨5592830680202219297641969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 119313721177647345016362005 5592830680202219297641969)
                ·
                  refine ⟨4194623010151664473231477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5592830680202219297641969 4194623010151664473231477)
                  ·
                    refine ⟨393245907201718544365451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4194623010151664473231477 393245907201718544365451)
                    ·
                      rfl

theorem cell23_2297531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 6, 2, 5].length) (baseStart_2297531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2297531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2297531 prefixEnd_2297531 := by exact prefixLift 2297531
  have htrace : WordTrace (prefixWord ++ tailWord_2297531) baseStart_2297531 baseEnd_2297531 := by
    simpa [prefixWord, tailWord_2297531, baseEnd_2297531] using wordTrace_append hprefix tailTrace_2297531
  have hstable : (prefixWord ++ tailWord_2297531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2297531).length < 2 ^ (prefixWord ++ tailWord_2297531).sum := by decide
  have hdescent : baseEnd_2297531 < baseStart_2297531 := by decide
  rcases family_descends (prefixWord ++ tailWord_2297531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2297542 : List Nat := [6, 1, 2, 1, 1, 1, 2, 1, 2, 2, 4]
def baseStart_2297542 : Nat := 118140960795 + 2297542 * 2 ^ 59
def prefixEnd_2297542 : Nat := 4983230072969 + 3 ^ 40 * 2297542 * 2
def baseEnd_2297542 : Nat := 1179743369892355090058803

theorem tailTrace_2297542 : CollatzResearch.WordTrace tailWord_2297542 prefixEnd_2297542 1179743369892355090058803 := by
  unfold tailWord_2297542
  simp only [CollatzResearch.WordTrace]
  refine ⟨2618695032575162430594715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 55865494028270131852687253 2618695032575162430594715)
  ·
    refine ⟨3928042548862743645892073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2618695032575162430594715 3928042548862743645892073)
    ·
      refine ⟨2946031911647057734419055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3928042548862743645892073 2946031911647057734419055)
      ·
        refine ⟨4419047867470586601628583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2946031911647057734419055 4419047867470586601628583)
        ·
          refine ⟨6628571801205879902442875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4419047867470586601628583 6628571801205879902442875)
          ·
            refine ⟨9942857701808819853664313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6628571801205879902442875 9942857701808819853664313)
            ·
              refine ⟨7457143276356614890248235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9942857701808819853664313 7457143276356614890248235)
              ·
                refine ⟨11185714914534922335372353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7457143276356614890248235 11185714914534922335372353)
                ·
                  refine ⟨8389286185901191751529265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11185714914534922335372353 8389286185901191751529265)
                  ·
                    refine ⟨6291964639425893813646949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8389286185901191751529265 6291964639425893813646949)
                    ·
                      refine ⟨1179743369892355090058803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6291964639425893813646949 1179743369892355090058803)
                      ·
                        rfl

theorem cell23_2297542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_2297542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2297542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2297542 prefixEnd_2297542 := by exact prefixLift 2297542
  have htrace : WordTrace (prefixWord ++ tailWord_2297542) baseStart_2297542 baseEnd_2297542 := by
    simpa [prefixWord, tailWord_2297542, baseEnd_2297542] using wordTrace_append hprefix tailTrace_2297542
  have hstable : (prefixWord ++ tailWord_2297542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2297542).length < 2 ^ (prefixWord ++ tailWord_2297542).sum := by decide
  have hdescent : baseEnd_2297542 < baseStart_2297542 := by decide
  rcases family_descends (prefixWord ++ tailWord_2297542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2297568 : List Nat := [2, 1, 1, 3, 1, 2, 2, 2, 1, 6, 2]
def baseStart_2297568 : Nat := 118140960795 + 2297568 * 2 ^ 59
def prefixEnd_2297568 : Nat := 4983230072969 + 3 ^ 40 * 2297568 * 2
def baseEnd_2297568 : Nat := 1179756720389371988333683

theorem tailTrace_2297568 : CollatzResearch.WordTrace tailWord_2297568 prefixEnd_2297568 1179756720389371988333683 := by
  unfold tailWord_2297568
  simp only [CollatzResearch.WordTrace]
  refine ⟨41899594670155502109738679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55866126226874002812984905 41899594670155502109738679)
  ·
    refine ⟨62849392005233253164608019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41899594670155502109738679 62849392005233253164608019)
    ·
      refine ⟨94274088007849879746912029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62849392005233253164608019 94274088007849879746912029)
      ·
        refine ⟨35352783002943704905092011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94274088007849879746912029 35352783002943704905092011)
        ·
          refine ⟨53029174504415557357638017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35352783002943704905092011 53029174504415557357638017)
          ·
            refine ⟨39771880878311668018228513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53029174504415557357638017 39771880878311668018228513)
            ·
              refine ⟨29828910658733751013671385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39771880878311668018228513 29828910658733751013671385)
              ·
                refine ⟨22371682994050313260253539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29828910658733751013671385 22371682994050313260253539)
                ·
                  refine ⟨33557524491075469890380309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22371682994050313260253539 33557524491075469890380309)
                  ·
                    refine ⟨1573008960519162651111577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 33557524491075469890380309 1573008960519162651111577)
                    ·
                      refine ⟨1179756720389371988333683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1573008960519162651111577 1179756720389371988333683)
                      ·
                        rfl

theorem cell23_2297568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 2, 1, 6, 2].length) (baseStart_2297568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2297568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2297568 prefixEnd_2297568 := by exact prefixLift 2297568
  have htrace : WordTrace (prefixWord ++ tailWord_2297568) baseStart_2297568 baseEnd_2297568 := by
    simpa [prefixWord, tailWord_2297568, baseEnd_2297568] using wordTrace_append hprefix tailTrace_2297568
  have hstable : (prefixWord ++ tailWord_2297568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2297568).length < 2 ^ (prefixWord ++ tailWord_2297568).sum := by decide
  have hdescent : baseEnd_2297568 < baseStart_2297568 := by decide
  rcases family_descends (prefixWord ++ tailWord_2297568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2297578 : List Nat := [3, 1, 3, 1, 1, 1, 2, 2, 5, 4]
def baseStart_2297578 : Nat := 118140960795 + 2297578 * 2 ^ 59
def prefixEnd_2297578 : Nat := 4983230072969 + 3 ^ 40 * 2297578 * 2
def baseEnd_2297578 : Nat := 393253951731972316402879

theorem tailTrace_2297578 : CollatzResearch.WordTrace tailWord_2297578 prefixEnd_2297578 393253951731972316402879 := by
  unfold tailWord_2297578
  simp only [CollatzResearch.WordTrace]
  refine ⟨20949888517568693981835347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55866369380183183951560925 20949888517568693981835347)
  ·
    refine ⟨31424832776353040972753021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20949888517568693981835347 31424832776353040972753021)
    ·
      refine ⟨11784312291132390364782383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31424832776353040972753021 11784312291132390364782383)
      ·
        refine ⟨17676468436698585547173575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11784312291132390364782383 17676468436698585547173575)
        ·
          refine ⟨26514702655047878320760363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17676468436698585547173575 26514702655047878320760363)
          ·
            refine ⟨39772053982571817481140545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26514702655047878320760363 39772053982571817481140545)
            ·
              refine ⟨29829040486928863110855409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39772053982571817481140545 29829040486928863110855409)
              ·
                refine ⟨22371780365196647333141557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29829040486928863110855409 22371780365196647333141557)
                ·
                  refine ⟨2097354409237185687482021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22371780365196647333141557 2097354409237185687482021)
                  ·
                    refine ⟨393253951731972316402879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2097354409237185687482021 393253951731972316402879)
                    ·
                      rfl

theorem cell23_2297578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 2, 5, 4].length) (baseStart_2297578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2297578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2297578 prefixEnd_2297578 := by exact prefixLift 2297578
  have htrace : WordTrace (prefixWord ++ tailWord_2297578) baseStart_2297578 baseEnd_2297578 := by
    simpa [prefixWord, tailWord_2297578, baseEnd_2297578] using wordTrace_append hprefix tailTrace_2297578
  have hstable : (prefixWord ++ tailWord_2297578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2297578).length < 2 ^ (prefixWord ++ tailWord_2297578).sum := by decide
  have hdescent : baseEnd_2297578 < baseStart_2297578 := by decide
  rcases family_descends (prefixWord ++ tailWord_2297578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2297591 : List Nat := [1, 1, 3, 1, 1, 1, 6, 1, 8]
def baseStart_2297591 : Nat := 118140960795 + 2297591 * 2 ^ 59
def prefixEnd_2297591 : Nat := 4983230072969 + 3 ^ 40 * 2297591 * 2
def baseEnd_2297591 : Nat := 131085392271602822038453

theorem tailTrace_2297591 : CollatzResearch.WordTrace tailWord_2297591 prefixEnd_2297591 131085392271602822038453 := by
  unfold tailWord_2297591
  simp only [CollatzResearch.WordTrace]
  refine ⟨83800028219227679147564627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55866685479485119431709751 83800028219227679147564627)
  ·
    refine ⟨125700042328841518721346941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83800028219227679147564627 125700042328841518721346941)
    ·
      refine ⟨47137515873315569520505103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 125700042328841518721346941 47137515873315569520505103)
      ·
        refine ⟨70706273809973354280757655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47137515873315569520505103 70706273809973354280757655)
        ·
          refine ⟨106059410714960031421136483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70706273809973354280757655 106059410714960031421136483)
          ·
            refine ⟨159089116072440047131704725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106059410714960031421136483 159089116072440047131704725)
            ·
              refine ⟨7457302315895627209298659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 159089116072440047131704725 7457302315895627209298659)
              ·
                refine ⟨11185953473843440813947989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7457302315895627209298659 11185953473843440813947989)
                ·
                  refine ⟨131085392271602822038453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11185953473843440813947989 131085392271602822038453)
                  ·
                    rfl

theorem cell23_2297591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 1, 8].length) (baseStart_2297591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2297591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2297591 prefixEnd_2297591 := by exact prefixLift 2297591
  have htrace : WordTrace (prefixWord ++ tailWord_2297591) baseStart_2297591 baseEnd_2297591 := by
    simpa [prefixWord, tailWord_2297591, baseEnd_2297591] using wordTrace_append hprefix tailTrace_2297591
  have hstable : (prefixWord ++ tailWord_2297591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2297591).length < 2 ^ (prefixWord ++ tailWord_2297591).sum := by decide
  have hdescent : baseEnd_2297591 < baseStart_2297591 := by decide
  rcases family_descends (prefixWord ++ tailWord_2297591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2297608 : List Nat := [2, 1, 3, 2, 2, 1, 3, 3, 6]
def baseStart_2297608 : Nat := 118140960795 + 2297608 * 2 ^ 59
def prefixEnd_2297608 : Nat := 4983230072969 + 3 ^ 40 * 2297608 * 2
def baseEnd_2297608 : Nat := 131086362179505759092611

theorem tailTrace_2297608 : CollatzResearch.WordTrace tailWord_2297608 prefixEnd_2297608 131086362179505759092611 := by
  unfold tailWord_2297608
  simp only [CollatzResearch.WordTrace]
  refine ⟨41900324130083045525466739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55867098840110727367288985 41900324130083045525466739)
  ·
    refine ⟨62850486195124568288200109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41900324130083045525466739 62850486195124568288200109)
    ·
      refine ⟨23568932323171713108075041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62850486195124568288200109 23568932323171713108075041)
      ·
        refine ⟨17676699242378784831056281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23568932323171713108075041 17676699242378784831056281)
        ·
          refine ⟨13257524431784088623292211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17676699242378784831056281 13257524431784088623292211)
          ·
            refine ⟨19886286647676132934938317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13257524431784088623292211 19886286647676132934938317)
            ·
              refine ⟨7457357492878549850601869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19886286647676132934938317 7457357492878549850601869)
              ·
                refine ⟨2796509059829456193975701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7457357492878549850601869 2796509059829456193975701)
                ·
                  refine ⟨131086362179505759092611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2796509059829456193975701 131086362179505759092611)
                  ·
                    rfl

theorem cell23_2297608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 3, 6].length) (baseStart_2297608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2297608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2297608 prefixEnd_2297608 := by exact prefixLift 2297608
  have htrace : WordTrace (prefixWord ++ tailWord_2297608) baseStart_2297608 baseEnd_2297608 := by
    simpa [prefixWord, tailWord_2297608, baseEnd_2297608] using wordTrace_append hprefix tailTrace_2297608
  have hstable : (prefixWord ++ tailWord_2297608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2297608).length < 2 ^ (prefixWord ++ tailWord_2297608).sum := by decide
  have hdescent : baseEnd_2297608 < baseStart_2297608 := by decide
  rcases family_descends (prefixWord ++ tailWord_2297608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2297611 : List Nat := [1, 1, 1, 1, 5, 1, 2, 2, 1, 2, 6]
def baseStart_2297611 : Nat := 118140960795 + 2297611 * 2 ^ 59
def prefixEnd_2297611 : Nat := 4983230072969 + 3 ^ 40 * 2297611 * 2
def baseEnd_2297611 : Nat := 1179778800057515320095985

theorem tailTrace_2297611 : CollatzResearch.WordTrace tailWord_2297611 prefixEnd_2297611 1179778800057515320095985 := by
  unfold tailWord_2297611
  simp only [CollatzResearch.WordTrace]
  refine ⟨83800757679155222563292687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55867171786103481708861791 83800757679155222563292687)
  ·
    refine ⟨125701136518732833844939031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83800757679155222563292687 125701136518732833844939031)
    ·
      refine ⟨188551704778099250767408547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125701136518732833844939031 188551704778099250767408547)
      ·
        refine ⟨282827557167148876151112821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188551704778099250767408547 282827557167148876151112821)
        ·
          refine ⟨26515083484420207139166827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 282827557167148876151112821 26515083484420207139166827)
          ·
            refine ⟨39772625226630310708750241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26515083484420207139166827 39772625226630310708750241)
            ·
              refine ⟨29829468919972733031562681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39772625226630310708750241 29829468919972733031562681)
              ·
                refine ⟨22372101689979549773672011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29829468919972733031562681 22372101689979549773672011)
                ·
                  refine ⟨33558152534969324660508017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22372101689979549773672011 33558152534969324660508017)
                  ·
                    refine ⟨25168614401226993495381013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33558152534969324660508017 25168614401226993495381013)
                    ·
                      refine ⟨1179778800057515320095985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25168614401226993495381013 1179778800057515320095985)
                      ·
                        rfl

theorem cell23_2297611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 2, 1, 2, 6].length) (baseStart_2297611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2297611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2297611 prefixEnd_2297611 := by exact prefixLift 2297611
  have htrace : WordTrace (prefixWord ++ tailWord_2297611) baseStart_2297611 baseEnd_2297611 := by
    simpa [prefixWord, tailWord_2297611, baseEnd_2297611] using wordTrace_append hprefix tailTrace_2297611
  have hstable : (prefixWord ++ tailWord_2297611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2297611).length < 2 ^ (prefixWord ++ tailWord_2297611).sum := by decide
  have hdescent : baseEnd_2297611 < baseStart_2297611 := by decide
  rcases family_descends (prefixWord ++ tailWord_2297611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2297726 : List Nat := [4, 2, 3, 1, 1, 1, 2, 2, 3, 2, 2]
def baseStart_2297726 : Nat := 118140960795 + 2297726 * 2 ^ 59
def prefixEnd_2297726 : Nat := 4983230072969 + 3 ^ 40 * 2297726 * 2
def baseEnd_2297726 : Nat := 1179837850332782370157957

theorem tailTrace_2297726 : CollatzResearch.WordTrace tailWord_2297726 prefixEnd_2297726 1179837850332782370157957 := by
  unfold tailWord_2297726
  simp only [CollatzResearch.WordTrace]
  refine ⟨10475619009217324650466129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55869968049159064802486021 10475619009217324650466129)
  ·
    refine ⟨7856714256912993487849597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10475619009217324650466129 7856714256912993487849597)
    ·
      refine ⟨2946267846342372557943599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7856714256912993487849597 2946267846342372557943599)
      ·
        refine ⟨4419401769513558836915399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2946267846342372557943599 4419401769513558836915399)
        ·
          refine ⟨6629102654270338255373099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4419401769513558836915399 6629102654270338255373099)
          ·
            refine ⟨9943653981405507383059649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6629102654270338255373099 9943653981405507383059649)
            ·
              refine ⟨7457740486054130537294737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9943653981405507383059649 7457740486054130537294737)
              ·
                refine ⟨5593305364540597902971053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7457740486054130537294737 5593305364540597902971053)
                ·
                  refine ⟨2097489511702724213614145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5593305364540597902971053 2097489511702724213614145)
                  ·
                    refine ⟨1573117133777043160210609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2097489511702724213614145 1573117133777043160210609)
                    ·
                      refine ⟨1179837850332782370157957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1573117133777043160210609 1179837850332782370157957)
                      ·
                        rfl

theorem cell23_2297726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 2, 3, 2, 2].length) (baseStart_2297726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2297726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2297726 prefixEnd_2297726 := by exact prefixLift 2297726
  have htrace : WordTrace (prefixWord ++ tailWord_2297726) baseStart_2297726 baseEnd_2297726 := by
    simpa [prefixWord, tailWord_2297726, baseEnd_2297726] using wordTrace_append hprefix tailTrace_2297726
  have hstable : (prefixWord ++ tailWord_2297726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2297726).length < 2 ^ (prefixWord ++ tailWord_2297726).sum := by decide
  have hdescent : baseEnd_2297726 < baseStart_2297726 := by decide
  rcases family_descends (prefixWord ++ tailWord_2297726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2297778 : List Nat := [3, 2, 1, 1, 1, 1, 1, 2, 2, 3, 6]
def baseStart_2297778 : Nat := 118140960795 + 2297778 * 2 ^ 59
def prefixEnd_2297778 : Nat := 4983230072969 + 3 ^ 40 * 2297778 * 2
def baseEnd_2297778 : Nat := 1179864551326816166707717

theorem tailTrace_2297778 : CollatzResearch.WordTrace tailWord_2297778 prefixEnd_2297778 1179864551326816166707717 := by
  unfold tailWord_2297778
  simp only [CollatzResearch.WordTrace]
  refine ⟨20951712167387552521155497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55871232446366806723081325 20951712167387552521155497)
  ·
    refine ⟨15713784125540664390866623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20951712167387552521155497 15713784125540664390866623)
    ·
      refine ⟨23570676188310996586299935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15713784125540664390866623 23570676188310996586299935)
      ·
        refine ⟨35356014282466494879449903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23570676188310996586299935 35356014282466494879449903)
        ·
          refine ⟨53034021423699742319174855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35356014282466494879449903 53034021423699742319174855)
          ·
            refine ⟨79551032135549613478762283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53034021423699742319174855 79551032135549613478762283)
            ·
              refine ⟨119326548203324420218143425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79551032135549613478762283 119326548203324420218143425)
              ·
                refine ⟨89494911152493315163607569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 119326548203324420218143425 89494911152493315163607569)
                ·
                  refine ⟨67121183364369986372705677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 89494911152493315163607569 67121183364369986372705677)
                  ·
                    refine ⟨25170443761638744889764629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 67121183364369986372705677 25170443761638744889764629)
                    ·
                      refine ⟨1179864551326816166707717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25170443761638744889764629 1179864551326816166707717)
                      ·
                        rfl

theorem cell23_2297778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 2, 3, 6].length) (baseStart_2297778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2297778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2297778 prefixEnd_2297778 := by exact prefixLift 2297778
  have htrace : WordTrace (prefixWord ++ tailWord_2297778) baseStart_2297778 baseEnd_2297778 := by
    simpa [prefixWord, tailWord_2297778, baseEnd_2297778] using wordTrace_append hprefix tailTrace_2297778
  have hstable : (prefixWord ++ tailWord_2297778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2297778).length < 2 ^ (prefixWord ++ tailWord_2297778).sum := by decide
  have hdescent : baseEnd_2297778 < baseStart_2297778 := by decide
  rcases family_descends (prefixWord ++ tailWord_2297778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2297815 : List Nat := [1, 1, 3, 2, 1, 1, 4, 2, 2, 3, 3]
def baseStart_2297815 : Nat := 118140960795 + 2297815 * 2 ^ 59
def prefixEnd_2297815 : Nat := 4983230072969 + 3 ^ 40 * 2297815 * 2
def baseEnd_2297815 : Nat := 1179883550111032521945047

theorem tailTrace_2297815 : CollatzResearch.WordTrace tailWord_2297815 prefixEnd_2297815 1179883550111032521945047 := by
  unfold tailWord_2297815
  simp only [CollatzResearch.WordTrace]
  refine ⟨83808198170416165403718899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55872132113610776935812599 83808198170416165403718899)
  ·
    refine ⟨125712297255624248105578349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83808198170416165403718899 125712297255624248105578349)
    ·
      refine ⟨47142111470859093039591881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 125712297255624248105578349 47142111470859093039591881)
      ·
        refine ⟨35356583603144319779693911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47142111470859093039591881 35356583603144319779693911)
        ·
          refine ⟨53034875404716479669540867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35356583603144319779693911 53034875404716479669540867)
          ·
            refine ⟨79552313107074719504311301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53034875404716479669540867 79552313107074719504311301)
            ·
              refine ⟨14916058707576509907058369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 79552313107074719504311301 14916058707576509907058369)
              ·
                refine ⟨11187044030682382430293777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14916058707576509907058369 11187044030682382430293777)
                ·
                  refine ⟨8390283023011786822720333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11187044030682382430293777 8390283023011786822720333)
                  ·
                    refine ⟨3146356133629420058520125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8390283023011786822720333 3146356133629420058520125)
                    ·
                      refine ⟨1179883550111032521945047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3146356133629420058520125 1179883550111032521945047)
                      ·
                        rfl

theorem cell23_2297815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 2, 2, 3, 3].length) (baseStart_2297815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2297815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2297815 prefixEnd_2297815 := by exact prefixLift 2297815
  have htrace : WordTrace (prefixWord ++ tailWord_2297815) baseStart_2297815 baseEnd_2297815 := by
    simpa [prefixWord, tailWord_2297815, baseEnd_2297815] using wordTrace_append hprefix tailTrace_2297815
  have hstable : (prefixWord ++ tailWord_2297815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2297815).length < 2 ^ (prefixWord ++ tailWord_2297815).sum := by decide
  have hdescent : baseEnd_2297815 < baseStart_2297815 := by decide
  rcases family_descends (prefixWord ++ tailWord_2297815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2297882 : List Nat := [3, 1, 1, 3, 1, 3, 1, 3, 3, 4]
def baseStart_2297882 : Nat := 118140960795 + 2297882 * 2 ^ 59
def prefixEnd_2297882 : Nat := 4983230072969 + 3 ^ 40 * 2297882 * 2
def baseEnd_2297882 : Nat := 393305984438294586602413

theorem tailTrace_2297882 : CollatzResearch.WordTrace tailWord_2297882 prefixEnd_2297882 393305984438294586602413 := by
  unfold tailWord_2297882
  simp only [CollatzResearch.WordTrace]
  refine ⟨20952660465293358961601975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55873761240782290564271933 20952660465293358961601975)
  ·
    refine ⟨31428990697940038442402963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20952660465293358961601975 31428990697940038442402963)
    ·
      refine ⟨47143486046910057663604445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31428990697940038442402963 47143486046910057663604445)
      ·
        refine ⟨17678807267591271623851667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47143486046910057663604445 17678807267591271623851667)
        ·
          refine ⟨26518210901386907435777501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17678807267591271623851667 26518210901386907435777501)
          ·
            refine ⟨9944329088020090288416563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26518210901386907435777501 9944329088020090288416563)
            ·
              refine ⟨14916493632030135432624845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9944329088020090288416563 14916493632030135432624845)
              ·
                refine ⟨5593685112011300787234317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14916493632030135432624845 5593685112011300787234317)
                ·
                  refine ⟨2097631917004237795212869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5593685112011300787234317 2097631917004237795212869)
                  ·
                    refine ⟨393305984438294586602413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2097631917004237795212869 393305984438294586602413)
                    ·
                      rfl

theorem cell23_2297882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 3, 3, 4].length) (baseStart_2297882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2297882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2297882 prefixEnd_2297882 := by exact prefixLift 2297882
  have htrace : WordTrace (prefixWord ++ tailWord_2297882) baseStart_2297882 baseEnd_2297882 := by
    simpa [prefixWord, tailWord_2297882, baseEnd_2297882] using wordTrace_append hprefix tailTrace_2297882
  have hstable : (prefixWord ++ tailWord_2297882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2297882).length < 2 ^ (prefixWord ++ tailWord_2297882).sum := by decide
  have hdescent : baseEnd_2297882 < baseStart_2297882 := by decide
  rcases family_descends (prefixWord ++ tailWord_2297882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2297925 : List Nat := [1, 3, 1, 1, 1, 3, 1, 2, 5, 5]
def baseStart_2297925 : Nat := 118140960795 + 2297925 * 2 ^ 59
def prefixEnd_2297925 : Nat := 4983230072969 + 3 ^ 40 * 2297925 * 2
def baseEnd_2297925 : Nat := 393313344327675697189847

theorem tailTrace_2297925 : CollatzResearch.WordTrace tailWord_2297925 prefixEnd_2297925 393313344327675697189847 := by
  unfold tailWord_2297925
  simp only [CollatzResearch.WordTrace]
  refine ⟨83812210200017654190223229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55874806800011769460148819 83812210200017654190223229)
  ·
    refine ⟨31429578825006620321333711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83812210200017654190223229 31429578825006620321333711)
    ·
      refine ⟨47144368237509930482000567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31429578825006620321333711 47144368237509930482000567)
      ·
        refine ⟨70716552356264895723000851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47144368237509930482000567 70716552356264895723000851)
        ·
          refine ⟨106074828534397343584501277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70716552356264895723000851 106074828534397343584501277)
          ·
            refine ⟨39778060700399003844187979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 106074828534397343584501277 39778060700399003844187979)
            ·
              refine ⟨59667091050598505766281969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39778060700399003844187979 59667091050598505766281969)
              ·
                refine ⟨44750318287948879324711477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59667091050598505766281969 44750318287948879324711477)
                ·
                  refine ⟨4195342339495207436691701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44750318287948879324711477 4195342339495207436691701)
                  ·
                    refine ⟨393313344327675697189847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4195342339495207436691701 393313344327675697189847)
                    ·
                      rfl

theorem cell23_2297925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 2, 5, 5].length) (baseStart_2297925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2297925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2297925 prefixEnd_2297925 := by exact prefixLift 2297925
  have htrace : WordTrace (prefixWord ++ tailWord_2297925) baseStart_2297925 baseEnd_2297925 := by
    simpa [prefixWord, tailWord_2297925, baseEnd_2297925] using wordTrace_append hprefix tailTrace_2297925
  have hstable : (prefixWord ++ tailWord_2297925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2297925).length < 2 ^ (prefixWord ++ tailWord_2297925).sum := by decide
  have hdescent : baseEnd_2297925 < baseStart_2297925 := by decide
  rcases family_descends (prefixWord ++ tailWord_2297925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2297926 : List Nat := [6, 1, 1, 1, 1, 1, 3, 2, 2, 2, 3]
def baseStart_2297926 : Nat := 118140960795 + 2297926 * 2 ^ 59
def prefixEnd_2297926 : Nat := 4983230072969 + 3 ^ 40 * 2297926 * 2
def baseEnd_2297926 : Nat := 1179940546463681587657037

theorem tailTrace_2297926 : CollatzResearch.WordTrace tailWord_2297926 prefixEnd_2297926 1179940546463681587657037 := by
  unfold tailWord_2297926
  simp only [CollatzResearch.WordTrace]
  refine ⟨2619132708531688480031551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 55874831115342687574006421 2619132708531688480031551)
  ·
    refine ⟨3928699062797532720047327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2619132708531688480031551 3928699062797532720047327)
    ·
      refine ⟨5893048594196299080070991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3928699062797532720047327 5893048594196299080070991)
      ·
        refine ⟨8839572891294448620106487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5893048594196299080070991 8839572891294448620106487)
        ·
          refine ⟨13259359336941672930159731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8839572891294448620106487 13259359336941672930159731)
          ·
            refine ⟨19889039005412509395239597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13259359336941672930159731 19889039005412509395239597)
            ·
              refine ⟨7458389627029691023214849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19889039005412509395239597 7458389627029691023214849)
              ·
                refine ⟨5593792220272268267411137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7458389627029691023214849 5593792220272268267411137)
                ·
                  refine ⟨4195344165204201200558353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5593792220272268267411137 4195344165204201200558353)
                  ·
                    refine ⟨3146508123903150900418765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4195344165204201200558353 3146508123903150900418765)
                    ·
                      refine ⟨1179940546463681587657037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3146508123903150900418765 1179940546463681587657037)
                      ·
                        rfl

theorem cell23_2297926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 2, 2, 2, 3].length) (baseStart_2297926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2297926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2297926 prefixEnd_2297926 := by exact prefixLift 2297926
  have htrace : WordTrace (prefixWord ++ tailWord_2297926) baseStart_2297926 baseEnd_2297926 := by
    simpa [prefixWord, tailWord_2297926, baseEnd_2297926] using wordTrace_append hprefix tailTrace_2297926
  have hstable : (prefixWord ++ tailWord_2297926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2297926).length < 2 ^ (prefixWord ++ tailWord_2297926).sum := by decide
  have hdescent : baseEnd_2297926 < baseStart_2297926 := by decide
  rcases family_descends (prefixWord ++ tailWord_2297926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2297933 : List Nat := [1, 6, 1, 1, 1, 1, 5, 2, 1, 4]
def baseStart_2297933 : Nat := 118140960795 + 2297933 * 2 ^ 59
def prefixEnd_2297933 : Nat := 4983230072969 + 3 ^ 40 * 2297933 * 2
def baseEnd_2297933 : Nat := 393314713609421020089835

theorem tailTrace_2297933 : CollatzResearch.WordTrace tailWord_2297933 prefixEnd_2297933 393314713609421020089835 := by
  unfold tailWord_2297933
  simp only [CollatzResearch.WordTrace]
  refine ⟨83812501983988671556514453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55875001322659114371009635 83812501983988671556514453)
  ·
    refine ⟨3928711030499468979211615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 83812501983988671556514453 3928711030499468979211615)
    ·
      refine ⟨5893066545749203468817423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3928711030499468979211615 5893066545749203468817423)
      ·
        refine ⟨8839599818623805203226135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5893066545749203468817423 8839599818623805203226135)
        ·
          refine ⟨13259399727935707804839203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8839599818623805203226135 13259399727935707804839203)
          ·
            refine ⟨19889099591903561707258805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13259399727935707804839203 19889099591903561707258805)
            ·
              refine ⟨1864603086740958910055513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19889099591903561707258805 1864603086740958910055513)
              ·
                refine ⟨1398452315055719182541635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1864603086740958910055513 1398452315055719182541635)
                ·
                  refine ⟨2097678472583578773812453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1398452315055719182541635 2097678472583578773812453)
                  ·
                    refine ⟨393314713609421020089835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2097678472583578773812453 393314713609421020089835)
                    ·
                      rfl

theorem cell23_2297933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 5, 2, 1, 4].length) (baseStart_2297933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2297933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2297933 prefixEnd_2297933 := by exact prefixLift 2297933
  have htrace : WordTrace (prefixWord ++ tailWord_2297933) baseStart_2297933 baseEnd_2297933 := by
    simpa [prefixWord, tailWord_2297933, baseEnd_2297933] using wordTrace_append hprefix tailTrace_2297933
  have hstable : (prefixWord ++ tailWord_2297933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2297933).length < 2 ^ (prefixWord ++ tailWord_2297933).sum := by decide
  have hdescent : baseEnd_2297933 < baseStart_2297933 := by decide
  rcases family_descends (prefixWord ++ tailWord_2297933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2297966 : List Nat := [4, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2]
def baseStart_2297966 : Nat := 118140960795 + 2297966 * 2 ^ 59
def prefixEnd_2297966 : Nat := 4983230072969 + 3 ^ 40 * 2297966 * 2
def baseEnd_2297966 : Nat := 1179961085689861431156853

theorem tailTrace_2297966 : CollatzResearch.WordTrace tailWord_2297966 prefixEnd_2297966 1179961085689861431156853 := by
  unfold tailWord_2297966
  simp only [CollatzResearch.WordTrace]
  refine ⟨10476713199108639774058219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55875803728579412128310501 10476713199108639774058219)
  ·
    refine ⟨15715069798662959661087329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10476713199108639774058219 15715069798662959661087329)
    ·
      refine ⟨11786302348997219745815497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15715069798662959661087329 11786302348997219745815497)
      ·
        refine ⟨8839726761747914809361623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11786302348997219745815497 8839726761747914809361623)
        ·
          refine ⟨13259590142621872214042435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8839726761747914809361623 13259590142621872214042435)
          ·
            refine ⟨19889385213932808321063653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13259590142621872214042435 19889385213932808321063653)
            ·
              refine ⟨3729259727612401560199435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19889385213932808321063653 3729259727612401560199435)
              ·
                refine ⟨5593889591418602340299153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3729259727612401560199435 5593889591418602340299153)
                ·
                  refine ⟨4195417193563951755224365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5593889591418602340299153 4195417193563951755224365)
                  ·
                    refine ⟨1573281447586481908209137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4195417193563951755224365 1573281447586481908209137)
                    ·
                      refine ⟨1179961085689861431156853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1573281447586481908209137 1179961085689861431156853)
                      ·
                        rfl

theorem cell23_2297966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2].length) (baseStart_2297966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2297966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2297966 prefixEnd_2297966 := by exact prefixLift 2297966
  have htrace : WordTrace (prefixWord ++ tailWord_2297966) baseStart_2297966 baseEnd_2297966 := by
    simpa [prefixWord, tailWord_2297966, baseEnd_2297966] using wordTrace_append hprefix tailTrace_2297966
  have hstable : (prefixWord ++ tailWord_2297966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2297966).length < 2 ^ (prefixWord ++ tailWord_2297966).sum := by decide
  have hdescent : baseEnd_2297966 < baseStart_2297966 := by decide
  rcases family_descends (prefixWord ++ tailWord_2297966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2297985 : List Nat := [1, 2, 4, 2, 14]
def baseStart_2297985 : Nat := 118140960795 + 2297985 * 2 ^ 59
def prefixEnd_2297985 : Nat := 4983230072969 + 3 ^ 40 * 2297985 * 2
def baseEnd_2297985 : Nat := 1618615695229488143785

theorem tailTrace_2297985 : CollatzResearch.WordTrace tailWord_2297985 prefixEnd_2297985 1618615695229488143785 := by
  unfold tailWord_2297985
  simp only [CollatzResearch.WordTrace]
  refine ⟨83814398579800284437407409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55876265719866856291604939 83814398579800284437407409)
  ·
    refine ⟨62860798934850213328055557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83814398579800284437407409 62860798934850213328055557)
    ·
      refine ⟨11786399800284414999010417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62860798934850213328055557 11786399800284414999010417)
      ·
        refine ⟨8839799850213311249257813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11786399800284414999010417 8839799850213311249257813)
        ·
          refine ⟨1618615695229488143785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 8839799850213311249257813 1618615695229488143785)
          ·
            rfl

theorem cell23_2297985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 14].length) (baseStart_2297985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2297985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2297985 prefixEnd_2297985 := by exact prefixLift 2297985
  have htrace : WordTrace (prefixWord ++ tailWord_2297985) baseStart_2297985 baseEnd_2297985 := by
    simpa [prefixWord, tailWord_2297985, baseEnd_2297985] using wordTrace_append hprefix tailTrace_2297985
  have hstable : (prefixWord ++ tailWord_2297985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2297985).length < 2 ^ (prefixWord ++ tailWord_2297985).sum := by decide
  have hdescent : baseEnd_2297985 < baseStart_2297985 := by decide
  rcases family_descends (prefixWord ++ tailWord_2297985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2297989 : List Nat := [1, 3, 1, 1, 5, 1, 1, 4, 2, 4]
def baseStart_2297989 : Nat := 118140960795 + 2297989 * 2 ^ 59
def prefixEnd_2297989 : Nat := 4983230072969 + 3 ^ 40 * 2297989 * 2
def baseEnd_2297989 : Nat := 393324298581638280389749

theorem tailTrace_2297989 : CollatzResearch.WordTrace tailWord_2297989 prefixEnd_2297989 393324298581638280389749 := by
  unfold tailWord_2297989
  simp only [CollatzResearch.WordTrace]
  refine ⟨83814544471785793120553021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55876362981190528747035347 83814544471785793120553021)
  ·
    refine ⟨31430454176919672420207383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83814544471785793120553021 31430454176919672420207383)
    ·
      refine ⟨47145681265379508630311075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31430454176919672420207383 47145681265379508630311075)
      ·
        refine ⟨70718521898069262945466613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47145681265379508630311075 70718521898069262945466613)
        ·
          refine ⟨6629861427943993401137495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 70718521898069262945466613 6629861427943993401137495)
          ·
            refine ⟨9944792141915990101706243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6629861427943993401137495 9944792141915990101706243)
            ·
              refine ⟨14917188212873985152559365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9944792141915990101706243 14917188212873985152559365)
              ·
                refine ⟨2796972789913872216104881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14917188212873985152559365 2796972789913872216104881)
                ·
                  refine ⟨2097729592435404162078661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2796972789913872216104881 2097729592435404162078661)
                  ·
                    refine ⟨393324298581638280389749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2097729592435404162078661 393324298581638280389749)
                    ·
                      rfl

theorem cell23_2297989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 4, 2, 4].length) (baseStart_2297989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2297989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2297989 prefixEnd_2297989 := by exact prefixLift 2297989
  have htrace : WordTrace (prefixWord ++ tailWord_2297989) baseStart_2297989 baseEnd_2297989 := by
    simpa [prefixWord, tailWord_2297989, baseEnd_2297989] using wordTrace_append hprefix tailTrace_2297989
  have hstable : (prefixWord ++ tailWord_2297989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2297989).length < 2 ^ (prefixWord ++ tailWord_2297989).sum := by decide
  have hdescent : baseEnd_2297989 < baseStart_2297989 := by decide
  rcases family_descends (prefixWord ++ tailWord_2297989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2298109 : List Nat := [1, 4, 1, 1, 1, 1, 1, 8, 5]
def baseStart_2298109 : Nat := 118140960795 + 2298109 * 2 ^ 59
def prefixEnd_2298109 : Nat := 4983230072969 + 3 ^ 40 * 2298109 * 2
def baseEnd_2298109 : Nat := 131114945935939374629855

theorem tailTrace_2298109 : CollatzResearch.WordTrace tailWord_2298109 prefixEnd_2298109 131114945935939374629855 := by
  unfold tailWord_2298109
  simp only [CollatzResearch.WordTrace]
  refine ⟨83818921231351053614921381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55879280820900702409947587 83818921231351053614921381)
  ·
    refine ⟨15716047730878322552797759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83818921231351053614921381 15716047730878322552797759)
    ·
      refine ⟨23574071596317483829196639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15716047730878322552797759 23574071596317483829196639)
      ·
        refine ⟨35361107394476225743794959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23574071596317483829196639 35361107394476225743794959)
        ·
          refine ⟨53041661091714338615692439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35361107394476225743794959 53041661091714338615692439)
          ·
            refine ⟨79562491637571507923538659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53041661091714338615692439 79562491637571507923538659)
            ·
              refine ⟨119343737456357261885307989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79562491637571507923538659 119343737456357261885307989)
              ·
                refine ⟨1398559423316686662718453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 119343737456357261885307989 1398559423316686662718453)
                ·
                  refine ⟨131114945935939374629855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1398559423316686662718453 131114945935939374629855)
                  ·
                    rfl

theorem cell23_2298109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 8, 5].length) (baseStart_2298109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2298109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2298109 prefixEnd_2298109 := by exact prefixLift 2298109
  have htrace : WordTrace (prefixWord ++ tailWord_2298109) baseStart_2298109 baseEnd_2298109 := by
    simpa [prefixWord, tailWord_2298109, baseEnd_2298109] using wordTrace_append hprefix tailTrace_2298109
  have hstable : (prefixWord ++ tailWord_2298109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2298109).length < 2 ^ (prefixWord ++ tailWord_2298109).sum := by decide
  have hdescent : baseEnd_2298109 < baseStart_2298109 := by decide
  rcases family_descends (prefixWord ++ tailWord_2298109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2298120 : List Nat := [2, 1, 3, 2, 3, 1, 4, 1, 2, 2, 2]
def baseStart_2298120 : Nat := 118140960795 + 2298120 * 2 ^ 59
def prefixEnd_2298120 : Nat := 4983230072969 + 3 ^ 40 * 2298120 * 2
def baseEnd_2298120 : Nat := 1180040161710653828631145

theorem tailTrace_2298120 : CollatzResearch.WordTrace tailWord_2298120 prefixEnd_2298120 1180040161710653828631145 := by
  unfold tailWord_2298120
  simp only [CollatzResearch.WordTrace]
  refine ⟨41909661217155601246785907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55879548289540801662381209 41909661217155601246785907)
  ·
    refine ⟨62864491825733401870178861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41909661217155601246785907 62864491825733401870178861)
    ·
      refine ⟨23574184434650025701317073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62864491825733401870178861 23574184434650025701317073)
      ·
        refine ⟨17680638325987519275987805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23574184434650025701317073 17680638325987519275987805)
        ·
          refine ⟨6630239372245319728495427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17680638325987519275987805 6630239372245319728495427)
          ·
            refine ⟨9945359058367979592743141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6630239372245319728495427 9945359058367979592743141)
            ·
              refine ⟨1864754823443996173639339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9945359058367979592743141 1864754823443996173639339)
              ·
                refine ⟨2797132235165994260459009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1864754823443996173639339 2797132235165994260459009)
                ·
                  refine ⟨2097849176374495695344257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2797132235165994260459009 2097849176374495695344257)
                  ·
                    refine ⟨1573386882280871771508193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2097849176374495695344257 1573386882280871771508193)
                    ·
                      refine ⟨1180040161710653828631145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1573386882280871771508193 1180040161710653828631145)
                      ·
                        rfl

theorem cell23_2298120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 4, 1, 2, 2, 2].length) (baseStart_2298120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2298120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2298120 prefixEnd_2298120 := by exact prefixLift 2298120
  have htrace : WordTrace (prefixWord ++ tailWord_2298120) baseStart_2298120 baseEnd_2298120 := by
    simpa [prefixWord, tailWord_2298120, baseEnd_2298120] using wordTrace_append hprefix tailTrace_2298120
  have hstable : (prefixWord ++ tailWord_2298120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2298120).length < 2 ^ (prefixWord ++ tailWord_2298120).sum := by decide
  have hdescent : baseEnd_2298120 < baseStart_2298120 := by decide
  rcases family_descends (prefixWord ++ tailWord_2298120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2298122 : List Nat := [3, 1, 2, 2, 1, 1, 2, 1, 3, 7]
def baseStart_2298122 : Nat := 118140960795 + 2298122 * 2 ^ 59
def prefixEnd_2298122 : Nat := 4983230072969 + 3 ^ 40 * 2298122 * 2
def baseEnd_2298122 : Nat := 393347062890654273602045

theorem tailTrace_2298122 : CollatzResearch.WordTrace tailWord_2298122 prefixEnd_2298122 393347062890654273602045 := by
  unfold tailWord_2298122
  simp only [CollatzResearch.WordTrace]
  refine ⟨20954848845075989208786155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55879596920202637890096413 20954848845075989208786155)
  ·
    refine ⟨31432273267613983813179233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20954848845075989208786155 31432273267613983813179233)
    ·
      refine ⟨23574204950710487859884425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31432273267613983813179233 23574204950710487859884425)
      ·
        refine ⟨17680653713032865894913319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23574204950710487859884425 17680653713032865894913319)
        ·
          refine ⟨26520980569549298842369979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17680653713032865894913319 26520980569549298842369979)
          ·
            refine ⟨39781470854323948263554969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26520980569549298842369979 39781470854323948263554969)
            ·
              refine ⟨29836103140742961197666227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39781470854323948263554969 29836103140742961197666227)
              ·
                refine ⟨44754154711114441796499341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29836103140742961197666227 44754154711114441796499341)
                ·
                  refine ⟨16782808016667915673687253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44754154711114441796499341 16782808016667915673687253)
                  ·
                    refine ⟨393347062890654273602045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16782808016667915673687253 393347062890654273602045)
                    ·
                      rfl

theorem cell23_2298122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 1, 3, 7].length) (baseStart_2298122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2298122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2298122 prefixEnd_2298122 := by exact prefixLift 2298122
  have htrace : WordTrace (prefixWord ++ tailWord_2298122) baseStart_2298122 baseEnd_2298122 := by
    simpa [prefixWord, tailWord_2298122, baseEnd_2298122] using wordTrace_append hprefix tailTrace_2298122
  have hstable : (prefixWord ++ tailWord_2298122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2298122).length < 2 ^ (prefixWord ++ tailWord_2298122).sum := by decide
  have hdescent : baseEnd_2298122 < baseStart_2298122 := by decide
  rcases family_descends (prefixWord ++ tailWord_2298122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2298159 : List Nat := [1, 1, 2, 1, 2, 1, 6, 2, 2, 1, 4]
def baseStart_2298159 : Nat := 118140960795 + 2298159 * 2 ^ 59
def prefixEnd_2298159 : Nat := 4983230072969 + 3 ^ 40 * 2298159 * 2
def baseEnd_2298159 : Nat := 1180060187456179176043465

theorem tailTrace_2298159 : CollatzResearch.WordTrace tailWord_2298159 prefixEnd_2298159 1180060187456179176043465 := by
  unfold tailWord_2298159
  simp only [CollatzResearch.WordTrace]
  refine ⟨83820744881169912154241531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55880496587446608102827687 83820744881169912154241531)
  ·
    refine ⟨125731117321754868231362297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83820744881169912154241531 125731117321754868231362297)
    ·
      refine ⟨94298337991316151173521723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125731117321754868231362297 94298337991316151173521723)
      ·
        refine ⟨141447506986974226760282585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94298337991316151173521723 141447506986974226760282585)
        ·
          refine ⟨106085630240230670070211939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 141447506986974226760282585 106085630240230670070211939)
          ·
            refine ⟨159128445360346005105317909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106085630240230670070211939 159128445360346005105317909)
            ·
              refine ⟨7459145876266218989311777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 159128445360346005105317909 7459145876266218989311777)
              ·
                refine ⟨5594359407199664241983833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7459145876266218989311777 5594359407199664241983833)
                ·
                  refine ⟨4195769555399748181487875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5594359407199664241983833 4195769555399748181487875)
                  ·
                    refine ⟨6293654333099622272231813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4195769555399748181487875 6293654333099622272231813)
                    ·
                      refine ⟨1180060187456179176043465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6293654333099622272231813 1180060187456179176043465)
                      ·
                        rfl

theorem cell23_2298159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 2, 2, 1, 4].length) (baseStart_2298159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2298159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2298159 prefixEnd_2298159 := by exact prefixLift 2298159
  have htrace : WordTrace (prefixWord ++ tailWord_2298159) baseStart_2298159 baseEnd_2298159 := by
    simpa [prefixWord, tailWord_2298159, baseEnd_2298159] using wordTrace_append hprefix tailTrace_2298159
  have hstable : (prefixWord ++ tailWord_2298159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2298159).length < 2 ^ (prefixWord ++ tailWord_2298159).sum := by decide
  have hdescent : baseEnd_2298159 < baseStart_2298159 := by decide
  rcases family_descends (prefixWord ++ tailWord_2298159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2298179 : List Nat := [1, 1, 1, 3, 1, 3, 2, 2, 4, 2, 3]
def baseStart_2298179 : Nat := 118140960795 + 2298179 * 2 ^ 59
def prefixEnd_2298179 : Nat := 4983230072969 + 3 ^ 40 * 2298179 * 2
def baseEnd_2298179 : Nat := 1180070457069269097793373

theorem tailTrace_2298179 : CollatzResearch.WordTrace tailWord_2298179 prefixEnd_2298179 1180070457069269097793373 := by
  unfold tailWord_2298179
  simp only [CollatzResearch.WordTrace]
  refine ⟨83821474341097455569969591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55880982894064970379979727 83821474341097455569969591)
  ·
    refine ⟨125732211511646183354954387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83821474341097455569969591 125732211511646183354954387)
    ·
      refine ⟨188598317267469275032431581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125732211511646183354954387 188598317267469275032431581)
      ·
        refine ⟨70724368975300978137161843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 188598317267469275032431581 70724368975300978137161843)
        ·
          refine ⟨106086553462951467205742765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70724368975300978137161843 106086553462951467205742765)
          ·
            refine ⟨39782457548606800202153537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 106086553462951467205742765 39782457548606800202153537)
            ·
              refine ⟨29836843161455100151615153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39782457548606800202153537 29836843161455100151615153)
              ·
                refine ⟨22377632371091325113711365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29836843161455100151615153 22377632371091325113711365)
                ·
                  refine ⟨4195806069579623458820881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22377632371091325113711365 4195806069579623458820881)
                  ·
                    refine ⟨3146854552184717594115661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4195806069579623458820881 3146854552184717594115661)
                    ·
                      refine ⟨1180070457069269097793373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3146854552184717594115661 1180070457069269097793373)
                      ·
                        rfl

theorem cell23_2298179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 4, 2, 3].length) (baseStart_2298179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2298179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2298179 prefixEnd_2298179 := by exact prefixLift 2298179
  have htrace : WordTrace (prefixWord ++ tailWord_2298179) baseStart_2298179 baseEnd_2298179 := by
    simpa [prefixWord, tailWord_2298179, baseEnd_2298179] using wordTrace_append hprefix tailTrace_2298179
  have hstable : (prefixWord ++ tailWord_2298179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2298179).length < 2 ^ (prefixWord ++ tailWord_2298179).sum := by decide
  have hdescent : baseEnd_2298179 < baseStart_2298179 := by decide
  rcases family_descends (prefixWord ++ tailWord_2298179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2298196 : List Nat := [2, 4, 1, 1, 2, 3, 1, 1, 1, 4, 3]
def baseStart_2298196 : Nat := 118140960795 + 2298196 * 2 ^ 59
def prefixEnd_2298196 : Nat := 4983230072969 + 3 ^ 40 * 2298196 * 2
def baseEnd_2298196 : Nat := 1180079186240395531280795

theorem tailTrace_2298196 : CollatzResearch.WordTrace tailWord_2298196 prefixEnd_2298196 1180079186240395531280795 := by
  unfold tailWord_2298196
  simp only [CollatzResearch.WordTrace]
  refine ⟨41911047191017933736669221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55881396254690578315558961 41911047191017933736669221)
  ·
    refine ⟨7858321348315862575625479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41911047191017933736669221 7858321348315862575625479)
    ·
      refine ⟨11787482022473793863438219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7858321348315862575625479 11787482022473793863438219)
      ·
        refine ⟨17681223033710690795157329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11787482022473793863438219 17681223033710690795157329)
        ·
          refine ⟨13260917275283018096367997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17681223033710690795157329 13260917275283018096367997)
          ·
            refine ⟨4972843978231131786137999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13260917275283018096367997 4972843978231131786137999)
            ·
              refine ⟨7459265967346697679206999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4972843978231131786137999 7459265967346697679206999)
              ·
                refine ⟨11188898951020046518810499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7459265967346697679206999 11188898951020046518810499)
                ·
                  refine ⟨16783348426530069778215749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11188898951020046518810499 16783348426530069778215749)
                  ·
                    refine ⟨3146877829974388083415453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16783348426530069778215749 3146877829974388083415453)
                    ·
                      refine ⟨1180079186240395531280795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3146877829974388083415453 1180079186240395531280795)
                      ·
                        rfl

theorem cell23_2298196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 1, 1, 4, 3].length) (baseStart_2298196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2298196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2298196 prefixEnd_2298196 := by exact prefixLift 2298196
  have htrace : WordTrace (prefixWord ++ tailWord_2298196) baseStart_2298196 baseEnd_2298196 := by
    simpa [prefixWord, tailWord_2298196, baseEnd_2298196] using wordTrace_append hprefix tailTrace_2298196
  have hstable : (prefixWord ++ tailWord_2298196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2298196).length < 2 ^ (prefixWord ++ tailWord_2298196).sum := by decide
  have hdescent : baseEnd_2298196 < baseStart_2298196 := by decide
  rcases family_descends (prefixWord ++ tailWord_2298196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2298216 : List Nat := [2, 1, 4, 2, 2, 1, 3, 2, 6]
def baseStart_2298216 : Nat := 118140960795 + 2298216 * 2 ^ 59
def prefixEnd_2298216 : Nat := 4983230072969 + 3 ^ 40 * 2298216 * 2
def baseEnd_2298216 : Nat := 131121050650387272558967

theorem tailTrace_2298216 : CollatzResearch.WordTrace tailWord_2298216 prefixEnd_2298216 131121050650387272558967 := by
  unfold tailWord_2298216
  simp only [CollatzResearch.WordTrace]
  refine ⟨41911411920981705444533251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55881882561308940592711001 41911411920981705444533251)
  ·
    refine ⟨62867117881472558166799877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41911411920981705444533251 62867117881472558166799877)
    ·
      refine ⟨11787584602776104656274977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62867117881472558166799877 11787584602776104656274977)
      ·
        refine ⟨8840688452082078492206233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11787584602776104656274977 8840688452082078492206233)
        ·
          refine ⟨6630516339061558869154675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8840688452082078492206233 6630516339061558869154675)
          ·
            refine ⟨9945774508592338303732013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6630516339061558869154675 9945774508592338303732013)
            ·
              refine ⟨3729665440722126863899505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9945774508592338303732013 3729665440722126863899505)
              ·
                refine ⟨2797249080541595147924629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3729665440722126863899505 2797249080541595147924629)
                ·
                  refine ⟨131121050650387272558967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2797249080541595147924629 131121050650387272558967)
                  ·
                    rfl

theorem cell23_2298216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 3, 2, 6].length) (baseStart_2298216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2298216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2298216 prefixEnd_2298216 := by exact prefixLift 2298216
  have htrace : WordTrace (prefixWord ++ tailWord_2298216) baseStart_2298216 baseEnd_2298216 := by
    simpa [prefixWord, tailWord_2298216, baseEnd_2298216] using wordTrace_append hprefix tailTrace_2298216
  have hstable : (prefixWord ++ tailWord_2298216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2298216).length < 2 ^ (prefixWord ++ tailWord_2298216).sum := by decide
  have hdescent : baseEnd_2298216 < baseStart_2298216 := by decide
  rcases family_descends (prefixWord ++ tailWord_2298216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2298236 : List Nat := [2, 2, 2, 1, 1, 1, 2, 1, 6, 3, 2]
def baseStart_2298236 : Nat := 118140960795 + 2298236 * 2 ^ 59
def prefixEnd_2298236 : Nat := 4983230072969 + 3 ^ 40 * 2298236 * 2
def baseEnd_2298236 : Nat := 1180099725466575374780611

theorem tailTrace_2298236 : CollatzResearch.WordTrace tailWord_2298236 prefixEnd_2298236 1180099725466575374780611 := by
  unfold tailWord_2298236
  simp only [CollatzResearch.WordTrace]
  refine ⟨41911776650945477152397281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55882368867927302869863041 41911776650945477152397281)
  ·
    refine ⟨31433832488209107864297961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41911776650945477152397281 31433832488209107864297961)
    ·
      refine ⟨23575374366156830898223471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31433832488209107864297961 23575374366156830898223471)
      ·
        refine ⟨35363061549235246347335207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23575374366156830898223471 35363061549235246347335207)
        ·
          refine ⟨53044592323852869521002811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35363061549235246347335207 53044592323852869521002811)
          ·
            refine ⟨79566888485779304281504217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53044592323852869521002811 79566888485779304281504217)
            ·
              refine ⟨59675166364334478211128163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79566888485779304281504217 59675166364334478211128163)
              ·
                refine ⟨89512749546501717316692245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59675166364334478211128163 89512749546501717316692245)
                ·
                  refine ⟨4195910134992267999219949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 89512749546501717316692245 4195910134992267999219949)
                  ·
                    refine ⟨1573466300622100499707481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4195910134992267999219949 1573466300622100499707481)
                    ·
                      refine ⟨1180099725466575374780611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1573466300622100499707481 1180099725466575374780611)
                      ·
                        rfl

theorem cell23_2298236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 6, 3, 2].length) (baseStart_2298236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2298236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2298236 prefixEnd_2298236 := by exact prefixLift 2298236
  have htrace : WordTrace (prefixWord ++ tailWord_2298236) baseStart_2298236 baseEnd_2298236 := by
    simpa [prefixWord, tailWord_2298236, baseEnd_2298236] using wordTrace_append hprefix tailTrace_2298236
  have hstable : (prefixWord ++ tailWord_2298236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2298236).length < 2 ^ (prefixWord ++ tailWord_2298236).sum := by decide
  have hdescent : baseEnd_2298236 < baseStart_2298236 := by decide
  rcases family_descends (prefixWord ++ tailWord_2298236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2298270 : List Nat := [4, 3, 1, 2, 1, 1, 1, 1, 4, 3, 2]
def baseStart_2298270 : Nat := 118140960795 + 2298270 * 2 ^ 59
def prefixEnd_2298270 : Nat := 4983230072969 + 3 ^ 40 * 2298270 * 2
def baseEnd_2298270 : Nat := 1180117183808828241755455

theorem tailTrace_2298270 : CollatzResearch.WordTrace tailWord_2298270 prefixEnd_2298270 1180117183808828241755455 := by
  unfold tailWord_2298270
  simp only [CollatzResearch.WordTrace]
  refine ⟨10478099172970972263941533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55883195589178518741021509 10478099172970972263941533)
  ·
    refine ⟨3929287189864114598978075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10478099172970972263941533 3929287189864114598978075)
    ·
      refine ⟨5893930784796171898467113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3929287189864114598978075 5893930784796171898467113)
      ·
        refine ⟨4420448088597128923850335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5893930784796171898467113 4420448088597128923850335)
        ·
          refine ⟨6630672132895693385775503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4420448088597128923850335 6630672132895693385775503)
          ·
            refine ⟨9946008199343540078663255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6630672132895693385775503 9946008199343540078663255)
            ·
              refine ⟨14919012299015310117994883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9946008199343540078663255 14919012299015310117994883)
              ·
                refine ⟨22378518448522965176992325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14919012299015310117994883 22378518448522965176992325)
                ·
                  refine ⟨4195972209098055970686061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22378518448522965176992325 4195972209098055970686061)
                  ·
                    refine ⟨1573489578411770989007273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4195972209098055970686061 1573489578411770989007273)
                    ·
                      refine ⟨1180117183808828241755455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1573489578411770989007273 1180117183808828241755455)
                      ·
                        rfl

theorem cell23_2298270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 1, 4, 3, 2].length) (baseStart_2298270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2298270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2298270 prefixEnd_2298270 := by exact prefixLift 2298270
  have htrace : WordTrace (prefixWord ++ tailWord_2298270) baseStart_2298270 baseEnd_2298270 := by
    simpa [prefixWord, tailWord_2298270, baseEnd_2298270] using wordTrace_append hprefix tailTrace_2298270
  have hstable : (prefixWord ++ tailWord_2298270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2298270).length < 2 ^ (prefixWord ++ tailWord_2298270).sum := by decide
  have hdescent : baseEnd_2298270 < baseStart_2298270 := by decide
  rcases family_descends (prefixWord ++ tailWord_2298270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2298276 : List Nat := [2, 3, 1, 2, 1, 1, 4, 1, 4, 4]
def baseStart_2298276 : Nat := 118140960795 + 2298276 * 2 ^ 59
def prefixEnd_2298276 : Nat := 4983230072969 + 3 ^ 40 * 2298276 * 2
def baseEnd_2298276 : Nat := 393373421564251739426809

theorem tailTrace_2298276 : CollatzResearch.WordTrace tailWord_2298276 prefixEnd_2298276 393373421564251739426809 := by
  unfold tailWord_2298276
  simp only [CollatzResearch.WordTrace]
  refine ⟨41912506110873020568125341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55883341481164027424167121 41912506110873020568125341)
  ·
    refine ⟨15717189791577382713047003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41912506110873020568125341 15717189791577382713047003)
    ·
      refine ⟨23575784687366074069570505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15717189791577382713047003 23575784687366074069570505)
      ·
        refine ⟨17681838515524555552177879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23575784687366074069570505 17681838515524555552177879)
        ·
          refine ⟨26522757773286833328266819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17681838515524555552177879 26522757773286833328266819)
          ·
            refine ⟨39784136659930249992400229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26522757773286833328266819 39784136659930249992400229)
            ·
              refine ⟨7459525623736921873575043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39784136659930249992400229 7459525623736921873575043)
              ·
                refine ⟨11189288435605382810362565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7459525623736921873575043 11189288435605382810362565)
                ·
                  refine ⟨2097991581676009276942981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11189288435605382810362565 2097991581676009276942981)
                  ·
                    refine ⟨393373421564251739426809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2097991581676009276942981 393373421564251739426809)
                    ·
                      rfl

theorem cell23_2298276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 1, 4, 4].length) (baseStart_2298276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2298276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2298276 prefixEnd_2298276 := by exact prefixLift 2298276
  have htrace : WordTrace (prefixWord ++ tailWord_2298276) baseStart_2298276 baseEnd_2298276 := by
    simpa [prefixWord, tailWord_2298276, baseEnd_2298276] using wordTrace_append hprefix tailTrace_2298276
  have hstable : (prefixWord ++ tailWord_2298276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2298276).length < 2 ^ (prefixWord ++ tailWord_2298276).sum := by decide
  have hdescent : baseEnd_2298276 < baseStart_2298276 := by decide
  rcases family_descends (prefixWord ++ tailWord_2298276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2298289 : List Nat := [1, 2, 2, 4, 1, 2, 1, 10]
def baseStart_2298289 : Nat := 118140960795 + 2298289 * 2 ^ 59
def prefixEnd_2298289 : Nat := 4983230072969 + 3 ^ 40 * 2298289 * 2
def baseEnd_2298289 : Nat := 43708405183009765459921

theorem tailTrace_2298289 : CollatzResearch.WordTrace tailWord_2298289 prefixEnd_2298289 43708405183009765459921 := by
  unfold tailWord_2298289
  simp only [CollatzResearch.WordTrace]
  refine ⟨83825486370698944356473921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55883657580465962904315947 83825486370698944356473921)
  ·
    refine ⟨62869114778024208267355441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83825486370698944356473921 62869114778024208267355441)
    ·
      refine ⟨47151836083518156200516581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62869114778024208267355441 47151836083518156200516581)
      ·
        refine ⟨8840969265659654287596859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47151836083518156200516581 8840969265659654287596859)
        ·
          refine ⟨13261453898489481431395289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8840969265659654287596859 13261453898489481431395289)
          ·
            refine ⟨9946090423867111073546467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13261453898489481431395289 9946090423867111073546467)
            ·
              refine ⟨14919135635800666610319701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9946090423867111073546467 14919135635800666610319701)
              ·
                refine ⟨43708405183009765459921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 14919135635800666610319701 43708405183009765459921)
                ·
                  rfl

theorem cell23_2298289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 10].length) (baseStart_2298289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2298289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2298289 prefixEnd_2298289 := by exact prefixLift 2298289
  have htrace : WordTrace (prefixWord ++ tailWord_2298289) baseStart_2298289 baseEnd_2298289 := by
    simpa [prefixWord, tailWord_2298289, baseEnd_2298289] using wordTrace_append hprefix tailTrace_2298289
  have hstable : (prefixWord ++ tailWord_2298289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2298289).length < 2 ^ (prefixWord ++ tailWord_2298289).sum := by decide
  have hdescent : baseEnd_2298289 < baseStart_2298289 := by decide
  rcases family_descends (prefixWord ++ tailWord_2298289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2298300 : List Nat := [2, 2, 2, 4, 1, 3, 1, 2, 1, 1, 4]
def baseStart_2298300 : Nat := 118140960795 + 2298300 * 2 ^ 59
def prefixEnd_2298300 : Nat := 4983230072969 + 3 ^ 40 * 2298300 * 2
def baseEnd_2298300 : Nat := 1180132588228463124380317

theorem tailTrace_2298300 : CollatzResearch.WordTrace tailWord_2298300 prefixEnd_2298300 1180132588228463124380317 := by
  unfold tailWord_2298300
  simp only [CollatzResearch.WordTrace]
  refine ⟨41912943786829546617562177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55883925049106062156749569 41912943786829546617562177)
  ·
    refine ⟨31434707840122159963171633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41912943786829546617562177 31434707840122159963171633)
    ·
      refine ⟨23576030880091619972378725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31434707840122159963171633 23576030880091619972378725)
      ·
        refine ⟨4420505790017178744821011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23576030880091619972378725 4420505790017178744821011)
        ·
          refine ⟨6630758685025768117231517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4420505790017178744821011 6630758685025768117231517)
          ·
            refine ⟨2486534506884663043961819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6630758685025768117231517 2486534506884663043961819)
            ·
              refine ⟨3729801760326994565942729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2486534506884663043961819 3729801760326994565942729)
              ·
                refine ⟨2797351320245245924457047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3729801760326994565942729 2797351320245245924457047)
                ·
                  refine ⟨4196026980367868886685571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2797351320245245924457047 4196026980367868886685571)
                  ·
                    refine ⟨6294040470551803330028357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4196026980367868886685571 6294040470551803330028357)
                    ·
                      refine ⟨1180132588228463124380317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6294040470551803330028357 1180132588228463124380317)
                      ·
                        rfl

theorem cell23_2298300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_2298300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2298300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2298300 prefixEnd_2298300 := by exact prefixLift 2298300
  have htrace : WordTrace (prefixWord ++ tailWord_2298300) baseStart_2298300 baseEnd_2298300 := by
    simpa [prefixWord, tailWord_2298300, baseEnd_2298300] using wordTrace_append hprefix tailTrace_2298300
  have hstable : (prefixWord ++ tailWord_2298300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2298300).length < 2 ^ (prefixWord ++ tailWord_2298300).sum := by decide
  have hdescent : baseEnd_2298300 < baseStart_2298300 := by decide
  rcases family_descends (prefixWord ++ tailWord_2298300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2298343 : List Nat := [1, 1, 5, 2, 1, 1, 1, 1, 5, 3, 2]
def baseStart_2298343 : Nat := 118140960795 + 2298343 * 2 ^ 59
def prefixEnd_2298343 : Nat := 4983230072969 + 3 ^ 40 * 2298343 * 2
def baseEnd_2298343 : Nat := 1180154667896606456142619

theorem tailTrace_2298343 : CollatzResearch.WordTrace tailWord_2298343 prefixEnd_2298343 1180154667896606456142619 := by
  unfold tailWord_2298343
  simp only [CollatzResearch.WordTrace]
  refine ⟨83827455912503311578939683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55884970608335541052626455 83827455912503311578939683)
  ·
    refine ⟨125741183868754967368409525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83827455912503311578939683 125741183868754967368409525)
    ·
      refine ⟨11788235987695778190788393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 125741183868754967368409525 11788235987695778190788393)
      ·
        refine ⟨8841176990771833643091295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11788235987695778190788393 8841176990771833643091295)
        ·
          refine ⟨13261765486157750464636943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8841176990771833643091295 13261765486157750464636943)
          ·
            refine ⟨19892648229236625696955415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13261765486157750464636943 19892648229236625696955415)
            ·
              refine ⟨29838972343854938545433123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19892648229236625696955415 29838972343854938545433123)
              ·
                refine ⟨44758458515782407818149685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29838972343854938545433123 44758458515782407818149685)
                ·
                  refine ⟨4196105485854600732951533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44758458515782407818149685 4196105485854600732951533)
                  ·
                    refine ⟨1573539557195475274856825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4196105485854600732951533 1573539557195475274856825)
                    ·
                      refine ⟨1180154667896606456142619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1573539557195475274856825 1180154667896606456142619)
                      ·
                        rfl

theorem cell23_2298343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 1, 5, 3, 2].length) (baseStart_2298343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2298343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2298343 prefixEnd_2298343 := by exact prefixLift 2298343
  have htrace : WordTrace (prefixWord ++ tailWord_2298343) baseStart_2298343 baseEnd_2298343 := by
    simpa [prefixWord, tailWord_2298343, baseEnd_2298343] using wordTrace_append hprefix tailTrace_2298343
  have hstable : (prefixWord ++ tailWord_2298343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2298343).length < 2 ^ (prefixWord ++ tailWord_2298343).sum := by decide
  have hdescent : baseEnd_2298343 < baseStart_2298343 := by decide
  rcases family_descends (prefixWord ++ tailWord_2298343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2298350 : List Nat := [4, 1, 2, 1, 2, 2, 2, 3, 2, 1, 3]
def baseStart_2298350 : Nat := 118140960795 + 2298350 * 2 ^ 59
def prefixEnd_2298350 : Nat := 4983230072969 + 3 ^ 40 * 2298350 * 2
def baseEnd_2298350 : Nat := 1180158262261187928755087

theorem tailTrace_2298350 : CollatzResearch.WordTrace tailWord_2298350 prefixEnd_2298350 1180158262261187928755087 := by
  unfold tailWord_2298350
  simp only [CollatzResearch.WordTrace]
  refine ⟨10478463902934743971805563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55885140815651967849629669 10478463902934743971805563)
  ·
    refine ⟨15717695854402115957708345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10478463902934743971805563 15717695854402115957708345)
    ·
      refine ⟨11788271890801586968281259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15717695854402115957708345 11788271890801586968281259)
      ·
        refine ⟨17682407836202380452421889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11788271890801586968281259 17682407836202380452421889)
        ·
          refine ⟨13261805877151785339316417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17682407836202380452421889 13261805877151785339316417)
          ·
            refine ⟨9946354407863839004487313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13261805877151785339316417 9946354407863839004487313)
            ·
              refine ⟨7459765805897879253365485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9946354407863839004487313 7459765805897879253365485)
              ·
                refine ⟨2797412177211704720012057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7459765805897879253365485 2797412177211704720012057)
                ·
                  refine ⟨2098059132908778540009043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2797412177211704720012057 2098059132908778540009043)
                  ·
                    refine ⟨3147088699363167810013565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2098059132908778540009043 3147088699363167810013565)
                    ·
                      refine ⟨1180158262261187928755087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3147088699363167810013565 1180158262261187928755087)
                      ·
                        rfl

theorem cell23_2298350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 3, 2, 1, 3].length) (baseStart_2298350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2298350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2298350 prefixEnd_2298350 := by exact prefixLift 2298350
  have htrace : WordTrace (prefixWord ++ tailWord_2298350) baseStart_2298350 baseEnd_2298350 := by
    simpa [prefixWord, tailWord_2298350, baseEnd_2298350] using wordTrace_append hprefix tailTrace_2298350
  have hstable : (prefixWord ++ tailWord_2298350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2298350).length < 2 ^ (prefixWord ++ tailWord_2298350).sum := by decide
  have hdescent : baseEnd_2298350 < baseStart_2298350 := by decide
  rcases family_descends (prefixWord ++ tailWord_2298350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2298373 : List Nat := [1, 3, 1, 1, 2, 2, 4, 2, 1, 4, 2]
def baseStart_2298373 : Nat := 118140960795 + 2298373 * 2 ^ 59
def prefixEnd_2298373 : Nat := 4983230072969 + 3 ^ 40 * 2298373 * 2
def baseEnd_2298373 : Nat := 1180170072316241338767481

theorem tailTrace_2298373 : CollatzResearch.WordTrace tailWord_2298373 prefixEnd_2298373 1180170072316241338767481 := by
  unfold tailWord_2298373
  simp only [CollatzResearch.WordTrace]
  refine ⟨83828550102394626702531773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55885700068263084468354515 83828550102394626702531773)
  ·
    refine ⟨31435706288397985013449415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83828550102394626702531773 31435706288397985013449415)
    ·
      refine ⟨47153559432596977520174123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31435706288397985013449415 47153559432596977520174123)
      ·
        refine ⟨70730339148895466280261185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47153559432596977520174123 70730339148895466280261185)
        ·
          refine ⟨53047754361671599710195889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70730339148895466280261185 53047754361671599710195889)
          ·
            refine ⟨39785815771253699782646917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53047754361671599710195889 39785815771253699782646917)
            ·
              refine ⟨7459840457110068709246297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39785815771253699782646917 7459840457110068709246297)
              ·
                refine ⟨5594880342832551531934723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7459840457110068709246297 5594880342832551531934723)
                ·
                  refine ⟨8392320514248827297902085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5594880342832551531934723 8392320514248827297902085)
                  ·
                    refine ⟨1573560096421655118356641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8392320514248827297902085 1573560096421655118356641)
                    ·
                      refine ⟨1180170072316241338767481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1573560096421655118356641 1180170072316241338767481)
                      ·
                        rfl

theorem cell23_2298373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 2, 1, 4, 2].length) (baseStart_2298373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2298373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2298373 prefixEnd_2298373 := by exact prefixLift 2298373
  have htrace : WordTrace (prefixWord ++ tailWord_2298373) baseStart_2298373 baseEnd_2298373 := by
    simpa [prefixWord, tailWord_2298373, baseEnd_2298373] using wordTrace_append hprefix tailTrace_2298373
  have hstable : (prefixWord ++ tailWord_2298373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2298373).length < 2 ^ (prefixWord ++ tailWord_2298373).sum := by decide
  have hdescent : baseEnd_2298373 < baseStart_2298373 := by decide
  rcases family_descends (prefixWord ++ tailWord_2298373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2298396 : List Nat := [2, 2, 3, 1, 2, 2, 1, 3, 7]
def baseStart_2298396 : Nat := 118140960795 + 2298396 * 2 ^ 59
def prefixEnd_2298396 : Nat := 4983230072969 + 3 ^ 40 * 2298396 * 2
def baseEnd_2298396 : Nat := 131131320263477194308875

theorem tailTrace_2298396 : CollatzResearch.WordTrace tailWord_2298396 prefixEnd_2298396 131131320263477194308875 := by
  unfold tailWord_2298396
  simp only [CollatzResearch.WordTrace]
  refine ⟨41914694490655650815309521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55886259320874201087079361 41914694490655650815309521)
  ·
    refine ⟨31436020867991738111482141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41914694490655650815309521 31436020867991738111482141)
    ·
      refine ⟨11788507825496901791805803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31436020867991738111482141 11788507825496901791805803)
      ·
        refine ⟨17682761738245352687708705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11788507825496901791805803 17682761738245352687708705)
        ·
          refine ⟨13262071303684014515781529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17682761738245352687708705 13262071303684014515781529)
          ·
            refine ⟨9946553477763010886836147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13262071303684014515781529 9946553477763010886836147)
            ·
              refine ⟨14919830216644516330254221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9946553477763010886836147 14919830216644516330254221)
              ·
                refine ⟨5594936331241693623845333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14919830216644516330254221 5594936331241693623845333)
                ·
                  refine ⟨131131320263477194308875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5594936331241693623845333 131131320263477194308875)
                  ·
                    rfl

theorem cell23_2298396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 3, 7].length) (baseStart_2298396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2298396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2298396 prefixEnd_2298396 := by exact prefixLift 2298396
  have htrace : WordTrace (prefixWord ++ tailWord_2298396) baseStart_2298396 baseEnd_2298396 := by
    simpa [prefixWord, tailWord_2298396, baseEnd_2298396] using wordTrace_append hprefix tailTrace_2298396
  have hstable : (prefixWord ++ tailWord_2298396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2298396).length < 2 ^ (prefixWord ++ tailWord_2298396).sum := by decide
  have hdescent : baseEnd_2298396 < baseStart_2298396 := by decide
  rcases family_descends (prefixWord ++ tailWord_2298396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2298426 : List Nat := [3, 1, 1, 1, 3, 3, 2, 1, 1, 7]
def baseStart_2298426 : Nat := 118140960795 + 2298426 * 2 ^ 59
def prefixEnd_2298426 : Nat := 4983230072969 + 3 ^ 40 * 2298426 * 2
def baseEnd_2298426 : Nat := 393399095596976543801579

theorem tailTrace_2298426 : CollatzResearch.WordTrace tailWord_2298426 prefixEnd_2298426 393399095596976543801579 := by
  unfold tailWord_2298426
  simp only [CollatzResearch.WordTrace]
  refine ⟨20957620792800654188552783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55886988780801744502807421 20957620792800654188552783)
  ·
    refine ⟨31436431189200981282829175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20957620792800654188552783 31436431189200981282829175)
    ·
      refine ⟨47154646783801471924243763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31436431189200981282829175 47154646783801471924243763)
      ·
        refine ⟨70731970175702207886365645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47154646783801471924243763 70731970175702207886365645)
        ·
          refine ⟨26524488815888327957387117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70731970175702207886365645 26524488815888327957387117)
          ·
            refine ⟨9946683305958122984020169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26524488815888327957387117 9946683305958122984020169)
            ·
              refine ⟨7460012479468592238015127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9946683305958122984020169 7460012479468592238015127)
              ·
                refine ⟨11190018719202888357022691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7460012479468592238015127 11190018719202888357022691)
                ·
                  refine ⟨16785028078804332535534037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11190018719202888357022691 16785028078804332535534037)
                  ·
                    refine ⟨393399095596976543801579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16785028078804332535534037 393399095596976543801579)
                    ·
                      rfl

theorem cell23_2298426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 1, 1, 7].length) (baseStart_2298426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2298426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2298426 prefixEnd_2298426 := by exact prefixLift 2298426
  have htrace : WordTrace (prefixWord ++ tailWord_2298426) baseStart_2298426 baseEnd_2298426 := by
    simpa [prefixWord, tailWord_2298426, baseEnd_2298426] using wordTrace_append hprefix tailTrace_2298426
  have hstable : (prefixWord ++ tailWord_2298426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2298426).length < 2 ^ (prefixWord ++ tailWord_2298426).sum := by decide
  have hdescent : baseEnd_2298426 < baseStart_2298426 := by decide
  rcases family_descends (prefixWord ++ tailWord_2298426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2298463 : List Nat := [1, 1, 2, 3, 1, 1, 1, 5, 2, 4, 2]
def baseStart_2298463 : Nat := 118140960795 + 2298463 * 2 ^ 59
def prefixEnd_2298463 : Nat := 4983230072969 + 3 ^ 40 * 2298463 * 2
def baseEnd_2298463 : Nat := 1180216285575145986642067

theorem tailTrace_2298463 : CollatzResearch.WordTrace tailWord_2298463 prefixEnd_2298463 1180216285575145986642067 := by
  unfold tailWord_2298463
  simp only [CollatzResearch.WordTrace]
  refine ⟨83831832672068572073308043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55887888448045714715538695 83831832672068572073308043)
  ·
    refine ⟨125747749008102858109962065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83831832672068572073308043 125747749008102858109962065)
    ·
      refine ⟨94310811756077143582471549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125747749008102858109962065 94310811756077143582471549)
      ·
        refine ⟨35366554408528928843426831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94310811756077143582471549 35366554408528928843426831)
        ·
          refine ⟨53049831612793393265140247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35366554408528928843426831 53049831612793393265140247)
          ·
            refine ⟨79574747419190089897710371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53049831612793393265140247 79574747419190089897710371)
            ·
              refine ⟨119362121128785134846565557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79574747419190089897710371 119362121128785134846565557)
              ·
                refine ⟨11190198855823606391865521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 119362121128785134846565557 11190198855823606391865521)
                ·
                  refine ⟨8392649141867704793899141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11190198855823606391865521 8392649141867704793899141)
                  ·
                    refine ⟨1573621714100194648856089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8392649141867704793899141 1573621714100194648856089)
                    ·
                      refine ⟨1180216285575145986642067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1573621714100194648856089 1180216285575145986642067)
                      ·
                        rfl

theorem cell23_2298463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 5, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 5, 2, 4, 2].length) (baseStart_2298463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2298463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2298463 prefixEnd_2298463 := by exact prefixLift 2298463
  have htrace : WordTrace (prefixWord ++ tailWord_2298463) baseStart_2298463 baseEnd_2298463 := by
    simpa [prefixWord, tailWord_2298463, baseEnd_2298463] using wordTrace_append hprefix tailTrace_2298463
  have hstable : (prefixWord ++ tailWord_2298463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2298463).length < 2 ^ (prefixWord ++ tailWord_2298463).sum := by decide
  have hdescent : baseEnd_2298463 < baseStart_2298463 := by decide
  rcases family_descends (prefixWord ++ tailWord_2298463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2298476 : List Nat := [2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 4]
def baseStart_2298476 : Nat := 118140960795 + 2298476 * 2 ^ 59
def prefixEnd_2298476 : Nat := 4983230072969 + 3 ^ 40 * 2298476 * 2
def baseEnd_2298476 : Nat := 1180222960823654435779507

theorem tailTrace_2298476 : CollatzResearch.WordTrace tailWord_2298476 prefixEnd_2298476 1180222960823654435779507 := by
  unfold tailWord_2298476
  simp only [CollatzResearch.WordTrace]
  refine ⟨41916153410510737646765641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55888204547347650195687521 41916153410510737646765641)
  ·
    refine ⟨31437115057883053235074231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41916153410510737646765641 31437115057883053235074231)
    ·
      refine ⟨47155672586824579852611347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31437115057883053235074231 47155672586824579852611347)
      ·
        refine ⟨70733508880236869778917021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47155672586824579852611347 70733508880236869778917021)
        ·
          refine ⟨26525065830088826167093883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70733508880236869778917021 26525065830088826167093883)
          ·
            refine ⟨39787598745133239250640825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26525065830088826167093883 39787598745133239250640825)
            ·
              refine ⟨29840699058849929437980619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39787598745133239250640825 29840699058849929437980619)
              ·
                refine ⟨44761048588274894156970929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29840699058849929437980619 44761048588274894156970929)
                ·
                  refine ⟨33570786441206170617728197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44761048588274894156970929 33570786441206170617728197)
                  ·
                    refine ⟨6294522457726156990824037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33570786441206170617728197 6294522457726156990824037)
                    ·
                      refine ⟨1180222960823654435779507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6294522457726156990824037 1180222960823654435779507)
                      ·
                        rfl

theorem cell23_2298476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 4].length) (baseStart_2298476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2298476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2298476 prefixEnd_2298476 := by exact prefixLift 2298476
  have htrace : WordTrace (prefixWord ++ tailWord_2298476) baseStart_2298476 baseEnd_2298476 := by
    simpa [prefixWord, tailWord_2298476, baseEnd_2298476] using wordTrace_append hprefix tailTrace_2298476
  have hstable : (prefixWord ++ tailWord_2298476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2298476).length < 2 ^ (prefixWord ++ tailWord_2298476).sum := by decide
  have hdescent : baseEnd_2298476 < baseStart_2298476 := by decide
  rcases family_descends (prefixWord ++ tailWord_2298476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2298480 : List Nat := [2, 1, 1, 1, 7, 1, 2, 1, 2, 1, 4]
def baseStart_2298480 : Nat := 118140960795 + 2298480 * 2 ^ 59
def prefixEnd_2298480 : Nat := 4983230072969 + 3 ^ 40 * 2298480 * 2
def baseEnd_2298480 : Nat := 1180225014746272420129489

theorem tailTrace_2298480 : CollatzResearch.WordTrace tailWord_2298480 prefixEnd_2298480 1180225014746272420129489 := by
  unfold tailWord_2298480
  simp only [CollatzResearch.WordTrace]
  refine ⟨41916226356503491988338447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55888301808671322651117929 41916226356503491988338447)
  ·
    refine ⟨62874339534755237982507671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41916226356503491988338447 62874339534755237982507671)
    ·
      refine ⟨94311509302132856973761507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62874339534755237982507671 94311509302132856973761507)
      ·
        refine ⟨141467263953199285460642261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94311509302132856973761507 141467263953199285460642261)
        ·
          refine ⟨3315638998903108252983803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 141467263953199285460642261 3315638998903108252983803)
          ·
            refine ⟨4973458498354662379475705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3315638998903108252983803 4973458498354662379475705)
            ·
              refine ⟨3730093873765996784606779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4973458498354662379475705 3730093873765996784606779)
              ·
                refine ⟨5595140810648995176910169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3730093873765996784606779 5595140810648995176910169)
                ·
                  refine ⟨4196355607986746382682627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5595140810648995176910169 4196355607986746382682627)
                  ·
                    refine ⟨6294533411980119574023941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4196355607986746382682627 6294533411980119574023941)
                    ·
                      refine ⟨1180225014746272420129489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6294533411980119574023941 1180225014746272420129489)
                      ·
                        rfl

theorem cell23_2298480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 2, 1, 2, 1, 4].length) (baseStart_2298480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2298480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2298480 prefixEnd_2298480 := by exact prefixLift 2298480
  have htrace : WordTrace (prefixWord ++ tailWord_2298480) baseStart_2298480 baseEnd_2298480 := by
    simpa [prefixWord, tailWord_2298480, baseEnd_2298480] using wordTrace_append hprefix tailTrace_2298480
  have hstable : (prefixWord ++ tailWord_2298480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2298480).length < 2 ^ (prefixWord ++ tailWord_2298480).sum := by decide
  have hdescent : baseEnd_2298480 < baseStart_2298480 := by decide
  rcases family_descends (prefixWord ++ tailWord_2298480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2298498 : List Nat := [3, 4, 3, 1, 1, 2, 2, 2, 5]
def baseStart_2298498 : Nat := 118140960795 + 2298498 * 2 ^ 59
def prefixEnd_2298498 : Nat := 4983230072969 + 3 ^ 40 * 2298498 * 2
def baseEnd_2298498 : Nat := 131137139710894816633823

theorem tailTrace_2298498 : CollatzResearch.WordTrace tailWord_2298498 prefixEnd_2298498 131137139710894816633823 := by
  unfold tailWord_2298498
  simp only [CollatzResearch.WordTrace]
  refine ⟨20958277306735443262708037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55888739484627848700554765 20958277306735443262708037)
  ·
    refine ⟨3929676995012895611757757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20958277306735443262708037 3929676995012895611757757)
    ·
      refine ⟨1473628873129835854409159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3929676995012895611757757 1473628873129835854409159)
      ·
        refine ⟨2210443309694753781613739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1473628873129835854409159 2210443309694753781613739)
        ·
          refine ⟨3315664964542130672420609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2210443309694753781613739 3315664964542130672420609)
          ·
            refine ⟨2486748723406598004315457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3315664964542130672420609 2486748723406598004315457)
            ·
              refine ⟨1865061542554948503236593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2486748723406598004315457 1865061542554948503236593)
              ·
                refine ⟨1398796156916211377427445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1865061542554948503236593 1398796156916211377427445)
                ·
                  refine ⟨131137139710894816633823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1398796156916211377427445 131137139710894816633823)
                  ·
                    rfl

theorem cell23_2298498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 2, 2, 5].length) (baseStart_2298498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2298498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2298498 prefixEnd_2298498 := by exact prefixLift 2298498
  have htrace : WordTrace (prefixWord ++ tailWord_2298498) baseStart_2298498 baseEnd_2298498 := by
    simpa [prefixWord, tailWord_2298498, baseEnd_2298498] using wordTrace_append hprefix tailTrace_2298498
  have hstable : (prefixWord ++ tailWord_2298498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2298498).length < 2 ^ (prefixWord ++ tailWord_2298498).sum := by decide
  have hdescent : baseEnd_2298498 < baseStart_2298498 := by decide
  rcases family_descends (prefixWord ++ tailWord_2298498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2298500 : List Nat := [2, 3, 2, 1, 3, 1, 2, 2, 2, 2, 3]
def baseStart_2298500 : Nat := 118140960795 + 2298500 * 2 ^ 59
def prefixEnd_2298500 : Nat := 4983230072969 + 3 ^ 40 * 2298500 * 2
def baseEnd_2298500 : Nat := 1180235284359362341879397

theorem tailTrace_2298500 : CollatzResearch.WordTrace tailWord_2298500 prefixEnd_2298500 1180235284359362341879397 := by
  unfold tailWord_2298500
  simp only [CollatzResearch.WordTrace]
  refine ⟨41916591086467263696202477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55888788115289684928269969 41916591086467263696202477)
  ·
    refine ⟨15718721657425223886075929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41916591086467263696202477 15718721657425223886075929)
    ·
      refine ⟨11789041243068917914556947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15718721657425223886075929 11789041243068917914556947)
      ·
        refine ⟨17683561864603376871835421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11789041243068917914556947 17683561864603376871835421)
        ·
          refine ⟨6631335699226266326938283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17683561864603376871835421 6631335699226266326938283)
          ·
            refine ⟨9947003548839399490407425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6631335699226266326938283 9947003548839399490407425)
            ·
              refine ⟨7460252661629549617805569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9947003548839399490407425 7460252661629549617805569)
              ·
                refine ⟨5595189496222162213354177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7460252661629549617805569 5595189496222162213354177)
                ·
                  refine ⟨4196392122166621660015633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5595189496222162213354177 4196392122166621660015633)
                  ·
                    refine ⟨3147294091624966245011725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4196392122166621660015633 3147294091624966245011725)
                    ·
                      refine ⟨1180235284359362341879397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3147294091624966245011725 1180235284359362341879397)
                      ·
                        rfl

theorem cell23_2298500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 2, 2, 2, 3].length) (baseStart_2298500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2298500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2298500 prefixEnd_2298500 := by exact prefixLift 2298500
  have htrace : WordTrace (prefixWord ++ tailWord_2298500) baseStart_2298500 baseEnd_2298500 := by
    simpa [prefixWord, tailWord_2298500, baseEnd_2298500] using wordTrace_append hprefix tailTrace_2298500
  have hstable : (prefixWord ++ tailWord_2298500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2298500).length < 2 ^ (prefixWord ++ tailWord_2298500).sum := by decide
  have hdescent : baseEnd_2298500 < baseStart_2298500 := by decide
  rcases family_descends (prefixWord ++ tailWord_2298500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2298503 : List Nat := [1, 1, 4, 2, 1, 2, 4, 2, 6]
def baseStart_2298503 : Nat := 118140960795 + 2298503 * 2 ^ 59
def prefixEnd_2298503 : Nat := 4983230072969 + 3 ^ 40 * 2298503 * 2
def baseEnd_2298503 : Nat := 131137424977925092237987

theorem tailTrace_2298503 : CollatzResearch.WordTrace tailWord_2298503 prefixEnd_2298503 131137424977925092237987 := by
  unfold tailWord_2298503
  simp only [CollatzResearch.WordTrace]
  refine ⟨83833291591923658904764163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55888861061282439269842775 83833291591923658904764163)
  ·
    refine ⟨125749937387885488357146245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83833291591923658904764163 125749937387885488357146245)
    ·
      refine ⟨23578113260228529066964921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 125749937387885488357146245 23578113260228529066964921)
      ·
        refine ⟨17683584945171396800223691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23578113260228529066964921 17683584945171396800223691)
        ·
          refine ⟨26525377417757095200335537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17683584945171396800223691 26525377417757095200335537)
          ·
            refine ⟨19894033063317821400251653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26525377417757095200335537 19894033063317821400251653)
            ·
              refine ⟨3730131199372091512547185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19894033063317821400251653 3730131199372091512547185)
              ·
                refine ⟨2797598399529068634410389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3730131199372091512547185 2797598399529068634410389)
                ·
                  refine ⟨131137424977925092237987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2797598399529068634410389 131137424977925092237987)
                  ·
                    rfl

theorem cell23_2298503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 4, 2, 6].length) (baseStart_2298503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2298503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2298503 prefixEnd_2298503 := by exact prefixLift 2298503
  have htrace : WordTrace (prefixWord ++ tailWord_2298503) baseStart_2298503 baseEnd_2298503 := by
    simpa [prefixWord, tailWord_2298503, baseEnd_2298503] using wordTrace_append hprefix tailTrace_2298503
  have hstable : (prefixWord ++ tailWord_2298503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2298503).length < 2 ^ (prefixWord ++ tailWord_2298503).sum := by decide
  have hdescent : baseEnd_2298503 < baseStart_2298503 := by decide
  rcases family_descends (prefixWord ++ tailWord_2298503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2298533 : List Nat := [1, 3, 1, 2, 1, 2, 1, 6, 1, 5]
def baseStart_2298533 : Nat := 118140960795 + 2298533 * 2 ^ 59
def prefixEnd_2298533 : Nat := 4983230072969 + 3 ^ 40 * 2298533 * 2
def baseEnd_2298533 : Nat := 393417409740320237588915

theorem tailTrace_2298533 : CollatzResearch.WordTrace tailWord_2298533 prefixEnd_2298533 393417409740320237588915 := by
  unfold tailWord_2298533
  simp only [CollatzResearch.WordTrace]
  refine ⟨83834385781814974028356253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55889590521209982685570835 83834385781814974028356253)
  ·
    refine ⟨31437894668180615260633595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83834385781814974028356253 31437894668180615260633595)
    ·
      refine ⟨47156842002270922890950393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31437894668180615260633595 47156842002270922890950393)
      ·
        refine ⟨35367631501703192168212795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47156842002270922890950393 35367631501703192168212795)
        ·
          refine ⟨53051447252554788252319193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35367631501703192168212795 53051447252554788252319193)
          ·
            refine ⟨39788585439416091189239395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53051447252554788252319193 39788585439416091189239395)
            ·
              refine ⟨59682878159124136783859093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39788585439416091189239395 59682878159124136783859093)
              ·
                refine ⟨2797634913708943911743395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 59682878159124136783859093 2797634913708943911743395)
                ·
                  refine ⟨4196452370563415867615093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2797634913708943911743395 4196452370563415867615093)
                  ·
                    refine ⟨393417409740320237588915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4196452370563415867615093 393417409740320237588915)
                    ·
                      rfl

theorem cell23_2298533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 6, 1, 5].length) (baseStart_2298533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2298533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2298533 prefixEnd_2298533 := by exact prefixLift 2298533
  have htrace : WordTrace (prefixWord ++ tailWord_2298533) baseStart_2298533 baseEnd_2298533 := by
    simpa [prefixWord, tailWord_2298533, baseEnd_2298533] using wordTrace_append hprefix tailTrace_2298533
  have hstable : (prefixWord ++ tailWord_2298533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2298533).length < 2 ^ (prefixWord ++ tailWord_2298533).sum := by decide
  have hdescent : baseEnd_2298533 < baseStart_2298533 := by decide
  rcases family_descends (prefixWord ++ tailWord_2298533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2298547 : List Nat := [1, 1, 1, 2, 3, 4, 1, 5, 1, 1, 3]
def baseStart_2298547 : Nat := 118140960795 + 2298547 * 2 ^ 59
def prefixEnd_2298547 : Nat := 4983230072969 + 3 ^ 40 * 2298547 * 2
def baseEnd_2298547 : Nat := 1180259417950123657991681

theorem tailTrace_2298547 : CollatzResearch.WordTrace tailWord_2298547 prefixEnd_2298547 1180259417950123657991681 := by
  unfold tailWord_2298547
  simp only [CollatzResearch.WordTrace]
  refine ⟨83834896403764254419365895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55889930935842836279577263 83834896403764254419365895)
  ·
    refine ⟨125752344605646381629048843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83834896403764254419365895 125752344605646381629048843)
    ·
      refine ⟨188628516908469572443573265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125752344605646381629048843 188628516908469572443573265)
      ·
        refine ⟨141471387681352179332679949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 188628516908469572443573265 141471387681352179332679949)
        ·
          refine ⟨53051770380507067249754981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 141471387681352179332679949 53051770380507067249754981)
          ·
            refine ⟨9947206946345075109329059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53051770380507067249754981 9947206946345075109329059)
            ·
              refine ⟨14920810419517612663993589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9947206946345075109329059 14920810419517612663993589)
              ·
                refine ⟨1398825976829776187249399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14920810419517612663993589 1398825976829776187249399)
                ·
                  refine ⟨2098238965244664280874099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1398825976829776187249399 2098238965244664280874099)
                  ·
                    refine ⟨3147358447866996421311149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2098238965244664280874099 3147358447866996421311149)
                    ·
                      refine ⟨1180259417950123657991681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3147358447866996421311149 1180259417950123657991681)
                      ·
                        rfl

theorem cell23_2298547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 5, 1, 1, 3].length) (baseStart_2298547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2298547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2298547 prefixEnd_2298547 := by exact prefixLift 2298547
  have htrace : WordTrace (prefixWord ++ tailWord_2298547) baseStart_2298547 baseEnd_2298547 := by
    simpa [prefixWord, tailWord_2298547, baseEnd_2298547] using wordTrace_append hprefix tailTrace_2298547
  have hstable : (prefixWord ++ tailWord_2298547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2298547).length < 2 ^ (prefixWord ++ tailWord_2298547).sum := by decide
  have hdescent : baseEnd_2298547 < baseStart_2298547 := by decide
  rcases family_descends (prefixWord ++ tailWord_2298547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2298564 : List Nat := [2, 3, 3, 1, 1, 2, 2, 4, 1, 1, 3]
def baseStart_2298564 : Nat := 118140960795 + 2298564 * 2 ^ 59
def prefixEnd_2298564 : Nat := 4983230072969 + 3 ^ 40 * 2298564 * 2
def baseEnd_2298564 : Nat := 1180268147121250091479103

theorem tailTrace_2298564 : CollatzResearch.WordTrace tailWord_2298564 prefixEnd_2298564 1180268147121250091479103 := by
  unfold tailWord_2298564
  simp only [CollatzResearch.WordTrace]
  refine ⟨41917758222351333161367373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55890344296468444215156497 41917758222351333161367373)
  ·
    refine ⟨15719159333381749935512765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41917758222351333161367373 15719159333381749935512765)
    ·
      refine ⟨5894684750018156225817287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15719159333381749935512765 5894684750018156225817287)
      ·
        refine ⟨8842027125027234338725931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5894684750018156225817287 8842027125027234338725931)
        ·
          refine ⟨13263040687540851508088897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8842027125027234338725931 13263040687540851508088897)
          ·
            refine ⟨9947280515655638631066673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13263040687540851508088897 9947280515655638631066673)
            ·
              refine ⟨7460460386741728973300005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9947280515655638631066673 7460460386741728973300005)
              ·
                refine ⟨1398836322514074182493751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7460460386741728973300005 1398836322514074182493751)
                ·
                  refine ⟨2098254483771111273740627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1398836322514074182493751 2098254483771111273740627)
                  ·
                    refine ⟨3147381725656666910610941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2098254483771111273740627 3147381725656666910610941)
                    ·
                      refine ⟨1180268147121250091479103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3147381725656666910610941 1180268147121250091479103)
                      ·
                        rfl

theorem cell23_2298564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 4, 1, 1, 3].length) (baseStart_2298564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2298564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2298564 prefixEnd_2298564 := by exact prefixLift 2298564
  have htrace : WordTrace (prefixWord ++ tailWord_2298564) baseStart_2298564 baseEnd_2298564 := by
    simpa [prefixWord, tailWord_2298564, baseEnd_2298564] using wordTrace_append hprefix tailTrace_2298564
  have hstable : (prefixWord ++ tailWord_2298564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2298564).length < 2 ^ (prefixWord ++ tailWord_2298564).sum := by decide
  have hdescent : baseEnd_2298564 < baseStart_2298564 := by decide
  rcases family_descends (prefixWord ++ tailWord_2298564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2298583 : List Nat := [1, 1, 3, 2, 1, 5, 1, 1, 1, 1, 6]
def baseStart_2298583 : Nat := 118140960795 + 2298583 * 2 ^ 59
def prefixEnd_2298583 : Nat := 4983230072969 + 3 ^ 40 * 2298583 * 2
def baseEnd_2298583 : Nat := 1180277903253685517141515

theorem tailTrace_2298583 : CollatzResearch.WordTrace tailWord_2298583 prefixEnd_2298583 1180277903253685517141515 := by
  unfold tailWord_2298583
  simp only [CollatzResearch.WordTrace]
  refine ⟨83836209431633832567676403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55890806287755888378450935 83836209431633832567676403)
  ·
    refine ⟨125754314147450748851514605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83836209431633832567676403 125754314147450748851514605)
    ·
      refine ⟨47157867805294030819317977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 125754314147450748851514605 47157867805294030819317977)
      ·
        refine ⟨35368400853970523114488483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47157867805294030819317977 35368400853970523114488483)
        ·
          refine ⟨53052601280955784671732725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35368400853970523114488483 53052601280955784671732725)
          ·
            refine ⟨4973681370089604812974943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 53052601280955784671732725 4973681370089604812974943)
            ·
              refine ⟨7460522055134407219462415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4973681370089604812974943 7460522055134407219462415)
              ·
                refine ⟨11190783082701610829193623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7460522055134407219462415 11190783082701610829193623)
                ·
                  refine ⟨16786174624052416243790435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11190783082701610829193623 16786174624052416243790435)
                  ·
                    refine ⟨25179261936078624365685653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16786174624052416243790435 25179261936078624365685653)
                    ·
                      refine ⟨1180277903253685517141515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25179261936078624365685653 1180277903253685517141515)
                      ·
                        rfl

theorem cell23_2298583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 1, 1, 1, 6].length) (baseStart_2298583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2298583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2298583 prefixEnd_2298583 := by exact prefixLift 2298583
  have htrace : WordTrace (prefixWord ++ tailWord_2298583) baseStart_2298583 baseEnd_2298583 := by
    simpa [prefixWord, tailWord_2298583, baseEnd_2298583] using wordTrace_append hprefix tailTrace_2298583
  have hstable : (prefixWord ++ tailWord_2298583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2298583).length < 2 ^ (prefixWord ++ tailWord_2298583).sum := by decide
  have hdescent : baseEnd_2298583 < baseStart_2298583 := by decide
  rcases family_descends (prefixWord ++ tailWord_2298583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2298593 : List Nat := [1, 2, 3, 1, 4, 2, 1, 9]
def baseStart_2298593 : Nat := 118140960795 + 2298593 * 2 ^ 59
def prefixEnd_2298593 : Nat := 4983230072969 + 3 ^ 40 * 2298593 * 2
def baseEnd_2298593 : Nat := 43714186594823351037647

theorem tailTrace_2298593 : CollatzResearch.WordTrace tailWord_2298593 prefixEnd_2298593 43714186594823351037647 := by
  unfold tailWord_2298593
  simp only [CollatzResearch.WordTrace]
  refine ⟨83836574161597604275540433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55891049441065069517026955 83836574161597604275540433)
  ·
    refine ⟨62877430621198203206655325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83836574161597604275540433 62877430621198203206655325)
    ·
      refine ⟨23579036482949326202495747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62877430621198203206655325 23579036482949326202495747)
      ·
        refine ⟨35368554724423989303743621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23579036482949326202495747 35368554724423989303743621)
        ·
          refine ⟨6631604010829497994451929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35368554724423989303743621 6631604010829497994451929)
          ·
            refine ⟨4973703008122123495838947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6631604010829497994451929 4973703008122123495838947)
            ·
              refine ⟨7460554512183185243758421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4973703008122123495838947 7460554512183185243758421)
              ·
                refine ⟨43714186594823351037647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7460554512183185243758421 43714186594823351037647)
                ·
                  rfl

theorem cell23_2298593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 9].length) (baseStart_2298593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2298593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2298593 prefixEnd_2298593 := by exact prefixLift 2298593
  have htrace : WordTrace (prefixWord ++ tailWord_2298593) baseStart_2298593 baseEnd_2298593 := by
    simpa [prefixWord, tailWord_2298593, baseEnd_2298593] using wordTrace_append hprefix tailTrace_2298593
  have hstable : (prefixWord ++ tailWord_2298593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2298593).length < 2 ^ (prefixWord ++ tailWord_2298593).sum := by decide
  have hdescent : baseEnd_2298593 < baseStart_2298593 := by decide
  rcases family_descends (prefixWord ++ tailWord_2298593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2298603 : List Nat := [1, 1, 1, 1, 2, 4, 1, 3, 3, 3, 3]
def baseStart_2298603 : Nat := 118140960795 + 2298603 * 2 ^ 59
def prefixEnd_2298603 : Nat := 4983230072969 + 3 ^ 40 * 2298603 * 2
def baseEnd_2298603 : Nat := 1180288172866775438891423

theorem tailTrace_2298603 : CollatzResearch.WordTrace tailWord_2298603 prefixEnd_2298603 1180288172866775438891423 := by
  unfold tailWord_2298603
  simp only [CollatzResearch.WordTrace]
  refine ⟨83836938891561375983404463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55891292594374250655602975 83836938891561375983404463)
  ·
    refine ⟨125755408337342063975106695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83836938891561375983404463 125755408337342063975106695)
    ·
      refine ⟨188633112506013095962660043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125755408337342063975106695 188633112506013095962660043)
      ·
        refine ⟨282949668759019643943990065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188633112506013095962660043 282949668759019643943990065)
        ·
          refine ⟨212212251569264732957992549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 282949668759019643943990065 212212251569264732957992549)
          ·
            refine ⟨39789797169237137429623603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 212212251569264732957992549 39789797169237137429623603)
            ·
              refine ⟨59684695753855706144435405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39789797169237137429623603 59684695753855706144435405)
              ·
                refine ⟨22381760907695889804163277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59684695753855706144435405 22381760907695889804163277)
                ·
                  refine ⟨8393160340385958676561229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22381760907695889804163277 8393160340385958676561229)
                  ·
                    refine ⟨3147435127644734503710461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8393160340385958676561229 3147435127644734503710461)
                    ·
                      refine ⟨1180288172866775438891423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3147435127644734503710461 1180288172866775438891423)
                      ·
                        rfl

theorem cell23_2298603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 3, 3, 3, 3].length) (baseStart_2298603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2298603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2298603 prefixEnd_2298603 := by exact prefixLift 2298603
  have htrace : WordTrace (prefixWord ++ tailWord_2298603) baseStart_2298603 baseEnd_2298603 := by
    simpa [prefixWord, tailWord_2298603, baseEnd_2298603] using wordTrace_append hprefix tailTrace_2298603
  have hstable : (prefixWord ++ tailWord_2298603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2298603).length < 2 ^ (prefixWord ++ tailWord_2298603).sum := by decide
  have hdescent : baseEnd_2298603 < baseStart_2298603 := by decide
  rcases family_descends (prefixWord ++ tailWord_2298603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2298621 : List Nat := [1, 4, 1, 1, 1, 1, 7, 2, 1, 2, 2]
def baseStart_2298621 : Nat := 118140960795 + 2298621 * 2 ^ 59
def prefixEnd_2298621 : Nat := 4983230072969 + 3 ^ 40 * 2298621 * 2
def baseEnd_2298621 : Nat := 1180297415518556368466341

theorem tailTrace_2298621 : CollatzResearch.WordTrace tailWord_2298621 prefixEnd_2298621 1180297415518556368466341 := by
  unfold tailWord_2298621
  simp only [CollatzResearch.WordTrace]
  refine ⟨83837595405496165057559717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55891730270330776705039811 83837595405496165057559717)
  ·
    refine ⟨15719549138530530948292447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83837595405496165057559717 15719549138530530948292447)
    ·
      refine ⟨23579323707795796422438671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15719549138530530948292447 23579323707795796422438671)
      ·
        refine ⟨35368985561693694633658007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23579323707795796422438671 35368985561693694633658007)
        ·
          refine ⟨53053478342540541950487011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35368985561693694633658007 53053478342540541950487011)
          ·
            refine ⟨79580217513810812925730517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53053478342540541950487011 79580217513810812925730517)
            ·
              refine ⟨1865161347979940927946809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 79580217513810812925730517 1865161347979940927946809)
              ·
                refine ⟨1398871010984955695960107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1865161347979940927946809 1398871010984955695960107)
                ·
                  refine ⟨2098306516477433543940161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1398871010984955695960107 2098306516477433543940161)
                  ·
                    refine ⟨1573729887358075157955121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2098306516477433543940161 1573729887358075157955121)
                    ·
                      refine ⟨1180297415518556368466341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1573729887358075157955121 1180297415518556368466341)
                      ·
                        rfl

theorem cell23_2298621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 7, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 7, 2, 1, 2, 2].length) (baseStart_2298621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2298621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2298621 prefixEnd_2298621 := by exact prefixLift 2298621
  have htrace : WordTrace (prefixWord ++ tailWord_2298621) baseStart_2298621 baseEnd_2298621 := by
    simpa [prefixWord, tailWord_2298621, baseEnd_2298621] using wordTrace_append hprefix tailTrace_2298621
  have hstable : (prefixWord ++ tailWord_2298621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2298621).length < 2 ^ (prefixWord ++ tailWord_2298621).sum := by decide
  have hdescent : baseEnd_2298621 < baseStart_2298621 := by decide
  rcases family_descends (prefixWord ++ tailWord_2298621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2298700 : List Nat := [2, 2, 1, 3, 3, 2, 1, 2, 7]
def baseStart_2298700 : Nat := 118140960795 + 2298700 * 2 ^ 59
def prefixEnd_2298700 : Nat := 4983230072969 + 3 ^ 40 * 2298700 * 2
def baseEnd_2298700 : Nat := 131148664498917951042053

theorem tailTrace_2298700 : CollatzResearch.WordTrace tailWord_2298700 prefixEnd_2298700 131148664498917951042053 := by
  unfold tailWord_2298700
  simp only [CollatzResearch.WordTrace]
  refine ⟨41920238386104980774842777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55893651181473307699790369 41920238386104980774842777)
  ·
    refine ⟨31440178789578735581132083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41920238386104980774842777 31440178789578735581132083)
    ·
      refine ⟨47160268184368103371698125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31440178789578735581132083 47160268184368103371698125)
      ·
        refine ⟨17685100569138038764386797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47160268184368103371698125 17685100569138038764386797)
        ·
          refine ⟨6631912713426764536645049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17685100569138038764386797 6631912713426764536645049)
          ·
            refine ⟨4973934535070073402483787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6631912713426764536645049 4973934535070073402483787)
            ·
              refine ⟨7460901802605110103725681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4973934535070073402483787 7460901802605110103725681)
              ·
                refine ⟨5595676351953832577794261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7460901802605110103725681 5595676351953832577794261)
                ·
                  refine ⟨131148664498917951042053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5595676351953832577794261 131148664498917951042053)
                  ·
                    rfl

theorem cell23_2298700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 2, 7].length) (baseStart_2298700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2298700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2298700 prefixEnd_2298700 := by exact prefixLift 2298700
  have htrace : WordTrace (prefixWord ++ tailWord_2298700) baseStart_2298700 baseEnd_2298700 := by
    simpa [prefixWord, tailWord_2298700, baseEnd_2298700] using wordTrace_append hprefix tailTrace_2298700
  have hstable : (prefixWord ++ tailWord_2298700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2298700).length < 2 ^ (prefixWord ++ tailWord_2298700).sum := by decide
  have hdescent : baseEnd_2298700 < baseStart_2298700 := by decide
  rcases family_descends (prefixWord ++ tailWord_2298700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2298807 : List Nat := [1, 1, 3, 1, 3, 1, 6, 1, 6]
def baseStart_2298807 : Nat := 118140960795 + 2298807 * 2 ^ 59
def prefixEnd_2298807 : Nat := 4983230072969 + 3 ^ 40 * 2298807 * 2
def baseEnd_2298807 : Nat := 131154769213365848971165

theorem tailTrace_2298807 : CollatzResearch.WordTrace tailWord_2298807 prefixEnd_2298807 131154769213365848971165 := by
  unfold tailWord_2298807
  simp only [CollatzResearch.WordTrace]
  refine ⟨83844379382822318823830675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55896252921881545882553783 83844379382822318823830675)
  ·
    refine ⟨125766569074233478235746013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83844379382822318823830675 125766569074233478235746013)
    ·
      refine ⟨47162463402837554338404755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 125766569074233478235746013 47162463402837554338404755)
      ·
        refine ⟨70743695104256331507607133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47162463402837554338404755 70743695104256331507607133)
        ·
          refine ⟨26528885664096124315352675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70743695104256331507607133 26528885664096124315352675)
          ·
            refine ⟨39793328496144186473029013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26528885664096124315352675 39793328496144186473029013)
            ·
              refine ⟨1865312273256758740923235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 39793328496144186473029013 1865312273256758740923235)
              ·
                refine ⟨2797968409885138111384853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1865312273256758740923235 2797968409885138111384853)
                ·
                  refine ⟨131154769213365848971165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2797968409885138111384853 131154769213365848971165)
                  ·
                    rfl

theorem cell23_2298807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 6, 1, 6].length) (baseStart_2298807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2298807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2298807 prefixEnd_2298807 := by exact prefixLift 2298807
  have htrace : WordTrace (prefixWord ++ tailWord_2298807) baseStart_2298807 baseEnd_2298807 := by
    simpa [prefixWord, tailWord_2298807, baseEnd_2298807] using wordTrace_append hprefix tailTrace_2298807
  have hstable : (prefixWord ++ tailWord_2298807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2298807).length < 2 ^ (prefixWord ++ tailWord_2298807).sum := by decide
  have hdescent : baseEnd_2298807 < baseStart_2298807 := by decide
  rcases family_descends (prefixWord ++ tailWord_2298807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2298851 : List Nat := [1, 1, 1, 6, 1, 1, 3, 4, 1, 1, 3]
def baseStart_2298851 : Nat := 118140960795 + 2298851 * 2 ^ 59
def prefixEnd_2298851 : Nat := 4983230072969 + 3 ^ 40 * 2298851 * 2
def baseEnd_2298851 : Nat := 1180415516069090468590283

theorem tailTrace_2298851 : CollatzResearch.WordTrace tailWord_2298851 prefixEnd_2298851 1180415516069090468590283 := by
  unfold tailWord_2298851
  simp only [CollatzResearch.WordTrace]
  refine ⟨83845984194662914338432407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55897322796441942892288271 83845984194662914338432407)
  ·
    refine ⟨125768976291994371507648611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83845984194662914338432407 125768976291994371507648611)
    ·
      refine ⟨188653464437991557261472917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125768976291994371507648611 188653464437991557261472917)
      ·
        refine ⟨8843131145530854246631543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 188653464437991557261472917 8843131145530854246631543)
        ·
          refine ⟨13264696718296281369947315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8843131145530854246631543 13264696718296281369947315)
          ·
            refine ⟨19897045077444422054920973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13264696718296281369947315 19897045077444422054920973)
            ·
              refine ⟨7461391904041658270595365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19897045077444422054920973 7461391904041658270595365)
              ·
                refine ⟨1399010982007810925736631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7461391904041658270595365 1399010982007810925736631)
                ·
                  refine ⟨2098516473011716388604947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1399010982007810925736631 2098516473011716388604947)
                  ·
                    refine ⟨3147774709517574582907421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2098516473011716388604947 3147774709517574582907421)
                    ·
                      refine ⟨1180415516069090468590283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3147774709517574582907421 1180415516069090468590283)
                      ·
                        rfl

theorem cell23_2298851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 4, 1, 1, 3].length) (baseStart_2298851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2298851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2298851 prefixEnd_2298851 := by exact prefixLift 2298851
  have htrace : WordTrace (prefixWord ++ tailWord_2298851) baseStart_2298851 baseEnd_2298851 := by
    simpa [prefixWord, tailWord_2298851, baseEnd_2298851] using wordTrace_append hprefix tailTrace_2298851
  have hstable : (prefixWord ++ tailWord_2298851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2298851).length < 2 ^ (prefixWord ++ tailWord_2298851).sum := by decide
  have hdescent : baseEnd_2298851 < baseStart_2298851 := by decide
  rcases family_descends (prefixWord ++ tailWord_2298851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2298887 : List Nat := [1, 1, 4, 3, 1, 1, 1, 4, 1, 2, 4]
def baseStart_2298887 : Nat := 118140960795 + 2298887 * 2 ^ 59
def prefixEnd_2298887 : Nat := 4983230072969 + 3 ^ 40 * 2298887 * 2
def baseEnd_2298887 : Nat := 1180434001372652327740117

theorem tailTrace_2298887 : CollatzResearch.WordTrace tailWord_2298887 prefixEnd_2298887 1180434001372652327740117 := by
  unfold tailWord_2298887
  simp only [CollatzResearch.WordTrace]
  refine ⟨83847297222532492486742915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55898198148354994991161943 83847297222532492486742915)
  ·
    refine ⟨125770945833798738730114373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83847297222532492486742915 125770945833798738730114373)
    ·
      refine ⟨23582052343837263511896445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 125770945833798738730114373 23582052343837263511896445)
      ·
        refine ⟨8843269628938973816961167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23582052343837263511896445 8843269628938973816961167)
        ·
          refine ⟨13264904443408460725441751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8843269628938973816961167 13264904443408460725441751)
          ·
            refine ⟨19897356665112691088162627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13264904443408460725441751 19897356665112691088162627)
            ·
              refine ⟨29846034997669036632243941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19897356665112691088162627 29846034997669036632243941)
              ·
                refine ⟨5596131562062944368545739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29846034997669036632243941 5596131562062944368545739)
                ·
                  refine ⟨8394197343094416552818609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5596131562062944368545739 8394197343094416552818609)
                  ·
                    refine ⟨6295648007320812414613957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8394197343094416552818609 6295648007320812414613957)
                    ·
                      refine ⟨1180434001372652327740117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6295648007320812414613957 1180434001372652327740117)
                      ·
                        rfl

theorem cell23_2298887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_2298887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2298887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2298887 prefixEnd_2298887 := by exact prefixLift 2298887
  have htrace : WordTrace (prefixWord ++ tailWord_2298887) baseStart_2298887 baseEnd_2298887 := by
    simpa [prefixWord, tailWord_2298887, baseEnd_2298887] using wordTrace_append hprefix tailTrace_2298887
  have hstable : (prefixWord ++ tailWord_2298887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2298887).length < 2 ^ (prefixWord ++ tailWord_2298887).sum := by decide
  have hdescent : baseEnd_2298887 < baseStart_2298887 := by decide
  rcases family_descends (prefixWord ++ tailWord_2298887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2298891 : List Nat := [1, 1, 1, 1, 6, 4, 2, 1, 1, 1, 4]
def baseStart_2298891 : Nat := 118140960795 + 2298891 * 2 ^ 59
def prefixEnd_2298891 : Nat := 4983230072969 + 3 ^ 40 * 2298891 * 2
def baseEnd_2298891 : Nat := 1180436055295270312090099

theorem tailTrace_2298891 : CollatzResearch.WordTrace tailWord_2298891 prefixEnd_2298891 1180436055295270312090099 := by
  unfold tailWord_2298891
  simp only [CollatzResearch.WordTrace]
  refine ⟨83847443114518001169888527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55898295409678667446592351 83847443114518001169888527)
  ·
    refine ⟨125771164671777001754832791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83847443114518001169888527 125771164671777001754832791)
    ·
      refine ⟨188656747007665502632249187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125771164671777001754832791 188656747007665502632249187)
      ·
        refine ⟨282985120511498253948373781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188656747007665502632249187 282985120511498253948373781)
        ·
          refine ⟨13264927523976480653830021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 282985120511498253948373781 13264927523976480653830021)
          ·
            refine ⟨2487173910745590122593129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13264927523976480653830021 2487173910745590122593129)
            ·
              refine ⟨1865380433059192591944847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2487173910745590122593129 1865380433059192591944847)
              ·
                refine ⟨2798070649588788887917271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1865380433059192591944847 2798070649588788887917271)
                ·
                  refine ⟨4197105974383183331875907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2798070649588788887917271 4197105974383183331875907)
                  ·
                    refine ⟨6295658961574774997813861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4197105974383183331875907 6295658961574774997813861)
                    ·
                      refine ⟨1180436055295270312090099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6295658961574774997813861 1180436055295270312090099)
                      ·
                        rfl

theorem cell23_2298891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 2, 1, 1, 1, 4].length) (baseStart_2298891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2298891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2298891 prefixEnd_2298891 := by exact prefixLift 2298891
  have htrace : WordTrace (prefixWord ++ tailWord_2298891) baseStart_2298891 baseEnd_2298891 := by
    simpa [prefixWord, tailWord_2298891, baseEnd_2298891] using wordTrace_append hprefix tailTrace_2298891
  have hstable : (prefixWord ++ tailWord_2298891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2298891).length < 2 ^ (prefixWord ++ tailWord_2298891).sum := by decide
  have hdescent : baseEnd_2298891 < baseStart_2298891 := by decide
  rcases family_descends (prefixWord ++ tailWord_2298891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2298901 : List Nat := [1, 3, 2, 1, 4, 3, 1, 2, 2, 4]
def baseStart_2298901 : Nat := 118140960795 + 2298901 * 2 ^ 59
def prefixEnd_2298901 : Nat := 4983230072969 + 3 ^ 40 * 2298901 * 2
def baseEnd_2298901 : Nat := 393480396700605090988351

theorem tailTrace_2298901 : CollatzResearch.WordTrace tailWord_2298901 prefixEnd_2298901 393480396700605090988351 := by
  unfold tailWord_2298901
  simp only [CollatzResearch.WordTrace]
  refine ⟨83847807844481772877752557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55898538562987848585168371 83847807844481772877752557)
  ·
    refine ⟨31442927941680664829157209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83847807844481772877752557 31442927941680664829157209)
    ·
      refine ⟨23582195956260498621867907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31442927941680664829157209 23582195956260498621867907)
      ·
        refine ⟨35373293934390747932801861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23582195956260498621867907 35373293934390747932801861)
        ·
          refine ⟨6632492612698265237400349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35373293934390747932801861 6632492612698265237400349)
          ·
            refine ⟨2487184729761849464025131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6632492612698265237400349 2487184729761849464025131)
            ·
              refine ⟨3730777094642774196037697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2487184729761849464025131 3730777094642774196037697)
              ·
                refine ⟨2798082820982080647028273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3730777094642774196037697 2798082820982080647028273)
                ·
                  refine ⟨2098562115736560485271205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2798082820982080647028273 2098562115736560485271205)
                  ·
                    refine ⟨393480396700605090988351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2098562115736560485271205 393480396700605090988351)
                    ·
                      rfl

theorem cell23_2298901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 1, 2, 2, 4].length) (baseStart_2298901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2298901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2298901 prefixEnd_2298901 := by exact prefixLift 2298901
  have htrace : WordTrace (prefixWord ++ tailWord_2298901) baseStart_2298901 baseEnd_2298901 := by
    simpa [prefixWord, tailWord_2298901, baseEnd_2298901] using wordTrace_append hprefix tailTrace_2298901
  have hstable : (prefixWord ++ tailWord_2298901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2298901).length < 2 ^ (prefixWord ++ tailWord_2298901).sum := by decide
  have hdescent : baseEnd_2298901 < baseStart_2298901 := by decide
  rcases family_descends (prefixWord ++ tailWord_2298901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2298908 : List Nat := [2, 2, 3, 1, 4, 1, 2, 1, 3, 2, 2]
def baseStart_2298908 : Nat := 118140960795 + 2298908 * 2 ^ 59
def prefixEnd_2298908 : Nat := 4983230072969 + 3 ^ 40 * 2298908 * 2
def baseEnd_2298908 : Nat := 1180444784466396745577521

theorem tailTrace_2298908 : CollatzResearch.WordTrace tailWord_2298908 prefixEnd_2298908 1180444784466396745577521 := by
  unfold tailWord_2298908
  simp only [CollatzResearch.WordTrace]
  refine ⟨41924031577728206536628689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55898708770304275382171585 41924031577728206536628689)
  ·
    refine ⟨31443023683296154902471517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41924031577728206536628689 31443023683296154902471517)
    ·
      refine ⟨11791133881236058088426819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31443023683296154902471517 11791133881236058088426819)
      ·
        refine ⟨17686700821854087132640229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11791133881236058088426819 17686700821854087132640229)
        ·
          refine ⟨3316256404097641337370043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17686700821854087132640229 3316256404097641337370043)
          ·
            refine ⟨4974384606146462006055065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3316256404097641337370043 4974384606146462006055065)
            ·
              refine ⟨3730788454609846504541299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4974384606146462006055065 3730788454609846504541299)
              ·
                refine ⟨5596182681914769756811949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3730788454609846504541299 5596182681914769756811949)
                ·
                  refine ⟨2098568505718038658804481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5596182681914769756811949 2098568505718038658804481)
                  ·
                    refine ⟨1573926379288528994103361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2098568505718038658804481 1573926379288528994103361)
                    ·
                      refine ⟨1180444784466396745577521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1573926379288528994103361 1180444784466396745577521)
                      ·
                        rfl

theorem cell23_2298908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 2, 1, 3, 2, 2].length) (baseStart_2298908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2298908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2298908 prefixEnd_2298908 := by exact prefixLift 2298908
  have htrace : WordTrace (prefixWord ++ tailWord_2298908) baseStart_2298908 baseEnd_2298908 := by
    simpa [prefixWord, tailWord_2298908, baseEnd_2298908] using wordTrace_append hprefix tailTrace_2298908
  have hstable : (prefixWord ++ tailWord_2298908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2298908).length < 2 ^ (prefixWord ++ tailWord_2298908).sum := by decide
  have hdescent : baseEnd_2298908 < baseStart_2298908 := by decide
  rcases family_descends (prefixWord ++ tailWord_2298908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2298937 : List Nat := [1, 2, 1, 5, 2, 1, 1, 1, 2, 2, 5]
def baseStart_2298937 : Nat := 118140960795 + 2298937 * 2 ^ 59
def prefixEnd_2298937 : Nat := 4983230072969 + 3 ^ 40 * 2298937 * 2
def baseEnd_2298937 : Nat := 1180459675405377132114887

theorem tailTrace_2298937 : CollatzResearch.WordTrace tailWord_2298937 prefixEnd_2298937 1180459675405377132114887 := by
  unfold tailWord_2298937
  simp only [CollatzResearch.WordTrace]
  refine ⟨83849120872351351026063065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55899413914900900684042043 83849120872351351026063065)
  ·
    refine ⟨62886840654263513269547299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83849120872351351026063065 62886840654263513269547299)
    ·
      refine ⟨94330260981395269904320949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62886840654263513269547299 94330260981395269904320949)
      ·
        refine ⟨8843461967005806553530089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 94330260981395269904320949 8843461967005806553530089)
        ·
          refine ⟨6632596475254354915147567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8843461967005806553530089 6632596475254354915147567)
          ·
            refine ⟨9948894712881532372721351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6632596475254354915147567 9948894712881532372721351)
            ·
              refine ⟨14923342069322298559082027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9948894712881532372721351 14923342069322298559082027)
              ·
                refine ⟨22385013103983447838623041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14923342069322298559082027 22385013103983447838623041)
                ·
                  refine ⟨16788759827987585878967281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22385013103983447838623041 16788759827987585878967281)
                  ·
                    refine ⟨12591569870990689409225461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16788759827987585878967281 12591569870990689409225461)
                    ·
                      refine ⟨1180459675405377132114887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12591569870990689409225461 1180459675405377132114887)
                      ·
                        rfl

theorem cell23_2298937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_2298937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2298937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2298937 prefixEnd_2298937 := by exact prefixLift 2298937
  have htrace : WordTrace (prefixWord ++ tailWord_2298937) baseStart_2298937 baseEnd_2298937 := by
    simpa [prefixWord, tailWord_2298937, baseEnd_2298937] using wordTrace_append hprefix tailTrace_2298937
  have hstable : (prefixWord ++ tailWord_2298937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2298937).length < 2 ^ (prefixWord ++ tailWord_2298937).sum := by decide
  have hdescent : baseEnd_2298937 < baseStart_2298937 := by decide
  rcases family_descends (prefixWord ++ tailWord_2298937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2298942 : List Nat := [4, 2, 1, 3, 1, 3, 1, 3, 1, 2, 2]
def baseStart_2298942 : Nat := 118140960795 + 2298942 * 2 ^ 59
def prefixEnd_2298942 : Nat := 4983230072969 + 3 ^ 40 * 2298942 * 2
def baseEnd_2298942 : Nat := 1180462242808649612552365

theorem tailTrace_2298942 : CollatzResearch.WordTrace tailWord_2298942 prefixEnd_2298942 1180462242808649612552365 := by
  unfold tailWord_2298942
  simp only [CollatzResearch.WordTrace]
  refine ⟨10481162904666654609999385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55899535491555491253330053 10481162904666654609999385)
  ·
    refine ⟨7860872178499990957499539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10481162904666654609999385 7860872178499990957499539)
    ·
      refine ⟨11791308267749986436249309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7860872178499990957499539 11791308267749986436249309)
      ·
        refine ⟨4421740600406244913593491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11791308267749986436249309 4421740600406244913593491)
        ·
          refine ⟨6632610900609367370390237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4421740600406244913593491 6632610900609367370390237)
          ·
            refine ⟨2487229087728512763896339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6632610900609367370390237 2487229087728512763896339)
            ·
              refine ⟨3730843631592769145844509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2487229087728512763896339 3730843631592769145844509)
              ·
                refine ⟨1399066361847288429691691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3730843631592769145844509 1399066361847288429691691)
                ·
                  refine ⟨2098599542770932644537537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1399066361847288429691691 2098599542770932644537537)
                  ·
                    refine ⟨1573949657078199483403153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2098599542770932644537537 1573949657078199483403153)
                    ·
                      refine ⟨1180462242808649612552365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1573949657078199483403153 1180462242808649612552365)
                      ·
                        rfl

theorem cell23_2298942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 1, 3, 1, 2, 2].length) (baseStart_2298942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2298942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2298942 prefixEnd_2298942 := by exact prefixLift 2298942
  have htrace : WordTrace (prefixWord ++ tailWord_2298942) baseStart_2298942 baseEnd_2298942 := by
    simpa [prefixWord, tailWord_2298942, baseEnd_2298942] using wordTrace_append hprefix tailTrace_2298942
  have hstable : (prefixWord ++ tailWord_2298942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2298942).length < 2 ^ (prefixWord ++ tailWord_2298942).sum := by decide
  have hdescent : baseEnd_2298942 < baseStart_2298942 := by decide
  rcases family_descends (prefixWord ++ tailWord_2298942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2298951 : List Nat := [1, 1, 4, 1, 3, 2, 2, 3, 1, 3, 2]
def baseStart_2298951 : Nat := 118140960795 + 2298951 * 2 ^ 59
def prefixEnd_2298951 : Nat := 4983230072969 + 3 ^ 40 * 2298951 * 2
def baseEnd_2298951 : Nat := 1180466864134540077339823

theorem tailTrace_2298951 : CollatzResearch.WordTrace tailWord_2298951 prefixEnd_2298951 1180466864134540077339823 := by
  unfold tailWord_2298951
  simp only [CollatzResearch.WordTrace]
  refine ⟨83849631494300631417072707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55899754329533754278048471 83849631494300631417072707)
  ·
    refine ⟨125774447241450947125609061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83849631494300631417072707 125774447241450947125609061)
    ·
      refine ⟨23582708857772052586051699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 125774447241450947125609061 23582708857772052586051699)
      ·
        refine ⟨35374063286658078879077549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23582708857772052586051699 35374063286658078879077549)
        ·
          refine ⟨13265273732496779579654081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35374063286658078879077549 13265273732496779579654081)
          ·
            refine ⟨9948955299372584684740561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13265273732496779579654081 9948955299372584684740561)
            ·
              refine ⟨7461716474529438513555421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9948955299372584684740561 7461716474529438513555421)
              ·
                refine ⟨2798143677948539442583283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7461716474529438513555421 2798143677948539442583283)
                ·
                  refine ⟨4197215516922809163874925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2798143677948539442583283 4197215516922809163874925)
                  ·
                    refine ⟨1573955818846053436453097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4197215516922809163874925 1573955818846053436453097)
                    ·
                      refine ⟨1180466864134540077339823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1573955818846053436453097 1180466864134540077339823)
                      ·
                        rfl

theorem cell23_2298951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 3, 1, 3, 2].length) (baseStart_2298951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2298951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2298951 prefixEnd_2298951 := by exact prefixLift 2298951
  have htrace : WordTrace (prefixWord ++ tailWord_2298951) baseStart_2298951 baseEnd_2298951 := by
    simpa [prefixWord, tailWord_2298951, baseEnd_2298951] using wordTrace_append hprefix tailTrace_2298951
  have hstable : (prefixWord ++ tailWord_2298951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2298951).length < 2 ^ (prefixWord ++ tailWord_2298951).sum := by decide
  have hdescent : baseEnd_2298951 < baseStart_2298951 := by decide
  rcases family_descends (prefixWord ++ tailWord_2298951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2298967 : List Nat := [1, 1, 3, 2, 2, 1, 1, 3, 2, 4, 3]
def baseStart_2298967 : Nat := 118140960795 + 2298967 * 2 ^ 59
def prefixEnd_2298967 : Nat := 4983230072969 + 3 ^ 40 * 2298967 * 2
def baseEnd_2298967 : Nat := 1180475079825012014739749

theorem tailTrace_2298967 : CollatzResearch.WordTrace tailWord_2298967 prefixEnd_2298967 1180475079825012014739749 := by
  unfold tailWord_2298967
  simp only [CollatzResearch.WordTrace]
  refine ⟨83850215062242666149655155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55900143374828444099770103 83850215062242666149655155)
  ·
    refine ⟨125775322593363999224482733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83850215062242666149655155 125775322593363999224482733)
    ·
      refine ⟨47165745972511499709181025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 125775322593363999224482733 47165745972511499709181025)
      ·
        refine ⟨35374309479383624781885769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47165745972511499709181025 35374309479383624781885769)
        ·
          refine ⟨26530732109537718586414327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35374309479383624781885769 26530732109537718586414327)
          ·
            refine ⟨39796098164306577879621491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26530732109537718586414327 39796098164306577879621491)
            ·
              refine ⟨59694147246459866819432237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39796098164306577879621491 59694147246459866819432237)
              ·
                refine ⟨22385305217422450057287089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59694147246459866819432237 22385305217422450057287089)
                ·
                  refine ⟨16788978913066837542965317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22385305217422450057287089 16788978913066837542965317)
                  ·
                    refine ⟨3147933546200032039305997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16788978913066837542965317 3147933546200032039305997)
                    ·
                      refine ⟨1180475079825012014739749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3147933546200032039305997 1180475079825012014739749)
                      ·
                        rfl

theorem cell23_2298967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 3, 2, 4, 3].length) (baseStart_2298967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2298967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2298967 prefixEnd_2298967 := by exact prefixLift 2298967
  have htrace : WordTrace (prefixWord ++ tailWord_2298967) baseStart_2298967 baseEnd_2298967 := by
    simpa [prefixWord, tailWord_2298967, baseEnd_2298967] using wordTrace_append hprefix tailTrace_2298967
  have hstable : (prefixWord ++ tailWord_2298967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2298967).length < 2 ^ (prefixWord ++ tailWord_2298967).sum := by decide
  have hdescent : baseEnd_2298967 < baseStart_2298967 := by decide
  rcases family_descends (prefixWord ++ tailWord_2298967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2298977 : List Nat := [1, 2, 3, 1, 1, 2, 2, 3, 2, 2, 4]
def baseStart_2298977 : Nat := 118140960795 + 2298977 * 2 ^ 59
def prefixEnd_2298977 : Nat := 4983230072969 + 3 ^ 40 * 2298977 * 2
def baseEnd_2298977 : Nat := 1180480214631556975614703

theorem tailTrace_2298977 : CollatzResearch.WordTrace tailWord_2298977 prefixEnd_2298977 1180480214631556975614703 := by
  unfold tailWord_2298977
  simp only [CollatzResearch.WordTrace]
  refine ⟨83850579792206437857519185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55900386528137625238346123 83850579792206437857519185)
  ·
    refine ⟨62887934844154828393139389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83850579792206437857519185 62887934844154828393139389)
    ·
      refine ⟨23582975566558060647427271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62887934844154828393139389 23582975566558060647427271)
      ·
        refine ⟨35374463349837090971140907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23582975566558060647427271 35374463349837090971140907)
        ·
          refine ⟨53061695024755636456711361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35374463349837090971140907 53061695024755636456711361)
          ·
            refine ⟨39796271268566727342533521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53061695024755636456711361 39796271268566727342533521)
            ·
              refine ⟨29847203451425045506900141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39796271268566727342533521 29847203451425045506900141)
              ·
                refine ⟨11192701294284392065087553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29847203451425045506900141 11192701294284392065087553)
                ·
                  refine ⟨8394525970713294048815665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11192701294284392065087553 8394525970713294048815665)
                  ·
                    refine ⟨6295894478034970536611749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8394525970713294048815665 6295894478034970536611749)
                    ·
                      refine ⟨1180480214631556975614703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6295894478034970536611749 1180480214631556975614703)
                      ·
                        rfl

theorem cell23_2298977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 3, 2, 2, 4].length) (baseStart_2298977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2298977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2298977 prefixEnd_2298977 := by exact prefixLift 2298977
  have htrace : WordTrace (prefixWord ++ tailWord_2298977) baseStart_2298977 baseEnd_2298977 := by
    simpa [prefixWord, tailWord_2298977, baseEnd_2298977] using wordTrace_append hprefix tailTrace_2298977
  have hstable : (prefixWord ++ tailWord_2298977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2298977).length < 2 ^ (prefixWord ++ tailWord_2298977).sum := by decide
  have hdescent : baseEnd_2298977 < baseStart_2298977 := by decide
  rcases family_descends (prefixWord ++ tailWord_2298977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2299004 : List Nat := [2, 2, 2, 1, 1, 3, 2, 5, 5]
def baseStart_2299004 : Nat := 118140960795 + 2299004 * 2 ^ 59
def prefixEnd_2299004 : Nat := 4983230072969 + 3 ^ 40 * 2299004 * 2
def baseEnd_2299004 : Nat := 131166008734358707775231

theorem tailTrace_2299004 : CollatzResearch.WordTrace tailWord_2299004 prefixEnd_2299004 131166008734358707775231 := by
  unfold tailWord_2299004
  simp only [CollatzResearch.WordTrace]
  refine ⟨41925782281554310734376033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55901043042072414312501377 41925782281554310734376033)
  ·
    refine ⟨31444336711165733050782025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41925782281554310734376033 31444336711165733050782025)
    ·
      refine ⟨23583252533374299788086519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31444336711165733050782025 23583252533374299788086519)
      ·
        refine ⟨35374878800061449682129779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23583252533374299788086519 35374878800061449682129779)
        ·
          refine ⟨53062318200092174523194669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35374878800061449682129779 53062318200092174523194669)
          ·
            refine ⟨19898369325034565446198001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53062318200092174523194669 19898369325034565446198001)
            ·
              refine ⟨14923776993775924084648501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19898369325034565446198001 14923776993775924084648501)
              ·
                refine ⟨1399104093166492882935797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14923776993775924084648501 1399104093166492882935797)
                ·
                  refine ⟨131166008734358707775231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1399104093166492882935797 131166008734358707775231)
                  ·
                    rfl

theorem cell23_2299004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 5, 5].length) (baseStart_2299004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2299004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2299004 prefixEnd_2299004 := by exact prefixLift 2299004
  have htrace : WordTrace (prefixWord ++ tailWord_2299004) baseStart_2299004 baseEnd_2299004 := by
    simpa [prefixWord, tailWord_2299004, baseEnd_2299004] using wordTrace_append hprefix tailTrace_2299004
  have hstable : (prefixWord ++ tailWord_2299004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2299004).length < 2 ^ (prefixWord ++ tailWord_2299004).sum := by decide
  have hdescent : baseEnd_2299004 < baseStart_2299004 := by decide
  rcases family_descends (prefixWord ++ tailWord_2299004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2299027 : List Nat := [1, 1, 1, 2, 1, 2, 6, 1, 1, 2, 5]
def baseStart_2299027 : Nat := 118140960795 + 2299027 * 2 ^ 59
def prefixEnd_2299027 : Nat := 4983230072969 + 3 ^ 40 * 2299027 * 2
def baseEnd_2299027 : Nat := 1180505888664281779989473

theorem tailTrace_2299027 : CollatzResearch.WordTrace tailWord_2299027 prefixEnd_2299027 1180505888664281779989473 := by
  unfold tailWord_2299027
  simp only [CollatzResearch.WordTrace]
  refine ⟨83852403442025296396839335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55901602294683530931226223 83852403442025296396839335)
  ·
    refine ⟨125778605163037944595259003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83852403442025296396839335 125778605163037944595259003)
    ·
      refine ⟨188667907744556916892888505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125778605163037944595259003 188667907744556916892888505)
      ·
        refine ⟨141500930808417687669666379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 188667907744556916892888505 141500930808417687669666379)
        ·
          refine ⟨212251396212626531504499569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141500930808417687669666379 212251396212626531504499569)
          ·
            refine ⟨159188547159469898628374677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 212251396212626531504499569 159188547159469898628374677)
            ·
              refine ⟨7461963148100151498205063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 159188547159469898628374677 7461963148100151498205063)
              ·
                refine ⟨11192944722150227247307595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7461963148100151498205063 11192944722150227247307595)
                ·
                  refine ⟨16789417083225340870961393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11192944722150227247307595 16789417083225340870961393)
                  ·
                    refine ⟨12592062812419005653221045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16789417083225340870961393 12592062812419005653221045)
                    ·
                      refine ⟨1180505888664281779989473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12592062812419005653221045 1180505888664281779989473)
                      ·
                        rfl

theorem cell23_2299027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 1, 1, 2, 5].length) (baseStart_2299027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2299027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2299027 prefixEnd_2299027 := by exact prefixLift 2299027
  have htrace : WordTrace (prefixWord ++ tailWord_2299027) baseStart_2299027 baseEnd_2299027 := by
    simpa [prefixWord, tailWord_2299027, baseEnd_2299027] using wordTrace_append hprefix tailTrace_2299027
  have hstable : (prefixWord ++ tailWord_2299027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2299027).length < 2 ^ (prefixWord ++ tailWord_2299027).sum := by decide
  have hdescent : baseEnd_2299027 < baseStart_2299027 := by decide
  rcases family_descends (prefixWord ++ tailWord_2299027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2299097 : List Nat := [1, 2, 1, 2, 3, 1, 1, 1, 3, 2, 6]
def baseStart_2299097 : Nat := 118140960795 + 2299097 * 2 ^ 59
def prefixEnd_2299097 : Nat := 4983230072969 + 3 ^ 40 * 2299097 * 2
def baseEnd_2299097 : Nat := 1180541832310096506114151

theorem tailTrace_2299097 : CollatzResearch.WordTrace tailWord_2299097 prefixEnd_2299097 1180541832310096506114151 := by
  unfold tailWord_2299097
  simp only [CollatzResearch.WordTrace]
  refine ⟨83854956551771698351887545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55903304367847798901258363 83854956551771698351887545)
  ·
    refine ⟨62891217413828773763915659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83854956551771698351887545 62891217413828773763915659)
    ·
      refine ⟨94336826120743160645873489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62891217413828773763915659 94336826120743160645873489)
      ·
        refine ⟨70752619590557370484405117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94336826120743160645873489 70752619590557370484405117)
        ·
          refine ⟨26532232346459013931651919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70752619590557370484405117 26532232346459013931651919)
          ·
            refine ⟨39798348519688520897477879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26532232346459013931651919 39798348519688520897477879)
            ·
              refine ⟨59697522779532781346216819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39798348519688520897477879 59697522779532781346216819)
              ·
                refine ⟨89546284169299172019325229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59697522779532781346216819 89546284169299172019325229)
                ·
                  refine ⟨33579856563487189507246961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 89546284169299172019325229 33579856563487189507246961)
                  ·
                    refine ⟨25184892422615392130435221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33579856563487189507246961 25184892422615392130435221)
                    ·
                      refine ⟨1180541832310096506114151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 25184892422615392130435221 1180541832310096506114151)
                      ·
                        rfl

theorem cell23_2299097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 3, 2, 6].length) (baseStart_2299097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2299097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2299097 prefixEnd_2299097 := by exact prefixLift 2299097
  have htrace : WordTrace (prefixWord ++ tailWord_2299097) baseStart_2299097 baseEnd_2299097 := by
    simpa [prefixWord, tailWord_2299097, baseEnd_2299097] using wordTrace_append hprefix tailTrace_2299097
  have hstable : (prefixWord ++ tailWord_2299097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2299097).length < 2 ^ (prefixWord ++ tailWord_2299097).sum := by decide
  have hdescent : baseEnd_2299097 < baseStart_2299097 := by decide
  rcases family_descends (prefixWord ++ tailWord_2299097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2299164 : List Nat := [2, 2, 3, 1, 1, 1, 2, 2, 3, 1, 5]
def baseStart_2299164 : Nat := 118140960795 + 2299164 * 2 ^ 59
def prefixEnd_2299164 : Nat := 4983230072969 + 3 ^ 40 * 2299164 * 2
def baseEnd_2299164 : Nat := 1180576235513947743976343

theorem tailTrace_2299164 : CollatzResearch.WordTrace tailWord_2299164 prefixEnd_2299164 1180576235513947743976343 := by
  unfold tailWord_2299164
  simp only [CollatzResearch.WordTrace]
  refine ⟨41928700121264484397288273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55904933495019312529717697 41928700121264484397288273)
  ·
    refine ⟨31446525090948363297966205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41928700121264484397288273 31446525090948363297966205)
    ·
      refine ⟨11792446909105636236737327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31446525090948363297966205 11792446909105636236737327)
      ·
        refine ⟨17688670363658454355105991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11792446909105636236737327 17688670363658454355105991)
        ·
          refine ⟨26533005545487681532658987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17688670363658454355105991 26533005545487681532658987)
          ·
            refine ⟨39799508318231522298988481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26533005545487681532658987 39799508318231522298988481)
            ·
              refine ⟨29849631238673641724241361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39799508318231522298988481 29849631238673641724241361)
              ·
                refine ⟨22387223429005231293181021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29849631238673641724241361 22387223429005231293181021)
                ·
                  refine ⟨8395208785876961734942883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22387223429005231293181021 8395208785876961734942883)
                  ·
                    refine ⟨12592813178815442602414325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8395208785876961734942883 12592813178815442602414325)
                    ·
                      refine ⟨1180576235513947743976343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12592813178815442602414325 1180576235513947743976343)
                      ·
                        rfl

theorem cell23_2299164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 2, 3, 1, 5].length) (baseStart_2299164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2299164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2299164 prefixEnd_2299164 := by exact prefixLift 2299164
  have htrace : WordTrace (prefixWord ++ tailWord_2299164) baseStart_2299164 baseEnd_2299164 := by
    simpa [prefixWord, tailWord_2299164, baseEnd_2299164] using wordTrace_append hprefix tailTrace_2299164
  have hstable : (prefixWord ++ tailWord_2299164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2299164).length < 2 ^ (prefixWord ++ tailWord_2299164).sum := by decide
  have hdescent : baseEnd_2299164 < baseStart_2299164 := by decide
  rcases family_descends (prefixWord ++ tailWord_2299164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2299165 : List Nat := [1, 4, 2, 3, 1, 2, 2, 1, 2, 3, 2]
def baseStart_2299165 : Nat := 118140960795 + 2299165 * 2 ^ 59
def prefixEnd_2299165 : Nat := 4983230072969 + 3 ^ 40 * 2299165 * 2
def baseEnd_2299165 : Nat := 1180576748994602240063839

theorem tailTrace_2299165 : CollatzResearch.WordTrace tailWord_2299165 prefixEnd_2299165 1180576748994602240063839 := by
  unfold tailWord_2299165
  simp only [CollatzResearch.WordTrace]
  refine ⟨83857436715525345965362949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55904957810350230643575299 83857436715525345965362949)
  ·
    refine ⟨15723269384161002368505553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83857436715525345965362949 15723269384161002368505553)
    ·
      refine ⟨11792452038120751776379165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15723269384161002368505553 11792452038120751776379165)
      ·
        refine ⟨4422169514295281916142187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11792452038120751776379165 4422169514295281916142187)
        ·
          refine ⟨6633254271442922874213281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4422169514295281916142187 6633254271442922874213281)
          ·
            refine ⟨4974940703582192155659961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6633254271442922874213281 4974940703582192155659961)
            ·
              refine ⟨3731205527686644116744971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4974940703582192155659961 3731205527686644116744971)
              ·
                refine ⟨5596808291529966175117457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3731205527686644116744971 5596808291529966175117457)
                ·
                  refine ⟨4197606218647474631338093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5596808291529966175117457 4197606218647474631338093)
                  ·
                    refine ⟨1574102331992802986751785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4197606218647474631338093 1574102331992802986751785)
                    ·
                      refine ⟨1180576748994602240063839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1574102331992802986751785 1180576748994602240063839)
                      ·
                        rfl

theorem cell23_2299165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 2, 1, 2, 3, 2].length) (baseStart_2299165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2299165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2299165 prefixEnd_2299165 := by exact prefixLift 2299165
  have htrace : WordTrace (prefixWord ++ tailWord_2299165) baseStart_2299165 baseEnd_2299165 := by
    simpa [prefixWord, tailWord_2299165, baseEnd_2299165] using wordTrace_append hprefix tailTrace_2299165
  have hstable : (prefixWord ++ tailWord_2299165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2299165).length < 2 ^ (prefixWord ++ tailWord_2299165).sum := by decide
  have hdescent : baseEnd_2299165 < baseStart_2299165 := by decide
  rcases family_descends (prefixWord ++ tailWord_2299165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2299201 : List Nat := [1, 2, 5, 2, 1, 1, 3, 8]
def baseStart_2299201 : Nat := 118140960795 + 2299201 * 2 ^ 59
def prefixEnd_2299201 : Nat := 4983230072969 + 3 ^ 40 * 2299201 * 2
def baseEnd_2299201 : Nat := 43725749418450522193099

theorem tailTrace_2299201 : CollatzResearch.WordTrace tailWord_2299201 prefixEnd_2299201 43725749418450522193099 := by
  unfold tailWord_2299201
  simp only [CollatzResearch.WordTrace]
  refine ⟨83858749743394924113673457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55905833162263282742448971 83858749743394924113673457)
  ·
    refine ⟨62894062307546193085255093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83858749743394924113673457 62894062307546193085255093)
    ·
      refine ⟨5896318341332455601742665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 62894062307546193085255093 5896318341332455601742665)
      ·
        refine ⟨4422238755999341701306999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5896318341332455601742665 4422238755999341701306999)
        ·
          refine ⟨6633358133999012551960499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4422238755999341701306999 6633358133999012551960499)
          ·
            refine ⟨9950037200998518827940749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6633358133999012551960499 9950037200998518827940749)
            ·
              refine ⟨3731263950374444560477781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9950037200998518827940749 3731263950374444560477781)
              ·
                refine ⟨43725749418450522193099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3731263950374444560477781 43725749418450522193099)
                ·
                  rfl

theorem cell23_2299201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 3, 8].length) (baseStart_2299201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2299201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2299201 prefixEnd_2299201 := by exact prefixLift 2299201
  have htrace : WordTrace (prefixWord ++ tailWord_2299201) baseStart_2299201 baseEnd_2299201 := by
    simpa [prefixWord, tailWord_2299201, baseEnd_2299201] using wordTrace_append hprefix tailTrace_2299201
  have hstable : (prefixWord ++ tailWord_2299201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2299201).length < 2 ^ (prefixWord ++ tailWord_2299201).sum := by decide
  have hdescent : baseEnd_2299201 < baseStart_2299201 := by decide
  rcases family_descends (prefixWord ++ tailWord_2299201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2299214 : List Nat := [4, 1, 1, 1, 1, 1, 3, 2, 2, 7]
def baseStart_2299214 : Nat := 118140960795 + 2299214 * 2 ^ 59
def prefixEnd_2299214 : Nat := 4983230072969 + 3 ^ 40 * 2299214 * 2
def baseEnd_2299214 : Nat := 393533969848890849450371

theorem tailTrace_2299214 : CollatzResearch.WordTrace tailWord_2299214 prefixEnd_2299214 393533969848890849450371 := by
  unfold tailWord_2299214
  simp only [CollatzResearch.WordTrace]
  refine ⟨10482402986543478416737087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55906149261565218222597797 10482402986543478416737087)
  ·
    refine ⟨15723604479815217625105631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10482402986543478416737087 15723604479815217625105631)
    ·
      refine ⟨23585406719722826437658447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15723604479815217625105631 23585406719722826437658447)
      ·
        refine ⟨35378110079584239656487671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23585406719722826437658447 35378110079584239656487671)
        ·
          refine ⟨53067165119376359484731507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35378110079584239656487671 53067165119376359484731507)
          ·
            refine ⟨79600747679064539227097261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53067165119376359484731507 79600747679064539227097261)
            ·
              refine ⟨29850280379649202210161473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79600747679064539227097261 29850280379649202210161473)
              ·
                refine ⟨22387710284736901657621105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29850280379649202210161473 22387710284736901657621105)
                ·
                  refine ⟨16790782713552676243215829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22387710284736901657621105 16790782713552676243215829)
                  ·
                    refine ⟨393533969848890849450371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16790782713552676243215829 393533969848890849450371)
                    ·
                      rfl

theorem cell23_2299214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 2, 2, 7].length) (baseStart_2299214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2299214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2299214 prefixEnd_2299214 := by exact prefixLift 2299214
  have htrace : WordTrace (prefixWord ++ tailWord_2299214) baseStart_2299214 baseEnd_2299214 := by
    simpa [prefixWord, tailWord_2299214, baseEnd_2299214] using wordTrace_append hprefix tailTrace_2299214
  have hstable : (prefixWord ++ tailWord_2299214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2299214).length < 2 ^ (prefixWord ++ tailWord_2299214).sum := by decide
  have hdescent : baseEnd_2299214 < baseStart_2299214 := by decide
  rcases family_descends (prefixWord ++ tailWord_2299214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2299224 : List Nat := [2, 1, 2, 2, 1, 1, 4, 1, 2, 2, 5]
def baseStart_2299224 : Nat := 118140960795 + 2299224 * 2 ^ 59
def prefixEnd_2299224 : Nat := 4983230072969 + 3 ^ 40 * 2299224 * 2
def baseEnd_2299224 : Nat := 1180607044353217509226067

theorem tailTrace_2299224 : CollatzResearch.WordTrace tailWord_2299224 prefixEnd_2299224 1180607044353217509226067 := by
  unfold tailWord_2299224
  simp only [CollatzResearch.WordTrace]
  refine ⟨41929794311155799520880363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55906392414874399361173817 41929794311155799520880363)
  ·
    refine ⟨62894691466733699281320545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41929794311155799520880363 62894691466733699281320545)
    ·
      refine ⟨47171018600050274460990409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62894691466733699281320545 47171018600050274460990409)
      ·
        refine ⟨35378263950037705845742807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47171018600050274460990409 35378263950037705845742807)
        ·
          refine ⟨53067395925056558768614211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35378263950037705845742807 53067395925056558768614211)
          ·
            refine ⟨79601093887584838152921317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53067395925056558768614211 79601093887584838152921317)
            ·
              refine ⟨14925205103922157153672747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 79601093887584838152921317 14925205103922157153672747)
              ·
                refine ⟨22387807655883235730509121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14925205103922157153672747 22387807655883235730509121)
                ·
                  refine ⟨16790855741912426797881841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22387807655883235730509121 16790855741912426797881841)
                  ·
                    refine ⟨12593141806434320098411381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16790855741912426797881841 12593141806434320098411381)
                    ·
                      refine ⟨1180607044353217509226067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12593141806434320098411381 1180607044353217509226067)
                      ·
                        rfl

theorem cell23_2299224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 1, 2, 2, 5].length) (baseStart_2299224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2299224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2299224 prefixEnd_2299224 := by exact prefixLift 2299224
  have htrace : WordTrace (prefixWord ++ tailWord_2299224) baseStart_2299224 baseEnd_2299224 := by
    simpa [prefixWord, tailWord_2299224, baseEnd_2299224] using wordTrace_append hprefix tailTrace_2299224
  have hstable : (prefixWord ++ tailWord_2299224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2299224).length < 2 ^ (prefixWord ++ tailWord_2299224).sum := by decide
  have hdescent : baseEnd_2299224 < baseStart_2299224 := by decide
  rcases family_descends (prefixWord ++ tailWord_2299224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2299245 : List Nat := [1, 5, 1, 1, 1, 3, 3, 2, 2, 1, 3]
def baseStart_2299245 : Nat := 118140960795 + 2299245 * 2 ^ 59
def prefixEnd_2299245 : Nat := 4983230072969 + 3 ^ 40 * 2299245 * 2
def baseEnd_2299245 : Nat := 1180617827446961927063471

theorem tailTrace_2299245 : CollatzResearch.WordTrace tailWord_2299245 prefixEnd_2299245 1180617827446961927063471 := by
  unfold tailWord_2299245
  simp only [CollatzResearch.WordTrace]
  refine ⟨83860354555235519628275189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55906903036823679752183459 83860354555235519628275189)
  ·
    refine ⟨7861908239553329965150799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 83860354555235519628275189 7861908239553329965150799)
    ·
      refine ⟨11792862359329994947726199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7861908239553329965150799 11792862359329994947726199)
      ·
        refine ⟨17689293538994992421589299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11792862359329994947726199 17689293538994992421589299)
        ·
          refine ⟨26533940308492488632383949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17689293538994992421589299 26533940308492488632383949)
          ·
            refine ⟨9950227615684683237143981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26533940308492488632383949 9950227615684683237143981)
            ·
              refine ⟨3731335355881756213928993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9950227615684683237143981 3731335355881756213928993)
              ·
                refine ⟨2798501516911317160446745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3731335355881756213928993 2798501516911317160446745)
                ·
                  refine ⟨2098876137683487870335059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2798501516911317160446745 2098876137683487870335059)
                  ·
                    refine ⟨3148314206525231805502589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2098876137683487870335059 3148314206525231805502589)
                    ·
                      refine ⟨1180617827446961927063471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3148314206525231805502589 1180617827446961927063471)
                      ·
                        rfl

theorem cell23_2299245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 3, 2, 2, 1, 3].length) (baseStart_2299245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2299245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2299245 prefixEnd_2299245 := by exact prefixLift 2299245
  have htrace : WordTrace (prefixWord ++ tailWord_2299245) baseStart_2299245 baseEnd_2299245 := by
    simpa [prefixWord, tailWord_2299245, baseEnd_2299245] using wordTrace_append hprefix tailTrace_2299245
  have hstable : (prefixWord ++ tailWord_2299245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2299245).length < 2 ^ (prefixWord ++ tailWord_2299245).sum := by decide
  have hdescent : baseEnd_2299245 < baseStart_2299245 := by decide
  rcases family_descends (prefixWord ++ tailWord_2299245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
